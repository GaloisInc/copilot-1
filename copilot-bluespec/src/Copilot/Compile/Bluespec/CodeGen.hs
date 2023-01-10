{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | High-level translation of Copilot Core into Bluespec.
module Copilot.Compile.Bluespec.CodeGen where

import Control.Monad.State  (runState)
import Data.List            (union, unzip4)
import Data.String          (IsString (..))
import Data.Typeable        (Typeable)

import qualified Language.Bluespec.Classic.AST as BS
import qualified Language.Bluespec.Classic.AST.Builtin.Ids as BS
import qualified Language.Bluespec.Classic.AST.Builtin.Types as BS

import Copilot.Core
import Copilot.Core.Extra

-- Internal imports
import Copilot.Compile.Bluespec.External
import Copilot.Compile.Bluespec.Translate
import Copilot.Compile.Bluespec.Util

-- | Write a generator function for a stream.
genfun :: String -> Expr a -> Type a -> BS.CDefl
genfun name expr ty =
    -- name :: ty
    -- name = expr
    BS.CLValueSign
      (BS.CDef nameid (BS.CQType [] (transtype ty)) [def])
      []
  where
    nameid = BS.mkId BS.NoPos $ fromString name
    def = BS.CClause [] [] (transExpr expr)

-- | Bind a buffer variable and initialise it with the stream buffer.
mkbuffdecln :: forall a. Id -> Type a -> [a] -> [BS.CStmt]
mkbuffdecln sid ty xs =
    initvals ++ [BS.CSletrec [initbufsig]]
  where
    -- sid_0     :: Reg <ty> <- mkReg xs_0
    -- ...
    -- sid_(n-1) :: Reg <ty> <- mkReg xs_(n-1)
    initvals = zipWith mkinitval xs [0..]
    -- sid :: Vector n (Reg <ty>)
    -- sid = update (... (update newVector 0 xs_0) ...) (n-1) xs_(n-1)
    initbufsig = BS.CLValueSign
                   (BS.CDef nameid (BS.CQType [] vecty) [initbufdef])
                   []
    initbufdef = BS.CClause
                   []
                   []
                   (genvector
                     (\idx _ -> BS.CVar $ BS.mkId BS.NoPos $
                                fromString $ streamelemname sid idx)
                     xs)

    nameid   = BS.mkId BS.NoPos $ fromString $ streamname sid
    bsty     = tReg `BS.TAp` transtype ty
    vecty    = tVector `BS.TAp` BS.cTNum numelems BS.NoPos `BS.TAp` bsty
    numelems = toInteger $ length xs

    mkinitval :: a -> Int -> BS.CStmt
    mkinitval x elemnum =
        BS.CSBindT
          (BS.CPVar elemid)
          Nothing
          []
          (BS.CQType [] bsty)
          (BS.CApply (BS.CVar (BS.mkId BS.NoPos "mkReg")) [constty ty x])
      where
        elemname = streamelemname sid elemnum
        elemid   = BS.mkId BS.NoPos $ fromString elemname

-- | Make an index variable and initialise it to 0.
mkindexdecln :: Id -> BS.CStmt
mkindexdecln sid =
  -- sid_idx :: Reg (Bit 64) <- mkReg 0
  BS.CSBindT
    (BS.CPVar nameid)
    Nothing
    []
    (BS.CQType [] bsty)
    (BS.CApply (BS.CVar (BS.mkId BS.NoPos "mkReg"))
               [cLit $ BS.LInt $ BS.ilDec 0])
  where
    nameid = BS.mkId BS.NoPos $ fromString $ indexname sid
    bsty   = tReg `BS.TAp` BS.tBitN 64 BS.NoPos

-- | Define an accessor function for the ring buffer associated with a stream
mkaccessdecln :: Id -> Type a -> [a] -> BS.CDefl
mkaccessdecln sid ty xs =
    -- sid_get :: Bits 64 -> ty
    -- sid_get x = (select sid ((sid_idx + x) % bufflength))._read
    BS.CLValueSign (BS.CDef nameid (BS.CQType [] funty) [def]) []
  where
    def        = BS.CClause [BS.CPVar argid] [] expr
    argty      = BS.tBit `BS.TAp` BS.cTNum 64 BS.NoPos
    retty      = transtype ty
    funty      = BS.tArrow `BS.TAp` argty `BS.TAp` retty
    name       = streamaccessorname sid
    nameid     = BS.mkId BS.NoPos $ fromString name
    bufflength = cLit $ BS.LInt $ BS.ilDec $ toInteger $ length xs
    argid      = BS.mkId BS.NoPos "x"
    index      = BS.CApply (BS.CVar (BS.idPercentAt BS.NoPos))
                   [ BS.CApply (BS.CVar BS.idPlus)
                       [ BS.CVar (BS.mkId BS.NoPos (fromString (indexname sid)))
                       , BS.CVar argid
                       ]
                   , bufflength
                   ]
    indexexpr  = cSelect (BS.CVar (BS.mkId BS.NoPos (fromString (streamname sid)))) index
    expr       = BS.CSelect indexexpr (BS.id_read BS.NoPos)

-- | Define fields for a module interface containing a specification's trigger
-- functions and external variables.
mkspecifcfields :: [Trigger] -> [External] -> [BS.CField]
mkspecifcfields triggers exts =
    map mktriggerfield triggers ++ map mkextfield exts
  where
    -- trigger :: args_1 -> ... -> args_n -> Action
    mktriggerfield :: Trigger -> BS.CField
    mktriggerfield (Trigger name _ args) =
      mkfield name $
      foldr
        (\(UExpr arg _) res -> BS.tArrow `BS.TAp` transtype arg `BS.TAp` res)
        BS.tAction
        args

    -- ext :: Reg ty
    mkextfield :: External -> BS.CField
    mkextfield (External name ty) =
      mkfield name $ tReg `BS.TAp` transtype ty

-- | Define a rule for a trigger function.
mktriggerrule :: Trigger -> BS.CRule
mktriggerrule (Trigger name guard args) =
    BS.CRule
      []
      (Just $ cLit $ BS.LString name)
      [ BS.CQFilter $
        BS.CVar $ BS.mkId BS.NoPos $
        fromString $ guardname name
      ]
      (BS.CApply nameexpr args')
  where
    ifcargid = BS.mkId BS.NoPos $ fromString ifcargname
    nameid   = BS.mkId BS.NoPos $ fromString name
    nameexpr = BS.CSelect (BS.CVar ifcargid) nameid

    args'   = take (length args) (map argcall (argnames name))
    argcall = BS.CVar . BS.mkId BS.NoPos . fromString

-- | Writes the step rule, that updates all streams.
mksteprule :: [Stream] -> BS.CRule
mksteprule streams =
    BS.CRule
      []
      Nothing
      [BS.CQFilter $ BS.CCon BS.idTrue []]
      -- NB: Use Caction instead of Cdo here. Caction permits an empty list of
      -- statements, whereas Cdo does not.
      (BS.Caction BS.NoPos $ bufferupdates ++ indexupdates)
  where
    (bufferupdates, indexupdates) = unzip $ map mkupdateglobals streams

    -- Write code to update global stream buffers and index.
    mkupdateglobals :: Stream -> (BS.CStmt, BS.CStmt)
    mkupdateglobals (Stream sid buff expr ty) =
        (bufferupdate, indexupdate)
      where
        bufferupdate =
          BS.CSExpr Nothing $
          BS.Cwrite
            BS.NoPos
            (cSelect (BS.CVar buffid) (BS.CVar indexid))
            (BS.CVar genid)

        indexupdate =
          BS.CSExpr Nothing $
          BS.Cwrite
            BS.NoPos
            (BS.CVar indexid)
            (BS.CApply (BS.CVar (BS.idPercentAt BS.NoPos))
                       [incindex, bufflength])

        bufflength = cLit $ BS.LInt $ BS.ilDec $ toInteger $ length buff
        incindex   = BS.CApply (BS.CVar BS.idPlus)
                       [ BS.CVar indexid
                       , cLit $ BS.LInt $ BS.ilDec 1
                       ]

        buffid  = BS.mkId BS.NoPos $ fromString $ streamname sid
        genid   = BS.mkId BS.NoPos $ fromString $ generatorname sid
        indexid = BS.mkId BS.NoPos $ fromString $ indexname sid

-- | Write a struct declaration based on its definition.
mkstructdecln :: Struct a => Type a -> BS.CDefn
mkstructdecln (Struct x) =
    BS.Cstruct
      True
      BS.SStruct
      (BS.IdK structid)
      [] -- No type variables
      structfields
      -- Derive a Bits instance so that we can put this struct in a Reg
      [BS.CTypeclass BS.idBits]
  where
    structid = BS.mkId BS.NoPos $ fromString $ structname $ typename x
    structfields = map mkstructfield $ toValues x

    mkstructfield :: Value a -> BS.CField
    mkstructfield (Value ty field) = mkfield (fieldname field) (transtype ty)

-- TODO RGS: The definitions below probably deserve another home

mkfield :: String -> BS.CType -> BS.CField
mkfield name ty =
  BS.CField
    { BS.cf_name = BS.mkId BS.NoPos $ fromString name
    , BS.cf_pragmas = Nothing
    , BS.cf_type = BS.CQType [] ty
    , BS.cf_default = []
    , BS.cf_orig_type = Nothing
    }

tReg :: BS.CType
tReg = BS.TCon $
  BS.TyCon
    { BS.tcon_name = BS.idReg
    , BS.tcon_kind = Just (BS.Kfun BS.KStar BS.KStar)
    , BS.tcon_sort = BS.TIstruct (BS.SInterface [])
                                 [BS.id_write BS.NoPos, BS.id_read BS.NoPos]
    }
