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
genfun :: String -> Expr a -> Type a -> [BS.CDefl]
genfun name expr ty =
    -- name :: ty
    -- name = expr
    [ BS.CLValueSign (BS.CDef nameid (BS.CQType [] (transtype ty)) []) []
    , BS.CLValue nameid [BS.CClause [] [] (transExpr expr)] []
    ]
  where
    nameid = BS.mkId BS.NoPos $ fromString name

-- | Bind a buffer variable and initialise it with the stream buffer.
mkbuffdecln :: forall a. Id -> Type a -> [a] -> [BS.CStmt]
mkbuffdecln sid ty xs =
    initvals ++ [BS.CSletrec [initbufsig, initbufdef]]
  where
    -- sid_0     :: Reg <ty> <- mkReg xs_0
    -- ...
    -- sid_(n-1) :: Reg <ty> <- mkReg xs_(n-1)
    initvals = zipWith mkinitval xs [0..]
    -- sid :: Vector n (Reg <ty>)
    initbufsig = BS.CLValueSign (BS.CDef nameid (BS.CQType [] bsty) []) []
    -- sid = update (... (update newVector 0 xs_0) ...) (n-1) xs_(n-1)
    initbufdef = BS.CLValue nameid [BS.CClause [] [] (constvector ty xs)] []

    nameid   = BS.mkId BS.NoPos $ fromString $ streamname sid
    bsty     = tVector `BS.TAp` BS.cTNum numelems BS.NoPos `BS.TAp` transtype ty
    numelems = toInteger $ length xs

    mkinitval :: a -> Int -> BS.CStmt
    mkinitval x elemnum =
        BS.CSBindT
          (BS.CPVar elemid)
          Nothing
          []
          (BS.CQType [] (tReg `BS.TAp` bsty))
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
mkaccessdecln :: Id -> Type a -> [a] -> [BS.CDefl]
mkaccessdecln sid ty xs =
    -- sid_get :: Bits 64 -> ty
    -- sid_get x = (select sid ((sid_idx + x) % bufflength))._read
    [ BS.CLValueSign (BS.CDef nameid (BS.CQType [] funty) []) []
    , BS.CLValue nameid [BS.CClause [BS.CPVar argid] [] expr] []
    ]
  where
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
      mkfield name $ foldr (\(UExpr arg _) res -> BS.TAp (transtype arg) res)
                           BS.tAction args

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
      (BS.CApply
         (BS.CVar $ BS.mkId BS.NoPos $ fromString name)
         (map mktriggerarg args))
  where
    mktriggerarg (UExpr _ expr) = transExpr expr

-- | Writes the step rule, that updates all streams.
mksteprule :: [Stream] -> BS.CRule
mksteprule streams =
    BS.CRule
      []
      -- TODO RGS: We should probably make sure that there is no other rule
      -- named `step`
      (Just $ cLit $ BS.LString "step")
      [BS.CQFilter $ BS.CCon BS.idTrue []]
      (BS.Cdo False $ bufferupdates ++ indexupdates)
  where
    (bufferupdates, indexupdates) = unzip $ map mkupdateglobals streams

    -- Write code to update global stream buffers and index.
    mkupdateglobals :: Stream -> (BS.CStmt, BS.CStmt)
    mkupdateglobals (Stream sid buff expr ty) =
        (bufferupdate, indexupdate)
      where
        bufferupdate = undefined
        indexupdate = undefined

{-
-- | Writes the step function, that updates all streams.
mkstep :: CSettings -> [Stream] -> [Trigger] -> [External] -> C.FunDef
mkstep cSettings streams triggers exts =
    C.FunDef void (cSettingsStepFunctionName cSettings) [] declns stmts
  where

    void = C.TypeSpec C.Void
    stmts  =  map mkexcopy exts
           ++ triggerStmts
           ++ tmpassigns
           ++ bufferupdates
           ++ indexupdates
    declns =  streamDeclns
           ++ concat triggerDeclns
    (streamDeclns, tmpassigns, bufferupdates, indexupdates) =
      unzip4 $ map mkupdateglobals streams
    (triggerDeclns, triggerStmts) =
      unzip $ map mktriggercheck triggers

    -- Write code to update global stream buffers and index.
    mkupdateglobals :: Stream -> (C.Decln, C.Stmt, C.Stmt, C.Stmt)
    mkupdateglobals (Stream sid buff expr ty) =
      (tmpdecln, tmpassign, bufferupdate, indexupdate)
        where
          tmpdecln = C.VarDecln Nothing cty tmp_var Nothing

          tmpassign = case ty of
            Array _ -> C.Expr $ memcpy (C.Ident tmp_var) val size
              where
                size = C.LitInt (fromIntegral $ tysize ty)
                        C..* C.SizeOfType (C.TypeName (tyElemName ty))
            _       -> C.Expr $ C.Ident tmp_var C..= val

          bufferupdate = case ty of
            Array _ -> C.Expr $ memcpy dest (C.Ident tmp_var) size
              where
                dest = C.Index buff_var index_var
                size = C.LitInt (fromIntegral $ tysize ty)
                         C..* C.SizeOfType (C.TypeName (tyElemName ty))
            _       -> C.Expr $
                           C.Index buff_var index_var C..= (C.Ident tmp_var)

          indexupdate = C.Expr $ index_var C..= (incindex C..% bufflength)
            where
              bufflength = C.LitInt $ fromIntegral $ length buff
              incindex   = index_var C..+ C.LitInt 1

          tmp_var   = streamname sid ++ "_tmp"
          buff_var  = C.Ident $ streamname sid
          index_var = C.Ident $ indexname sid
          val       = C.Funcall (C.Ident $ generatorname sid) []
          cty       = transtype ty

    -- Make code that copies an external variable to its local one.
    mkexcopy :: External -> C.Stmt
    mkexcopy (External name cpyname ty) = C.Expr $ case ty of
      Array _ -> memcpy exvar locvar size
        where
          exvar  = C.Ident cpyname
          locvar = C.Ident name
          size   = C.LitInt (fromIntegral $ tysize ty)
                     C..* C.SizeOfType (C.TypeName (tyElemName ty))

      _       -> C.Ident cpyname C..= C.Ident name

    -- Make if-statement to check the guard, call the handler if necessary.
    -- This returns two things:
    --
    -- * A list of Declns for temporary variables, one for each argument that
    --   the handler function accepts. For example, if a handler function takes
    --   three arguments, the list of Declns might look something like this:
    --
    --   @
    --   int8_t   handler_arg_temp0;
    --   int16_t  handler_arg_temp1;
    --   struct s handler_arg_temp2;
    --   @
    --
    -- * A Stmt representing the if-statement. Continuing the example above,
    --   the if-statement would look something like this:
    --
    --   @
    --   if (handler_guard()) {
    --     handler_arg_temp0 = handler_arg0();
    --     handler_arg_temp1 = handler_arg1();
    --     handler_arg_temp2 = handler_arg2();
    --     handler(handler_arg_temp0, handler_arg_temp1, &handler_arg_temp2);
    --   }
    --   @
    --
    -- We create temporary variables because:
    --
    -- 1. We want to pass structs by reference intead of by value. To this end,
    --    we use C's & operator to obtain a reference to a temporary variable
    --    of a struct type and pass that to the handler function.
    --
    -- 2. Assigning a struct to a temporary variable defensively ensures that
    --    any modifications that the handler called makes to the struct argument
    --    will not affect the internals of the monitoring code.
    mktriggercheck :: Trigger -> ([C.Decln], C.Stmt)
    mktriggercheck (Trigger name guard args) =
        (aTmpDeclns, ifStmt)
      where
        aTmpDeclns = zipWith (\tmpVar arg ->
                               C.VarDecln Nothing (tempType arg) tmpVar Nothing)
                             aTempNames
                             args
          where
            tempType (UExpr { uExprType = ty }) =
              case ty of
                -- If a temporary variable is being used to store an array,
                -- declare the type of the temporary variable as a pointer, not
                -- an array. The problem with declaring it as an array is that
                -- the `arg` function will return a pointer, not an array, and
                -- C doesn't make it easy to cast directly from an array to a
                -- pointer.
                Array ty' -> C.Ptr $ transtype ty'
                _         -> transtype ty

        aTempNames = take (length args) (argTempNames name)

        ifStmt = C.If guard' firetrigger

        guard' = C.Funcall (C.Ident $ guardname name) []

        -- The body of the if-statement. This consists of statements that assign
        -- the values of the temporary variables, following by a final statement
        -- that passes the temporary variables to the handler function.
        firetrigger = map C.Expr argAssigns ++
                      [C.Expr $ C.Funcall (C.Ident name)
                                          (zipWith passArg aTempNames args)]
          where
            passArg aTempName (UExpr { uExprType = ty }) =
              case ty of
                -- Special case for Struct to pass reference to temporary
                -- struct variable to handler. (See the comments for
                -- mktriggercheck for details.)
                Struct _ -> C.UnaryOp C.Ref $ C.Ident aTempName
                _        -> C.Ident aTempName

            argAssigns = zipWith (\aTempName arg ->
                                   C.AssignOp C.Assign (C.Ident aTempName) arg)
                                 aTempNames
                                 args'
            args'        = take (length args) (map argcall (argnames name))
            argcall name = C.Funcall (C.Ident name) []

    -- Write a call to the memcpy function.
    memcpy :: C.Expr -> C.Expr -> C.Expr -> C.Expr
    memcpy dest src size = C.Funcall (C.Ident "memcpy") [dest, src, size]

    -- Translate a Copilot type to a C99 type, handling arrays especially.
    --
    -- If the given type is an array (including multi-dimensional arrays), the
    -- type is that of the elements in the array. Otherwise, it is just the
    -- equivalent representation of the given type in C.
    tyElemName :: Type a -> C.Type
    tyElemName ty = case ty of
      Array ty' -> tyElemName ty'
      _         -> transtype ty
-}

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
