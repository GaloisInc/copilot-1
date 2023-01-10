{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Translate Copilot Core expressions and operators to Bluespec.
module Copilot.Compile.Bluespec.Translate where

import Control.Monad.State
import Data.String (IsString (..))

import qualified Language.Bluespec.Classic.AST as BS
import qualified Language.Bluespec.Classic.AST.Builtin.Ids as BS
import qualified Language.Bluespec.Classic.AST.Builtin.Types as BS

import Copilot.Core
import Copilot.Compile.Bluespec.Error (impossible)
import Copilot.Compile.Bluespec.Util

-- | Translates a Copilot Core expression into a Bluespec expression.
transExpr :: Expr a -> BS.CExpr
transExpr (Const ty x) = constty ty x

transExpr (Local ty1 _ name e1 e2) =
  let e1'  = transExpr e1
      cty1 = transtype ty1
      e2'  = transExpr e2 in
  BS.Cletrec
    [ BS.CLValue
        (BS.mkId BS.NoPos $ fromString name)
        [ BS.CClause [] [] e1'
        ]
        []
    ]
    e2'

transExpr (Var _ n) = BS.CVar $ BS.mkId BS.NoPos $ fromString n

transExpr (Drop _ amount sid) =
  let accessvar = streamaccessorname sid
      index     = BS.LInt $ BS.ilDec $ fromIntegral amount in
  BS.CApply (BS.CVar $ BS.mkId BS.NoPos $ fromString accessvar)
            [BS.CLit $ BS.CLiteral BS.NoPos index]

transExpr (ExternVar _ name _) = BS.CVar $ BS.mkId BS.NoPos $ fromString name

transExpr (Label _ _ e) = transExpr e -- ignore label

transExpr (Op1 op e) = transOp1 op (transExpr e)

transExpr (Op2 op e1 e2) = transOp2 op (transExpr e1) (transExpr e2)

transExpr (Op3 op e1 e2 e3) =
  transOp3 op (transExpr e1) (transExpr e2) (transExpr e3)

-- | Translates a Copilot unary operator and its argument into a Bluespec
-- function.
transOp1 :: Op1 a b -> BS.CExpr -> BS.CExpr
transOp1 op e =
  case op of
    Not         -> app BS.idNot
    Abs     _ty -> app $ BS.mkId BS.NoPos "abs"
    Sign    _ty -> app $ BS.mkId BS.NoPos "signum"

    -- Bluespec's Arith class does not have a `recip` method corresponding to
    -- Haskell's `recip` in the `Fractional` class, so we implement it
    -- ourselves.
    Recip    ty -> BS.CApply
                     (BS.CVar (BS.idSlashAt BS.NoPos))
                     [constNumTy ty 1, e]
    Acos    _ty -> app $ BS.mkId BS.NoPos "acos"
    Asin    _ty -> app $ BS.mkId BS.NoPos "asin"
    Atan    _ty -> app $ BS.mkId BS.NoPos "atan"
    Cos     _ty -> app $ BS.mkId BS.NoPos "cos"
    Sin     _ty -> app $ BS.mkId BS.NoPos "sin"
    Tan     _ty -> app $ BS.mkId BS.NoPos "tan"
    Acosh   _ty -> app $ BS.mkId BS.NoPos "acosh"
    Asinh   _ty -> app $ BS.mkId BS.NoPos "asinh"
    Atanh   _ty -> app $ BS.mkId BS.NoPos "atanh"
    Cosh    _ty -> app $ BS.mkId BS.NoPos "cosh"
    Sinh    _ty -> app $ BS.mkId BS.NoPos "sinh"
    Tanh    _ty -> app $ BS.mkId BS.NoPos "tanh"
    Exp     _ty -> app $ BS.mkId BS.NoPos "exp_e"
    Log     _ty -> app $ BS.mkId BS.NoPos "log"
    Sqrt    _ty -> app $ BS.mkId BS.NoPos "sqrt"

    -- Bluespec's `ceil` and `floor` functions return an `Integer` instead
    -- of a `Real`, so we must explicitly cast the result to an `Integer` using
    -- `fromInteger`.
    Ceiling _ty -> BS.CApply
                     (BS.CVar (BS.idFromInteger BS.NoPos))
                     [BS.CApply
                       (BS.CVar (BS.mkId BS.NoPos "ceil"))
                       [e]]
    Floor   _ty -> BS.CApply
                     (BS.CVar (BS.idFromInteger BS.NoPos))
                     [BS.CApply
                       (BS.CVar (BS.mkId BS.NoPos "floor"))
                       [e]]

    BwNot   _ty -> app $ BS.idInvertAt BS.NoPos
    Cast   _ ty -> transCast ty e
    GetField (Struct _)  _ f -> BS.CSelect e $ BS.mkId BS.NoPos $
                                fromString $ accessorname f
  where
    app i = BS.CApply (BS.CVar i) [e]

-- | Translates a Copilot binary operator and its arguments into a Bluespec
-- function.
transOp2 :: Op2 a b c -> BS.CExpr -> BS.CExpr -> BS.CExpr
transOp2 op e1 e2 =
  case op of
    And          -> app BS.idAnd
    Or           -> app $ BS.idOrAt BS.NoPos
    Add      _ty -> app BS.idPlus
    Sub      _ty -> app BS.idMinus
    Mul      _ty -> app $ BS.idStarAt BS.NoPos
    Mod      _ty -> app $ BS.idPercentAt BS.NoPos
    Div      _ty -> app $ BS.idSlashAt BS.NoPos
    Fdiv     _ty -> app $ BS.idSlashAt BS.NoPos
    Pow      _ty -> app $ BS.idStarStarAt BS.NoPos
    Logb     _ty -> app $ BS.mkId BS.NoPos "logb"
    Atan2    _ty -> app $ BS.mkId BS.NoPos "atan2"
    Eq       _   -> app BS.idEqual
    Ne       _   -> app BS.idNotEqual
    Le       _   -> app $ BS.idLtEqAt BS.NoPos
    Ge       _   -> app $ BS.idGtEqAt BS.NoPos
    Lt       _   -> app $ BS.idLtAt BS.NoPos
    Gt       _   -> app $ BS.idGtAt BS.NoPos
    BwAnd    _   -> app $ BS.idBitAndAt BS.NoPos
    BwOr     _   -> app $ BS.idBitOrAt BS.NoPos
    BwXor    _   -> app $ BS.idCaretAt BS.NoPos
    BwShiftL _ _ -> app $ BS.idLshAt BS.NoPos
    BwShiftR _ _ -> app $ BS.idRshAt BS.NoPos
    Index    _   -> cSelect e1 e2
  where
    app i = BS.CApply (BS.CVar i) [e1, e2]

-- | Translates a Copilot ternary operator and its arguments into a Bluespec
-- function.
transOp3 :: Op3 a b c d -> BS.CExpr -> BS.CExpr -> BS.CExpr -> BS.CExpr
transOp3 op e1 e2 e3 =
  case op of
    Mux _ -> BS.Cif BS.NoPos e1 e2 e3

-- | TODO RGS: Finish me
transCast :: Type a -> BS.CExpr -> BS.CExpr
transCast = error "TODO RGS: transCast"

-- | Transform a Copilot Core literal, based on its value and type, into a
-- Bluespec literal.
constty :: Type a -> a -> BS.CExpr
constty ty =
  case ty of
    -- The treatment of scalar types is relatively straightforward. Note that
    -- Bool is an enum, so we must construct it using a CCon rather than with
    -- a CLit.
    Bool      -> \v -> BS.CCon (if v then BS.idTrue else BS.idFalse) []
    Int8      -> cLit . BS.LInt . BS.ilDec . toInteger
    Int16     -> cLit . BS.LInt . BS.ilDec . toInteger
    Int32     -> cLit . BS.LInt . BS.ilDec . toInteger
    Int64     -> cLit . BS.LInt . BS.ilDec . toInteger
    Word8     -> cLit . BS.LInt . BS.ilDec . toInteger
    Word16    -> cLit . BS.LInt . BS.ilDec . toInteger
    Word32    -> cLit . BS.LInt . BS.ilDec . toInteger
    Word64    -> cLit . BS.LInt . BS.ilDec . toInteger
    Float     -> cLit . BS.LReal . realToFrac
    Double    -> cLit . BS.LReal

    -- Translating a Copilot array literal to a Bluespec Vector is somewhat
    -- involved. Given a Copilot array {x_0, ..., x_(n-1)}, the
    -- corresponding Bluespec Vector will look something like:
    --
    --   let arr = update (... (update newVector 0 x_0)) (n-1) x_(n-1)
    --
    -- We use the `update` function instead of the := syntax (e.g.,
    -- { array_temp[0] := x; array_temp[1] := y; ...}) so that we can construct
    -- a Vector in a pure context.
    Array ty' -> constvector ty' . arrayelems

    -- Converting a Copilot struct { field_0 = x_0, ..., field_(n-1) = x_(n-1) }
    -- to a Bluespec struct is quite straightforward, given Bluespec's struct
    -- initialization syntax.
    Struct s -> \v ->
      BS.CStruct
        (Just True)
        (BS.mkId BS.NoPos $ fromString $ typename s)
        (map (\(Value ty'' field@(Field val)) ->
               ( BS.mkId BS.NoPos $ fromString $ fieldname field
               , constty ty'' val
               ))
             (toValues v))

constvector :: Type a -> [a] -> BS.CExpr
constvector ty = genvector (\_ -> constty ty)

genvector :: (Int -> a -> BS.CExpr) -> [a] -> BS.CExpr
genvector f vec =
  snd $
  foldr
    (\x (!i, !v) ->
      ( i+1
      , BS.CApply
          (BS.CVar (BS.mkId BS.NoPos "update"))
          [ v
          , cLit (BS.LInt (BS.ilDec (toInteger i)))
          , f i x
          ]
      ))
    (0, BS.CVar (BS.mkId BS.NoPos "newVector"))
    vec

-- | Translate a Copilot type to a Bluespec type.
transtype :: Type a -> BS.CType
transtype ty = case ty of
  Bool      -> BS.tBool
  Int8      -> BS.tInt  `BS.TAp` BS.cTNum  8 BS.NoPos
  Int16     -> BS.tInt  `BS.TAp` BS.cTNum 16 BS.NoPos
  Int32     -> BS.tInt  `BS.TAp` BS.cTNum 32 BS.NoPos
  Int64     -> BS.tInt  `BS.TAp` BS.cTNum 64 BS.NoPos
  Word8     -> BS.tUInt `BS.TAp` BS.cTNum  8 BS.NoPos
  Word16    -> BS.tUInt `BS.TAp` BS.cTNum 16 BS.NoPos
  Word32    -> BS.tUInt `BS.TAp` BS.cTNum 32 BS.NoPos
  Word64    -> BS.tUInt `BS.TAp` BS.cTNum 64 BS.NoPos
  Float     -> tODOFloats
  Double    -> BS.tReal
  Array ty' -> tVector `BS.TAp` BS.cTNum length BS.NoPos `BS.TAp` transtype ty'
    where
      length = fromIntegral $ tylength ty
  Struct s  -> BS.TCon $
    BS.TyCon
      { BS.tcon_name = BS.mkId BS.NoPos $ fromString $ typename s
      , BS.tcon_kind = Just BS.KStar
      , BS.tcon_sort =
          BS.TIstruct BS.SStruct $
          map (\(Value _tu field) ->
                BS.mkId BS.NoPos $
                fromString $
                fieldname field)
              (toValues s)
      }

-- Translate a literal number of type @ty@ into a Bluespec literal.
--
-- PRE: The type of PRE is numeric (integer or floating-point), that
-- is, not boolean, struct or array.
constNumTy :: Type a -> Integer -> BS.CExpr
constNumTy ty =
  case ty of
    Float  -> cLit . BS.LReal . fromInteger
    Double -> cLit . BS.LReal . fromInteger
    _      -> cLit . BS.LInt . BS.ilDec

-- TODO RGS: The definitions below probably deserve another home

cLit :: BS.Literal -> BS.CExpr
cLit = BS.CLit . BS.CLiteral BS.NoPos

cSelect :: BS.CExpr -> BS.CExpr -> BS.CExpr
cSelect vec idx =
  BS.CApply (BS.CVar (BS.mkId BS.NoPos "select")) [vec, idx]

tVector :: BS.CType
tVector = BS.TCon $
  BS.TyCon
    { BS.tcon_name = BS.idVector
    , BS.tcon_kind = Just (BS.Kfun BS.KNum (BS.Kfun BS.KStar BS.KStar))
    , BS.tcon_sort =
        BS.TIdata
          { BS.tidata_cons = [BS.mkId BS.NoPos "V"]
          , BS.tidata_enum = False
          }
    }

tODOFloats :: a
tODOFloats = error "TODO RGS: Floats"
