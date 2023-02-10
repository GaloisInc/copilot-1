{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Translate Copilot Core expressions and operators to Bluespec.
module Copilot.Compile.Bluespec.Translate where

import Data.String (IsString (..))

import Copilot.Core
import Copilot.Compile.Bluespec.Error (impossible)
import Copilot.Compile.Bluespec.Util

import qualified Language.Bluespec.Classic.AST as BS
import qualified Language.Bluespec.Classic.AST.Builtin.Ids as BS
import qualified Language.Bluespec.Classic.AST.Builtin.Types as BS

-- | Translates a Copilot Core expression into a Bluespec expression.
transExpr :: Expr a -> BS.CExpr
transExpr (Const ty x) = constty ty x

transExpr (Local ty1 _ name e1 e2) =
  let nameid = BS.mkId BS.NoPos $ fromString name
      e1'    = transExpr e1
      ty1'   = transType ty1
      e2'    = transExpr e2 in
  BS.Cletrec
    [ BS.CLValueSign
        (BS.CDef nameid (BS.CQType [] ty1') [BS.CClause [] [] e1'])
        []
    ]
    e2'

transExpr (Var _ n) = BS.CVar $ BS.mkId BS.NoPos $ fromString n

transExpr (Drop _ amount sid) =
  let accessvar = streamaccessorname sid
      index     = BS.LInt $ BS.ilDec $ fromIntegral amount in
  BS.CApply (BS.CVar $ BS.mkId BS.NoPos $ fromString accessvar)
            [BS.CLit $ BS.CLiteral BS.NoPos index]

transExpr (ExternVar _ name _) =
  let ifcargid = BS.mkId BS.NoPos $ fromString ifcargname in
  BS.CSelect
    (BS.CSelect
      (BS.CVar ifcargid)
      (BS.mkId BS.NoPos $ fromString name))
    (BS.id_read BS.NoPos)

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
    BwNot   _ty -> app $ BS.idInvertAt BS.NoPos
    Sqrt    _ty -> BS.CSelect
                     (BS.CApply
                       (BS.CVar (BS.mkId BS.NoPos "sqrtFP"))
                       [e, defaultRoundMode])
                     BS.idPrimFst
    Ceiling _ty -> app $ BS.mkId BS.NoPos "ceil"
    Floor   _ty -> app $ BS.mkId BS.NoPos "floor"

    Cast fromTy toTy -> transCast fromTy toTy e
    GetField (Struct _)  _ f -> BS.CSelect e $ BS.mkId BS.NoPos $
                                fromString $ accessorname f
    GetField _ _ _ -> impossible "transOp1" "copilot-bluespec"
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
    Index    _   -> cIndexVector e1 e2
  where
    app i = BS.CApply (BS.CVar i) [e1, e2]

-- | Translates a Copilot ternary operator and its arguments into a Bluespec
-- function.
transOp3 :: Op3 a b c d -> BS.CExpr -> BS.CExpr -> BS.CExpr -> BS.CExpr
transOp3 op e1 e2 e3 =
  case op of
    Mux _ -> BS.Cif BS.NoPos e1 e2 e3

-- | Bluespec does not have a general-purpose casting operation, so we must
-- handle casts on a case-by-case basis.
transCast :: Type a -> Type b -> BS.CExpr -> BS.CExpr
transCast fromTy toTy =
  case (fromTy, toTy) of
    -----
    -- "safe" casts that cannot lose information
    -----

    (Bool,  Bool)    -> id
    (Bool,  Word8)   -> upcastBool
    (Bool,  Word16)  -> upcastBool
    (Bool,  Word32)  -> upcastBool
    (Bool,  Word64)  -> upcastBool
    (Bool,  Int8)    -> upcastBool
    (Bool,  Int16)   -> upcastBool
    (Bool,  Int32)   -> upcastBool
    (Bool,  Int64)   -> upcastBool

    (Int8,  Int8)    -> id
    (Int8,  Int16)   -> upcast
    (Int8,  Int32)   -> upcast
    (Int8,  Int64)   -> upcast
    (Int16, Int16)   -> id
    (Int16, Int32)   -> upcast
    (Int16, Int64)   -> upcast
    (Int32, Int32)   -> id
    (Int32, Int64)   -> upcast
    (Int64, Int64)   -> id

    (Word8,  Int16)  -> unpackPackUpcast Word16
    (Word8,  Int32)  -> unpackPackUpcast Word32
    (Word8,  Int64)  -> unpackPackUpcast Word64
    (Word8,  Word8)  -> id
    (Word8,  Word16) -> upcast
    (Word8,  Word32) -> upcast
    (Word8,  Word64) -> upcast
    (Word16, Int32)  -> unpackPackUpcast Word32
    (Word16, Int64)  -> unpackPackUpcast Word64
    (Word16, Word16) -> id
    (Word16, Word32) -> upcast
    (Word16, Word64) -> upcast
    (Word32, Int64)  -> unpackPackUpcast Word64
    (Word32, Word32) -> id
    (Word32, Word64) -> upcast
    (Word64, Word64) -> id

    -----
    -- "unsafe" casts, which may lose information
    -----

    -- unsigned truncations
    (Word64, Word32) -> downcast
    (Word64, Word16) -> downcast
    (Word64, Word8)  -> downcast
    (Word32, Word16) -> downcast
    (Word32, Word8)  -> downcast
    (Word16, Word8)  -> downcast

    -- signed truncations
    (Int64, Int32)   -> downcast
    (Int64, Int16)   -> downcast
    (Int64, Int8)    -> downcast
    (Int32, Int16)   -> downcast
    (Int32, Int8)    -> downcast
    (Int16, Int8)    -> downcast

    -- signed integer to float
    (Int64, Float)   -> castIntegralToFloatingPoint
    (Int32, Float)   -> castIntegralToFloatingPoint
    (Int16, Float)   -> castIntegralToFloatingPoint
    (Int8,  Float)   -> castIntegralToFloatingPoint

    -- unsigned integer to float
    (Word64, Float)  -> castIntegralToFloatingPoint
    (Word32, Float)  -> castIntegralToFloatingPoint
    (Word16, Float)  -> castIntegralToFloatingPoint
    (Word8,  Float)  -> castIntegralToFloatingPoint

    -- signed integer to double
    (Int64, Double)  -> castIntegralToFloatingPoint
    (Int32, Double)  -> castIntegralToFloatingPoint
    (Int16, Double)  -> castIntegralToFloatingPoint
    (Int8,  Double)  -> castIntegralToFloatingPoint

    -- unsigned integer to double
    (Word64, Double) -> castIntegralToFloatingPoint
    (Word32, Double) -> castIntegralToFloatingPoint
    (Word16, Double) -> castIntegralToFloatingPoint
    (Word8,  Double) -> castIntegralToFloatingPoint

    -- unsigned to signed conversion
    (Word64, Int64)  -> unpackPack
    (Word32, Int32)  -> unpackPack
    (Word16, Int16)  -> unpackPack
    (Word8,  Int8)   -> unpackPack

    -- signed to unsigned conversion
    (Int64, Word64)  -> unpackPack
    (Int32, Word32)  -> unpackPack
    (Int16, Word16)  -> unpackPack
    (Int8,  Word8)   -> unpackPack

    _ -> impossible "transCast" "copilot-bluespec"
  where
    -- unpackPack :: (Bits fromTy n, Bits toTy n) => fromTy -> toTy
    -- unpackPack e = (unpack (pack e)) :: toTy
    --
    -- The most basic cast. Used when fromTy and toTy are both integral types
    -- with the same number of bits.
    unpackPack :: BS.CExpr -> BS.CExpr
    unpackPack e = withTypeAnnotation $
                   BS.CApply
                     (BS.CVar BS.idUnpack)
                     [BS.CApply (BS.CVar BS.idPack) [e]]

    -- upcastBool :: (Add k 1 n, Bits toTy n) => Bool -> toTy
    -- upcastBool b = (unpack (extend (pack b))) :: toTy
    --
    -- Cast a Bool to a `Bits 1` value, extend it to `Bits n`, and then
    -- convert it back to an integral type.
    upcastBool :: BS.CExpr -> BS.CExpr
    upcastBool e = withTypeAnnotation $
                   BS.CApply
                     (BS.CVar BS.idUnpack)
                     [BS.CApply extendExpr [BS.CApply (BS.CVar BS.idPack) [e]]]

    -- upcast :: (BitExtend m n x) => x m -> x n
    -- upcast e = (extend e) :: ty
    --
    -- Convert a narrower integral type to a wider integral type (e.g.,
    -- `UInt 8` to `UInt 64` or `Int 8` to `Int 64`). Note that the `extend`
    -- operation is smart enough to choose between sign-extension and
    -- zero-extension depending on whether `x m` (i.e., fromTy) is a signed
    -- or unsigned type, respectively.
    upcast :: BS.CExpr -> BS.CExpr
    upcast e = withTypeAnnotation $ BS.CApply extendExpr [e]

    -- downcast :: (BitExtend m n x) => x n -> x m
    -- downcast e = (truncate e) :: ty
    --
    -- Convert a wider integral type to a narrow integral type (e.g.,
    -- `UInt 64` to `UInt 8` or `Int 64` to `Int 8`) by truncating the most
    -- significant bits.
    downcast :: BS.CExpr -> BS.CExpr
    downcast e = withTypeAnnotation $ BS.CApply truncateExpr [e]

    -- Apply upcast followed by unpackPack. This requires supplying the type to
    -- upcast to for type disambiguation purposes.
    unpackPackUpcast :: Type a -> BS.CExpr -> BS.CExpr
    unpackPackUpcast upcastTy e = unpackPack $
      BS.CApply extendExpr [e] `BS.CHasType` BS.CQType [] (transType upcastTy)

    -- castIntegralToFloatingPoint :: (FixedFloatCVT fromTy toTy) => fromTy toTy
    -- castIntegralToFloatingPoint e =
    --   ((vFixedToFloat e (0 :: UInt 64) Rnd_Nearest_Even).fst) :: tfl
    --
    -- While FloatingPoint does have a Bits instance, we don't want to convert
    -- an integral type to a FloatingPoint type using the Bits class, as the
    -- bit representation of an integral value differs quite a bit from the bit
    -- representation of a FloatingPoint value. Instead, we use the
    -- special-purpose FixedFloatCVT class for this task.
    castIntegralToFloatingPoint :: BS.CExpr -> BS.CExpr
    castIntegralToFloatingPoint e =
      withTypeAnnotation $
      BS.CSelect
        (BS.CApply
          (BS.CVar (BS.mkId BS.NoPos "vFixedToFloat"))
          [ e
          , constNumTy Word64 0
          , defaultRoundMode
          ])
        BS.idPrimFst

    -- It is sometimes possible to have ambiguous types unless we give explicit
    -- type signatures to various expressions.
    withTypeAnnotation :: BS.CExpr -> BS.CExpr
    withTypeAnnotation e = e `BS.CHasType` BS.CQType [] (transType toTy)

    extendExpr   = BS.CVar $ BS.mkId BS.NoPos "extend"
    truncateExpr = BS.CVar $ BS.mkId BS.NoPos "truncate"

-- | Transform a Copilot Core literal, based on its value and type, into a
-- Bluespec expression.
constty :: Type a -> a -> BS.CExpr
constty ty =
  case ty of
    -- The treatment of scalar types is relatively straightforward. Note that
    -- Bool is an enum, so we must construct it using a CCon rather than with
    -- a CLit.
    Bool      -> \v -> BS.CCon (if v then BS.idTrue else BS.idFalse) []
    Int8      -> constInt ty . toInteger
    Int16     -> constInt ty . toInteger
    Int32     -> constInt ty . toInteger
    Int64     -> constInt ty . toInteger
    Word8     -> constInt ty . toInteger
    Word16    -> constInt ty . toInteger
    Word32    -> constInt ty . toInteger
    Word64    -> constInt ty . toInteger
    Float     -> constFP ty . realToFrac
    Double    -> constFP ty

    -- Translating a Copilot array literal to a Bluespec Vector is somewhat
    -- involved. Given a Copilot array {x_0, ..., x_(n-1)}, the
    -- corresponding Bluespec Vector will look something like:
    --
    --   let arr = update (... (update newVector 0 x_0)) (n-1) x_(n-1)
    --
    -- We use the `update` function instead of the := syntax (e.g.,
    -- { array_temp[0] := x; array_temp[1] := y; ...}) so that we can construct
    -- a Vector in a pure context.
    Array ty' -> constVector ty' . arrayelems

    -- Converting a Copilot struct { field_0 = x_0, ..., field_(n-1) = x_(n-1) }
    -- to a Bluespec struct is quite straightforward, given Bluespec's struct
    -- initialization syntax.
    Struct s -> \v ->
      BS.CStruct
        (Just True)
        (BS.mkId BS.NoPos $ fromString $ structname $ typename s)
        (map (\(Value ty'' field@(Field val)) ->
               ( BS.mkId BS.NoPos $ fromString $ fieldname field
               , constty ty'' val
               ))
             (toValues v))

constVector :: Type a -> [a] -> BS.CExpr
constVector ty = genVector (\_ -> constty ty)

genVector :: (Int -> a -> BS.CExpr) -> [a] -> BS.CExpr
genVector f vec =
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
transType :: Type a -> BS.CType
transType ty = case ty of
  Bool   -> BS.tBool
  Int8   -> BS.tInt  `BS.TAp` BS.cTNum  8 BS.NoPos
  Int16  -> BS.tInt  `BS.TAp` BS.cTNum 16 BS.NoPos
  Int32  -> BS.tInt  `BS.TAp` BS.cTNum 32 BS.NoPos
  Int64  -> BS.tInt  `BS.TAp` BS.cTNum 64 BS.NoPos
  Word8  -> BS.tUInt `BS.TAp` BS.cTNum  8 BS.NoPos
  Word16 -> BS.tUInt `BS.TAp` BS.cTNum 16 BS.NoPos
  Word32 -> BS.tUInt `BS.TAp` BS.cTNum 32 BS.NoPos
  Word64 -> BS.tUInt `BS.TAp` BS.cTNum 64 BS.NoPos

  Float -> BS.TCon $
    BS.TyCon
      { BS.tcon_name = BS.mkId BS.NoPos "Float"
      , BS.tcon_kind = Just BS.KStar
      , BS.tcon_sort = BS.TItype 0 $ tFloatingPoint `BS.TAp`
                                     BS.cTNum  8 BS.NoPos `BS.TAp`
                                     BS.cTNum 23 BS.NoPos
      }
  Double -> BS.TCon $
    BS.TyCon
      { BS.tcon_name = BS.mkId BS.NoPos "Double"
      , BS.tcon_kind = Just BS.KStar
      , BS.tcon_sort = BS.TItype 0 $ tFloatingPoint `BS.TAp`
                                     BS.cTNum 11 BS.NoPos `BS.TAp`
                                     BS.cTNum 52 BS.NoPos
      }
  Array ty' -> tVector `BS.TAp` BS.cTNum len BS.NoPos `BS.TAp` transType ty'
    where
      len = toInteger $ tylength ty
  Struct s -> BS.TCon $
    BS.TyCon
      { BS.tcon_name = BS.mkId BS.NoPos $ fromString $ structname $ typename s
      , BS.tcon_kind = Just BS.KStar
      , BS.tcon_sort =
          BS.TIstruct BS.SStruct $
          map (\(Value _tu field) ->
                BS.mkId BS.NoPos $
                fromString $
                fieldname field)
              (toValues s)
      }

-- Translate a literal number of type @ty@ into a Bluespec expression.
--
-- PRE: The type of PRE is numeric (integer or floating-point), that
-- is, not boolean, struct or array.
constNumTy :: Type a -> Integer -> BS.CExpr
constNumTy ty =
  case ty of
    Float  -> constFP ty . fromInteger
    Double -> constFP ty . fromInteger
    _      -> constInt ty

-- Translate a Copilot integer literal into a Bluespec expression.
constInt :: Type a -> Integer -> BS.CExpr
constInt ty i
    -- Bluespec intentionally does not support negative literal syntax (e.g.,
    -- -42), so we must create negative integer literals using the `negate`
    -- function.
    | i >= 0    = withTypeAnnotation $ cLit $ BS.LInt $ BS.ilDec i
    | otherwise = withTypeAnnotation $
                  BS.CApply
                    (BS.CVar $ BS.idNegateAt BS.NoPos)
                    [cLit $ BS.LInt $ BS.ilDec $ negate i]
  where
    -- It is sometimes possible to have ambiguous types unless we give explicit
    -- type signatures to various expressions.
    withTypeAnnotation :: BS.CExpr -> BS.CExpr
    withTypeAnnotation e = e `BS.CHasType` BS.CQType [] (transType ty)

-- Translate a Copilot floating-point literal into a Bluespec expression.
constFP :: Type ty -> Double -> BS.CExpr
constFP ty d
    -- Bluespec intentionally does not support negative literal syntax (e.g.,
    -- -42.5), so we must create negative floating-point literals using the
    -- `negate` function.
    | d >= 0    = withTypeAnnotation $ cLit $ BS.LReal d
    | otherwise = withTypeAnnotation $
                  BS.CApply
                    (BS.CVar $ BS.idNegateAt BS.NoPos)
                    [cLit $ BS.LReal $ negate d]
  where
    -- It is sometimes possible to have ambiguous types unless we give explicit
    -- type signatures to various expressions.
    withTypeAnnotation :: BS.CExpr -> BS.CExpr
    withTypeAnnotation e = e `BS.CHasType` BS.CQType [] (transType ty)

cLit :: BS.Literal -> BS.CExpr
cLit = BS.CLit . BS.CLiteral BS.NoPos

cIndexVector :: BS.CExpr -> BS.CExpr -> BS.CExpr
cIndexVector vec idx =
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

tFloatingPoint :: BS.CType
tFloatingPoint = BS.TCon $
  BS.TyCon
    { BS.tcon_name = BS.mkId BS.NoPos "FloatingPoint"
    , BS.tcon_kind = Just (BS.Kfun BS.KNum (BS.Kfun BS.KNum BS.KStar))
    , BS.tcon_sort =
        BS.TIstruct BS.SStruct [ BS.mkId BS.NoPos "sign"
                               , BS.mkId BS.NoPos "exp"
                               , BS.mkId BS.NoPos "sfd"
                               ]
    }

-- TODO RGS: Ask Ivan about the best way to handle this
unsupportedFPOp :: String -> a
unsupportedFPOp op =
  error $ "Bluespec's FloatingPoint type does not support the " ++ op ++
          " operation."

defaultRoundMode :: BS.CExpr
defaultRoundMode = BS.CCon (BS.mkId BS.NoPos "Rnd_Nearest_Even") []
