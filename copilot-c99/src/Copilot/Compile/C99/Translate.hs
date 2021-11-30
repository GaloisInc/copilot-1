{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}

-- | Translate Copilot Core expressions and operators to C99.
module Copilot.Compile.C99.Translate
  {-# DEPRECATED "This module will be hidden in future versions." #-}
  where

import Control.Monad.State

import Copilot.Core
import Copilot.Compile.C99.Util

import qualified Language.C99.Simple as C

-- | Translates a Copilot Core expression into a C99 expression.
transexpr :: Expr a -> State FunEnv C.Expr
transexpr (Const ty x) = return $ constty ty x

transexpr (Local ty1 _ name e1 e2) = do
  e1' <- transexpr e1
  let cty1 = transtype ty1
      init = Just $ C.InitExpr e1'
  statetell [C.VarDecln Nothing cty1 name init]

  transexpr e2

transexpr (Var _ n) = return $ C.Ident n

transexpr (Drop _ amount sid) = do
  let accessvar = streamaccessorname sid
      index     = C.LitInt (fromIntegral amount)
  return $ funcall accessvar [index]

transexpr (ExternVar _ name _) = return $ C.Ident (excpyname name)

transexpr (Label _ _ e) = transexpr e -- ignore label

transexpr (Op1 op e) = do
  e' <- transexpr e
  return $ transop1 op e'

transexpr (Op2 op e1 e2) = do
  e1' <- transexpr e1
  e2' <- transexpr e2
  return $ transop2 op e1' e2'

transexpr (Op3 op e1 e2 e3) = do
  e1' <- transexpr e1
  e2' <- transexpr e2
  e3' <- transexpr e3
  return $ transop3 op e1' e2' e3'


-- | Translates a Copilot unary operator and its argument into a C99
-- expression.
transop1 :: Op1 a b -> C.Expr -> C.Expr
transop1 op e = case op of
  Not             -> (C..!) e

  Abs      Float  -> funcall "fabsf"    [e]
  Abs      Double -> funcall "fabs"     [e]
  Abs      _      -> funcall "abs"      [e]

  -- Implement `signum x` as `x > 0 ? 1 : (x < 0 ? -1 : x)`. This matches how
  -- GHC implements signum and ensures that it returns result when x is
  -- ±0 or NaN.
  Sign     ty     -> C.Cond (C.BinaryOp C.GT e (mkLit 0)) (mkLit 1) $
                     C.Cond (C.BinaryOp C.LT e (mkLit 0)) (mkLit (-1)) e
    where
      mkLit :: (forall a. Num a => a) -> C.Expr
      mkLit lit =
        case ty of
          -- Ensure that we use LitFloat or LitDouble as appropriate to avoid
          -- unwanted casts in the generated code.
          Float  -> C.LitFloat lit
          Double -> C.LitDouble lit
          _      -> C.LitInt lit

  Recip    Double -> C.LitDouble 1.0 C../ e
  Recip    Float  -> C.LitFloat 1.0 C../ e
  Recip    _      -> fpOnly "Recip"

  Exp      Double -> funcall "exp"    [e]
  Exp      Float  -> funcall "expf"   [e]
  Exp      _      -> fpOnly "Exp"

  Sqrt     Double -> funcall "sqrt"   [e]
  Sqrt     Float  -> funcall "sqrtf"  [e]
  Sqrt     _      -> fpOnly "Sqrt"

  Log      Double -> funcall "log"    [e]
  Log      Float  -> funcall "logf"   [e]
  Log      _      -> fpOnly "Log"

  Sin      Double -> funcall "sin"    [e]
  Sin      Float  -> funcall "sinf"   [e]
  Sin      _      -> fpOnly "Sin"

  Tan      Double -> funcall "tan"    [e]
  Tan      Float  -> funcall "tanf"   [e]
  Tan      _      -> fpOnly "Tan"

  Cos      Double -> funcall "cos"    [e]
  Cos      Float  -> funcall "cosf"   [e]
  Cos      _      -> fpOnly "Cos"

  Asin     Double -> funcall "asin"   [e]
  Asin     Float  -> funcall "asinf"  [e]
  Asin     _      -> fpOnly "Asin"

  Atan     Double -> funcall "atan"   [e]
  Atan     Float  -> funcall "atanf"  [e]
  Atan     _      -> fpOnly "Atan"

  Acos     Double -> funcall "acos"   [e]
  Acos     Float  -> funcall "acosf"  [e]
  Acos     _      -> fpOnly "Acos"

  Sinh     Double -> funcall "sinh"   [e]
  Sinh     Float  -> funcall "sinhf"  [e]
  Sinh     _      -> fpOnly "Sinh"

  Tanh     Double -> funcall "tanh"   [e]
  Tanh     Float  -> funcall "tanhf"  [e]
  Tanh     _      -> fpOnly "Tanh"

  Cosh     Double -> funcall "cosh"   [e]
  Cosh     Float  -> funcall "coshf"  [e]
  Cosh     _      -> fpOnly "Cosh"

  Asinh    Double -> funcall "asinh"  [e]
  Asinh    Float  -> funcall "asinhf" [e]
  Asinh    _      -> fpOnly "Asinh"

  Atanh    Double -> funcall "atanh"  [e]
  Atanh    Float  -> funcall "atanhf" [e]
  Atanh    _      -> fpOnly "Atanh"

  Acosh    Double -> funcall "acosh"  [e]
  Acosh    Float  -> funcall "acoshf" [e]
  Acosh    _      -> fpOnly "Acosh"

  Ceiling  Double -> funcall "ceil"   [e]
  Ceiling  Float  -> funcall "ceilf"  [e]
  Ceiling  _      -> fpOnly "Ceiling"

  Floor    Double -> funcall "floor"  [e]
  Floor    Float  -> funcall "floorf" [e]
  Floor    _      -> fpOnly "Floor"

  BwNot    _      -> (C..~) e

  Cast     _ ty  -> C.Cast (transtypename ty) e

  GetField (Struct _)  _ f -> C.Dot e (accessorname f)
  GetField _           _ _ -> error "GetStruct used on non-struct value"

-- | Translates a Copilot binary operator and its arguments into a C99
-- expression.
transop2 :: Op2 a b c -> C.Expr -> C.Expr -> C.Expr
transop2 op e1 e2 = case op of
  And          -> e1 C..&& e2
  Or           -> e1 C..|| e2
  Add      _   -> e1 C..+  e2
  Sub      _   -> e1 C..-  e2
  Mul      _   -> e1 C..*  e2
  Mod      _   -> e1 C..%  e2
  Div      _   -> e1 C../  e2
  Fdiv     _   -> e1 C../  e2

  Pow      Double -> funcall "pow"  [e1, e2]
  Pow      Float  -> funcall "powf" [e1, e2]
  Pow      _      -> fpOnly "Pow"

  Logb     Double -> funcall "log"  [e2] C../ funcall "log"  [e1]
  Logb     Float  -> funcall "logf" [e2] C../ funcall "logf" [e1]
  Logb     _      -> fpOnly "Logb"

  Atan2    Double -> funcall "atan2"  [e1, e2]
  Atan2    Float  -> funcall "atan2f" [e1, e2]
  Atan2    _      -> fpOnly "Atan2"

  Eq       _   -> e1 C..== e2
  Ne       _   -> e1 C..!= e2
  Le       _   -> e1 C..<= e2
  Ge       _   -> e1 C..>= e2
  Lt       _   -> e1 C..<  e2
  Gt       _   -> e1 C..>  e2
  BwAnd    _   -> e1 C..&  e2
  BwOr     _   -> e1 C..|  e2
  BwXor    _   -> e1 C..^  e2
  BwShiftL _ _ -> e1 C..<< e2
  BwShiftR _ _ -> e1 C..>> e2
  Index    _   -> C.Index e1 e2

-- | Translates a Copilot ternary operator and its arguments into a C99
-- expression.
transop3 :: Op3 a b c d -> C.Expr -> C.Expr -> C.Expr -> C.Expr
transop3 op e1 e2 e3 = case op of
  Mux _ -> C.Cond e1 e2 e3

fpOnly :: String -> a
fpOnly name = error $ name ++ " only supported for floating-point values"

-- | Transform a Copilot Core literal, based on its value and type, into a C99
-- literal.
constty :: Type a -> a -> C.Expr
constty ty = case ty of
  Bool   -> C.LitBool
  Int8   -> explicitty ty . C.LitInt . fromIntegral
  Int16  -> explicitty ty . C.LitInt . fromIntegral
  Int32  -> explicitty ty . C.LitInt . fromIntegral
  Int64  -> explicitty ty . C.LitInt . fromIntegral
  Word8  -> explicitty ty . C.LitInt . fromIntegral
  Word16 -> explicitty ty . C.LitInt . fromIntegral
  Word32 -> explicitty ty . C.LitInt . fromIntegral
  Word64 -> explicitty ty . C.LitInt . fromIntegral
  Float  -> explicitty ty . C.LitFloat
  Double -> explicitty ty . C.LitDouble
  Struct _ -> \v -> C.InitVal (transtypename ty) (map fieldinit (toValues v))
    where
      fieldinit (Value ty (Field val)) = C.InitExpr $ constty ty val
  Array ty' -> \v -> C.InitVal (transtypename ty) (vals v)
    where
      vals v = constarray ty' (arrayelems v)

      constarray :: Type a -> [a] -> [C.Init]
      constarray ty xs = case ty of
        Array ty' -> constarray ty' (concatMap arrayelems xs)
        _         -> map (C.InitExpr . constty ty) xs


-- | Explicitly cast a C99 value to a type.
explicitty :: Type a -> C.Expr -> C.Expr
explicitty ty = C.Cast (transtypename ty)

-- | Translate a Copilot type to a C99 type.
transtype :: Type a -> C.Type
transtype ty = case ty of
  Bool      -> C.TypeSpec $ C.TypedefName "bool"
  Int8      -> C.TypeSpec $ C.TypedefName "int8_t"
  Int16     -> C.TypeSpec $ C.TypedefName "int16_t"
  Int32     -> C.TypeSpec $ C.TypedefName "int32_t"
  Int64     -> C.TypeSpec $ C.TypedefName "int64_t"
  Word8     -> C.TypeSpec $ C.TypedefName "uint8_t"
  Word16    -> C.TypeSpec $ C.TypedefName "uint16_t"
  Word32    -> C.TypeSpec $ C.TypedefName "uint32_t"
  Word64    -> C.TypeSpec $ C.TypedefName "uint64_t"
  Float     -> C.TypeSpec C.Float
  Double    -> C.TypeSpec C.Double
  Array ty' -> C.Array (transtype ty') length where
    length = Just $ C.LitInt $ fromIntegral $ tylength ty
  Struct s  -> C.TypeSpec $ C.Struct (typename s)

-- | Translate a Copilot type intro a C typename
transtypename :: Type a -> C.TypeName
transtypename ty = C.TypeName $ transtype ty
