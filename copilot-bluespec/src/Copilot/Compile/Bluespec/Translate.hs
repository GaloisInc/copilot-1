{-# LANGUAGE GADTs #-}

-- | Translate Copilot Core expressions and operators to Bluespec.
module Copilot.Compile.Bluespec.Translate
    (transExpr)
  where

import Control.Monad.State

import Copilot.Core
import Copilot.Compile.Bluespec.Error (impossible)
import Copilot.Compile.Bluespec.Util (streamaccessorname, excpyname)

-- | Translates a Copilot Core expression into a Bluespec expression.
transExpr :: Expr a -> String
transExpr (Const ty x) = showWithType' ty x
transExpr (Op1 op e) = transOp1 op ++ "(" ++ transExpr e ++ ")"
transExpr (Op2 op e1 e2) = transOp2 op ++ " "
                                       ++ "(" ++ transExpr e1 ++ ")"
                                       ++ " "
                                       ++ "(" ++ transExpr e2 ++ ")"
transExpr (Op3 op e1 e2 e3) = transOp3 op ++ " "
                                          ++ "(" ++ transExpr e1 ++ ")"
                                          ++ " "
                                          ++ "(" ++ transExpr e2 ++ ")"
                                          ++ " "
                                          ++ "(" ++ transExpr e3 ++ ")"

-- Cases not handled
--
-- transexpr (Drop _ amount sid) = do
--   let accessvar = streamaccessorname sid
--       index     = C.LitInt (fromIntegral amount)
--   return $ funcall accessvar [index]
--
-- transexpr (ExternVar _ name _) = return $ C.Ident (excpyname name)
--
-- Cases not handled -- but we don't really care much about them.
--
-- transexpr (Label _ _ e) = transexpr e -- ignore label
--
-- transexpr (Local ty1 _ name e1 e2) = do
--   e1' <- transexpr e1
--   let cty1 = transtype ty1
--       init = Just $ C.InitExpr e1'
--
--   -- Add variable to function environment
--   modify (`mappend` [C.VarDecln Nothing cty1 name init])
--
--   transexpr e2
--
-- transexpr (Var _ n) = return $ C.Ident n

-- | Translates a Copilot unary operator into a Bluespec function.
transOp1 :: Op1 a b -> String
transOp1 op =
  case op of
    Not         -> "not"
    Abs     _ty -> "abs"
    Sign    _ty -> "sign"
    Recip   _ty -> "inv"
    Acos    _ty -> "acos"
    Asin    _ty -> "asin"
    Atan    _ty -> "atan"
    Cos     _ty -> "cos"
    Sin     _ty -> "sin"
    Tan     _ty -> "tan"
    Acosh   _ty -> "acosh"
    Asinh   _ty -> "asinh"
    Atanh   _ty -> "atanh"
    Cosh    _ty -> "cosh"
    Sinh    _ty -> "sinh"
    Tanh    _ty -> "tanh"
    Exp     _ty -> "exp"
    Log     _ty -> "log"
    Sqrt    _ty -> "sqrt"
    Ceiling _ty -> "ceil"
    Floor   _ty -> "floor"
    BwNot   _ty -> "(~)"

    -- Cases not handled
    --   Cast     _ ty -> C.Cast (transtypename ty) e
    --   GetField (Struct _)  _ f -> C.Dot e (accessorname f)

-- | Translates a Copilot binary operator into a Bluespec function.
transOp2 :: Op2 a b c -> String
transOp2 op =
  case op of
    And          -> "(&&)"
    Or           -> "(||)"
    Add      _ty -> "(+)"
    Sub      _ty -> "(-)"
    Mul      _ty -> "(*)"
    Mod      _ty -> "(%)"
    Div      _ty -> "(/)"
    Fdiv     _ty -> "(/)"
    Pow      _ty -> "(^)"
    Logb     _ty -> "\\e1 e2 -> log e1 / log e2"
    Atan2    _ty -> "atan2"
    Eq       _   -> "(==)"
    Ne       _   -> "(/=)"
    Le       _   -> "(<=)"
    Ge       _   -> "(>=)"
    Lt       _   -> "(<)"
    Gt       _   -> "(>)"
    BwAnd    _   -> "(&)"
    BwOr     _   -> "(|)"
    BwXor    _   -> "(^)"
    BwShiftL _ _ -> "(<<)"
    BwShiftR _ _ -> "(>>)"

-- Cases not handled
--   Index    _   -> C.Index e1 e2

-- | Translates a Copilot ternary operator into a Bluespec function.
transOp3 :: Op3 a b c d -> String
transOp3 op =
  case op of
    Mux _ -> "(\\x y z -> if x then y else z)"

-- * Auxiliary showing function for constant values

-- | Show a value. The representation depends on the type and the target
-- language. Booleans are represented differently depending on the backend.
showWithType' :: Type a -> a -> String
showWithType' t x = sw
  where
    sw = case showWit t of
           ShowWit -> show x

-- | Show Copilot Core type.
showType :: Type a -> String
showType t =
  case t of
    Bool   -> "Bool"
    Int8   -> "Int8"
    Int16  -> "Int16"
    Int32  -> "Int32"
    Int64  -> "Int64"
    Word8  -> "Word8"
    Word16 -> "Word16"
    Word32 -> "Word32"
    Word64 -> "Word64"
    Float  -> "Float"
    Double -> "Double"
    Array t -> "Array " ++ showType t
    Struct t -> "Struct"

-- * Auxiliary show instance

-- | Witness datatype for showing a value, used by 'showWithType'.
data ShowWit a = Show a => ShowWit

-- | Turn a type into a show witness.
showWit :: Type a -> ShowWit a
showWit t =
  case t of
    Bool   -> ShowWit
    Int8   -> ShowWit
    Int16  -> ShowWit
    Int32  -> ShowWit
    Int64  -> ShowWit
    Word8  -> ShowWit
    Word16 -> ShowWit
    Word32 -> ShowWit
    Word64 -> ShowWit
    Float  -> ShowWit
    Double -> ShowWit
    Array t -> ShowWit
    Struct t -> ShowWit

