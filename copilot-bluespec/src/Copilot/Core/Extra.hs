{-# LANGUAGE GADTs      #-}
{-# LANGUAGE Rank2Types #-}
-- | Auxiliary functions that manipulate structures in Copilot.Core.
module Copilot.Core.Extra where

import Copilot.Core
import Data.List     (union)
import Data.Typeable (Typeable)

--- | List all types of an expression, returns items uniquely.
exprtypes :: Typeable a => Expr a -> [UType]
exprtypes = concat . flattenExpr exprType
  where
    -- | List all types of an expression, returns items uniquely.
    exprType :: Typeable a => Expr a -> [UType]
    exprType e = case e of
      Const ty _            -> typetypes ty
      Local ty1 ty2 _ e1 e2 -> typetypes ty1 `union` typetypes ty2
      Var ty _              -> typetypes ty
      Drop ty _ _           -> typetypes ty
      ExternVar ty _ _      -> typetypes ty
      Label ty _ _          -> typetypes ty
      _                     -> []

    -- | List all types of a type, returns items uniquely.
    typetypes :: Typeable a => Type a -> [UType]
    typetypes ty = case ty of
      Array ty' -> typetypes ty' `union` [UType ty]
      Struct x  -> concatMap (\(Value ty' _) -> typetypes ty') (toValues x) `union` [UType ty]
      _         -> [UType ty]

-- | Collect all expression of a list of streams and triggers and wrap them
-- into an UEXpr.
gatherexprs :: [Stream] -> [Trigger] -> [UExpr]
gatherexprs streams triggers =  map streamexpr streams
                             ++ concatMap triggerexpr triggers
  where
    streamexpr  (Stream _ _ expr ty)   = UExpr ty expr
    triggerexpr (Trigger _ guard args) = UExpr Bool guard : args

-- Traverse a stream and apply a function to all expressions inside, gathering
-- the result.
flattenStreams :: (forall c . Typeable c => Expr c -> b)
               -> Stream
               -> [b]
flattenStreams f (Stream _ _ expr _) = flattenExpr f expr

-- Traverse a trigger and apply a function to all expressions inside, gathering
-- the result.
flattenTriggers :: (forall c . Typeable c => Expr c -> b)
                -> Trigger
                -> [b]
flattenTriggers f (Trigger _ guard args) =
    concat [ guardexts, argexts ]
  where
    guardexts = flattenExpr f guard
    argexts   = concatMap (flattenUExpr f) args

-- Traverse a uexpr and apply a function to all expressions inside, gathering
-- the result.
flattenUExpr :: (forall c . Typeable c => Expr c -> b)
             -> UExpr
             -> [b]
flattenUExpr f (UExpr _ expr) = flattenExpr f expr

-- Traverse an expr and apply a function to all expressions inside, gathering
-- the result.
flattenExpr :: Typeable a
            => (forall c . Typeable c => Expr c -> b)
            -> Expr a
            -> [b]
flattenExpr = go
  where
    go :: Typeable a
       => (forall c . Typeable c => Expr c -> b)
       -> Expr a
       -> [b]
    go f e@(Local _ _ _ e1 e2)   = f e : concat [ go f e1, go f e2 ]
    go f e@(ExternVar ty name _) = [ f e ]
    go f e@(Op1 _ e1)            = f e : go f e1
    go f e@(Op2 _ e1 e2)         = f e : concat [ go f e1, go f e2 ]
    go f e@(Op3 _ e1 e2 e3)      = f e : concat [ go f e1, go f e2, go f e3 ]
    go f e@(Label _ _ e1)        = f e : go f e1
    go f e                       = [ f e ]
