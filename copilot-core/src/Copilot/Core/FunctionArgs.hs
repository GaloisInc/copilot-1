{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}
module Copilot.Core.FunctionArgs
  ( FunctionArgs (..)
  , functionArgsToList
  , OneArg
  ) where

import Data.Typeable (Typeable)

data FunctionArgs f args where
  FunctionArgs0 :: FunctionArgs f ()
  FunctionArgs1 :: Typeable arg1
                => f arg1 -> FunctionArgs f (OneArg arg1)
  FunctionArgs2 :: (Typeable arg1, Typeable arg2)
                => f arg1 -> f arg2 -> FunctionArgs f (arg1, arg2)
  FunctionArgs3 :: (Typeable arg1, Typeable arg2, Typeable arg3)
                => f arg1 -> f arg2 -> f arg3 -> FunctionArgs f (arg1, arg2, arg3)
  -- and so on

functionArgsToList :: (forall arg. Typeable arg => f arg -> b) -> FunctionArgs f args -> [b]
functionArgsToList f args =
  case args of
    FunctionArgs0 -> []
    FunctionArgs1 arg1 -> [f arg1]
    FunctionArgs2 arg1 arg2 -> [f arg1, f arg2]
    FunctionArgs3 arg1 arg2 arg3 -> [f arg1, f arg2, f arg3]

data OneArg arg
