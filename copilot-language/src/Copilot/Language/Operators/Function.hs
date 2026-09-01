{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Copilot.Language.Operators.Function
  ( callFunction
  , callFunction0
  , callFunction1
  , callFunction2
  , callFunction3
  , Callable (..)
  ) where

import Copilot.Core (FunctionArgs (..), OneArg, Typed, TypedArgs)
import Copilot.Language.Stream (FunctionHandle, Stream (..))

callFunction :: Callable args res => FunctionHandle args res -> FunctionType args res
callFunction fnHdl = curryFunction (CallFunction fnHdl)

callFunction0 :: Typed res => FunctionHandle () res -> () -> Stream res
callFunction0 = callFunction

callFunction1 :: (Typed arg1, Typed res)
              => FunctionHandle (OneArg arg1) res -> Stream arg1 -> Stream res
callFunction1 = callFunction

callFunction2 :: (Typed arg1, Typed arg2, Typed res)
              => FunctionHandle (arg1, arg2) res -> Stream arg1 -> Stream arg2 -> Stream res
callFunction2 = callFunction

callFunction3 :: (Typed arg1, Typed arg2, Typed arg3, Typed res)
              => FunctionHandle (arg1, arg2, arg3) res -> Stream arg1 -> Stream arg2 -> Stream arg3 -> Stream res
callFunction3 = callFunction

class (TypedArgs args, Typed res) => Callable args res where
  type FunctionType args res
  curryFunction :: (FunctionArgs Stream args -> Stream res) -> FunctionType args res
  uncurryFunction :: FunctionType args res -> FunctionArgs Stream args -> Stream res

instance Typed res => Callable () res where
  type FunctionType () res = () -> Stream res
  curryFunction f () = f FunctionArgs0
  uncurryFunction f FunctionArgs0 = f ()

instance (Typed arg1, Typed res) => Callable (OneArg arg1) res where
  type FunctionType (OneArg arg1) res = Stream arg1 -> Stream res
  curryFunction f arg1 = f (FunctionArgs1 arg1)
  uncurryFunction f (FunctionArgs1 arg1) = f arg1

instance (Typed arg1, Typed arg2, Typed res) => Callable (arg1, arg2) res where
  type FunctionType (arg1, arg2) res = Stream arg1 -> Stream arg2 -> Stream res
  curryFunction f arg1 arg2 = f (FunctionArgs2 arg1 arg2)
  uncurryFunction f (FunctionArgs2 arg1 arg2) = f arg1 arg2

instance (Typed arg1, Typed arg2, Typed arg3, Typed res) => Callable (arg1, arg2, arg3) res where
  type FunctionType (arg1, arg2, arg3) res = Stream arg1 -> Stream arg2 -> Stream arg3 -> Stream res
  curryFunction f arg1 arg2 arg3 = f (FunctionArgs3 arg1 arg2 arg3)
  uncurryFunction f (FunctionArgs3 arg1 arg2 arg3) = f arg1 arg2 arg3
