module Copilot.Language.Operators.Function
  ( callFunction
  ) where

import Copilot.Core (Typed)
import Copilot.Language.Stream (FunctionHandle, Stream (..))

callFunction :: (Typed arg, Typed res)
             => FunctionHandle arg res -> Stream arg -> Stream res
callFunction = CallFunction
