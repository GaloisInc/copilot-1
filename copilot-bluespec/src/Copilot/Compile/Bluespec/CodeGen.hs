-- | High-level translation of Copilot Core into Bluespec.
module Copilot.Compile.Bluespec.CodeGen where

import Control.Monad.State  (runState)
import Data.List            (union, unzip4)
import Data.Typeable        (Typeable)

import Copilot.Core
import Copilot.Core.Extra

-- Internal imports
import Copilot.Compile.Bluespec.Translate

-- | Write a generator function for a stream.
genfun :: Show a => String -> Expr a -> Type a -> [String]
genfun name expr ty = [ "let " ++ name ++ " = " ++ transExpr expr ]
