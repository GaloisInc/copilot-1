-- | Compile Copilot specifications to Bluespec code.
module Copilot.Compile.Bluespec
  ( compile
  , compileWith
  , BluespecSettings(..)
  , mkDefaultBluespecSettings
  ) where

import Copilot.Compile.Bluespec.Compile
import Copilot.Compile.Bluespec.Settings
