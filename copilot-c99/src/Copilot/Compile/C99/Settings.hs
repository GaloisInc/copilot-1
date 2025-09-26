{-# LANGUAGE CPP #-}
-- | Settings used by the code generator to customize the code.
module Copilot.Compile.C99.Settings
    ( CSettings(..)
    , mkDefaultCSettings
    , OutputDirectory
    , outputDirectoryToPath
    )
  where

import System.FilePath ( takeDirectory )

-- | Enumerator to show where the generated code should be placed
data OutputDirectory = WithSpec 
                      | CurrentDir
                      | Custom String
                      deriving (Show, Eq)

outputDirectoryToPath :: OutputDirectory -> IO FilePath
outputDirectoryToPath (Custom dir) = return dir
outputDirectoryToPath CurrentDir = return "."
outputDirectoryToPath WithSpec = return (takeDirectory __FILE__)


-- | Settings used to customize the code generated.
data CSettings = CSettings
  { cSettingsStepFunctionName :: String
  , cSettingsOutputDirectory  :: FilePath
  }

-- | Default settings with a step function called @step@.
mkDefaultCSettings :: CSettings
mkDefaultCSettings = CSettings "step" "."
