-- | Settings used by the code generator to customize the code.
module Copilot.Compile.Bluespec.Settings where

-- | Settings used to customize the code generated.
data BluespecSettings = BluespecSettings
  { bluespecSettingsStepFunctionName :: String
  , bluespecSettingsOutputDirectory  :: FilePath
  }

-- | Default settings with a step function called @step@.
mkDefaultBluespecSettings :: BluespecSettings
mkDefaultBluespecSettings = BluespecSettings "step" "."
