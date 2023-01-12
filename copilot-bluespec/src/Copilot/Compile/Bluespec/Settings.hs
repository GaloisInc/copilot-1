-- | Settings used by the code generator to customize the code.
module Copilot.Compile.Bluespec.Settings where

-- | Settings used to customize the code generated.
-- TODO RGS: Do we want other settings? For example, the ability to customize
-- the name of the function defined in the generated .bs file?
newtype BluespecSettings = BluespecSettings
  { bluespecSettingsOutputDirectory  :: FilePath
  }

-- | Default Bluespec settings. Output to the current directory.
mkDefaultBluespecSettings :: BluespecSettings
mkDefaultBluespecSettings = BluespecSettings "."
