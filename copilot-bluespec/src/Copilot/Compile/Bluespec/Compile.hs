-- | Compile Copilot specifications to Bluespec code.
module Copilot.Compile.Bluespec.Compile
  ( compile
  , compileWith
  ) where

import System.Directory     (createDirectoryIfMissing)
import System.Exit          (exitFailure)
import System.FilePath      ((</>))
import System.IO            (hPutStrLn, stderr)

import Copilot.Core
import Copilot.Core.Extra

import Copilot.Compile.Bluespec.Util (guardname)
import Copilot.Compile.Bluespec.External
import Copilot.Compile.Bluespec.Settings
import Copilot.Compile.Bluespec.CodeGen

-- | Compile a specification to a Bluespec file.
--
-- The first argument is the settings for the bluespec code generated.
--
-- The second argument is used as module name and prefix file generated.
compileWith :: BluespecSettings -> String -> Spec -> IO ()
compileWith bluespecSettings prefix spec
  | null (specTriggers spec)
  = do hPutStrLn stderr $
         "Copilot error: attempt at compiling empty specification.\n"
         ++ "You must define at least one trigger to generate C monitors."
       exitFailure

  | otherwise
  = do let cfile = compilec bluespecSettings prefix spec

       let dir = bluespecSettingsOutputDirectory bluespecSettings
       createDirectoryIfMissing True dir

       writeFile (dir </> prefix ++ ".bs") $ cfile

-- | Compile a specification to a Bluespec
--
-- The first argument is used as the module name and the basis for the
-- filename.
compile :: String -> Spec -> IO ()
compile = compileWith mkDefaultBluespecSettings

-- | Generate the .bs file from a 'Spec'.
compilec :: BluespecSettings -> String -> Spec -> String
compilec bluespecSettings prefix spec = unlines
    [ packageDecl
    , ""
    , imports
    , ""
    , moduleDef
    ]
  where

    packageDecl = "package " ++ prefix ++ " where"

    imports = "import Real"

    moduleDef = unlines $
      [ "-- Module definition"
      , ""
      , "mkCopilotMonitor :: Module Empty"
      , "mkCopilotMonitor ="
      , "  module"
      ]
      ++
      registers
      ++
      variables
      ++
      rules

    -- One register definition per extern
    registers = map ("    " ++ ) $ map regDecl exts
    regDecl _ = ""

    variables = map ("    " ++ ) $ concatMap triggergen triggers
      where
        triggergen :: Trigger -> [String]
        triggergen (Trigger name guard args) = guarddef
          where
            guarddef = genfun (guardname name) guard Bool

    rules :: [String]
    rules = map ("    " ++ ) $ "rules" : map ("  " ++ ) ruleContents

    ruleContents = concatMap (rule streams) triggers

    rule :: [Stream] -> Trigger -> [String]
    rule streams trigger = [ ruleHeader, ruleBody ]
      where
        ruleHeader = concat
                       [ "\"", ruleName, "\""
                       , " : when (", guardname name, ") ==> do"
                       ]

        ruleBody   = unlines $
                       map ("  " ++ )
                         [ concat ["$display ", "\"Violation: ", name, "\""]
                         ]
        ruleName   = "Monitor" ++ name
        (Trigger name guard args) = trigger

    streams  = specStreams spec
    triggers = specTriggers spec
    exts     = gatherexts streams triggers
