{-# LANGUAGE OverloadedStrings #-}

-- | Compile Copilot specifications to Bluespec code.
module Copilot.Compile.Bluespec.Compile
  ( compile
  , compileWith
  ) where

import Data.String                    (IsString (..))
import Text.PrettyPrint.HughesPJClass (Pretty (..), render)
import System.Directory               (createDirectoryIfMissing)
import System.Exit                    (exitFailure)
import System.FilePath                ((</>))
import System.IO                      (hPutStrLn, stderr)

import qualified Language.Bluespec.Classic.AST as BS
import qualified Language.Bluespec.Classic.AST.Builtin.Ids as BS
import qualified Language.Bluespec.Classic.AST.Builtin.Types as BS

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
         ++ "You must define at least one trigger to generate Bluespec monitors."
       exitFailure

  | otherwise
  = do let bsFile = render $ pPrint $ compileBS bluespecSettings prefix spec

       let dir = bluespecSettingsOutputDirectory bluespecSettings
       createDirectoryIfMissing True dir

       writeFile (dir </> prefix ++ ".bs") bsFile

-- | Compile a specification to a Bluespec
--
-- The first argument is used as the module name and the basis for the
-- filename.
compile :: String -> Spec -> IO ()
compile = compileWith mkDefaultBluespecSettings

-- | Generate the .bs file from a 'Spec'.
compileBS :: BluespecSettings -> String -> Spec -> BS.CPackage
compileBS bluespecSettings prefix spec =
  BS.CPackage
    (i (fromString prefix))
    (Right [])
    imports
    []
    [moduleDef]
    []
  where
    -- TODO RGS: Hmmmmm
    i :: BS.FString -> BS.Id
    i = BS.mkId BS.NoPos

    -- TODO RGS: Hmmmmm
    tyCon :: BS.Id -> BS.Kind -> BS.TISort -> BS.Type
    tyCon name k s = BS.TCon $
      BS.TyCon { BS.tcon_name = name
               , BS.tcon_kind = Just k
               , BS.tcon_sort = s
               }

    -- TODO RGS: Hmmmmm
    stringExpr :: String -> BS.CExpr
    stringExpr = BS.CLit . BS.CLiteral BS.NoPos . BS.LString

    imports :: [BS.CImport]
    imports =
      [ BS.CImpId False (i "Real")
      ]

    moduleDef :: BS.CDefn
    moduleDef = BS.CValueSign $
      BS.CDef
        (i "mkCopilotMonitor")
        -- :: Module Empty
        (BS.CQType
          []
          (BS.tModule `BS.TAp` tyCon BS.idEmpty BS.KStar (BS.TIstruct (BS.SInterface []) [])))
        [ BS.CClause [] [] $
          BS.Cmodule BS.NoPos
           -- TODO RGS: Registers
           -- TODO RGS: Variables
           [ BS.CMrules $
             BS.Crules [] rules
           ]
        ]

    rules :: [BS.CRule]
    rules = map (rule streams) triggers

    rule :: [Stream] -> Trigger -> BS.CRule
    rule streams trigger =
        BS.CRule
          []
          (Just (stringExpr ruleName))
          [ BS.CQFilter $
            BS.CVar $ i $ fromString $ guardname name
          ]
          (BS.Cdo
            False
            [ BS.CSExpr Nothing $
              BS.CApply
                (BS.CVar BS.idDisplay)
                [stringExpr ("Violation: " ++ name)]
            ])
      where
        ruleName = "Monitor" ++ name
        (Trigger name guard args) = trigger

    {-
    -- One register definition per extern
    registers = map ("    " ++ ) $ map regDecl exts
    regDecl _ = ""

    variables = map ("    " ++ ) $ concatMap triggergen triggers
      where
        triggergen :: Trigger -> [String]
        triggergen (Trigger name guard args) = guarddef
          where
            guarddef = genfun (guardname name) guard Bool
    -}

    streams  = specStreams spec
    triggers = specTriggers spec
    exts     = gatherexts streams triggers
