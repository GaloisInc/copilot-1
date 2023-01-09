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
import Copilot.Compile.Bluespec.CodeGen
import Copilot.Compile.Bluespec.External
import Copilot.Compile.Bluespec.Settings
import Copilot.Compile.Bluespec.Translate
import Copilot.Compile.Bluespec.Util

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
    (BS.mkId BS.NoPos (fromString prefix))
    (Right [])
    imports
    []
    [ifcDef, moduleDef]
    []
  where
    -- TODO RGS: Hmmmmm
    stringExpr :: String -> BS.CExpr
    stringExpr = cLit . BS.LString

    imports :: [BS.CImport]
    imports =
      [ BS.CImpId False (BS.mkId BS.NoPos "Real")
      , BS.CImpId False (BS.mkId BS.NoPos "Vector")
      ]

    moduleDef :: BS.CDefn
    moduleDef = BS.CValueSign $
      BS.CDef
        (BS.mkId BS.NoPos $ fromString $ "mk" ++ prefix)
        -- :: <prefix>Ifc -> Module Empty
        (BS.CQType
          []
          (BS.tArrow
            `BS.TAp` BS.TCon (BS.TyCon
                       { BS.tcon_name = ifcid
                       , BS.tcon_kind = Just BS.KStar
                       , BS.tcon_sort = BS.TIstruct
                                          (BS.SInterface [])
                                          (map BS.cf_name ifcfields)
                       })
            `BS.TAp` (BS.tModule `BS.TAp`
                      BS.TCon (BS.TyCon
                                { BS.tcon_name = BS.idEmpty
                                , BS.tcon_kind = Just BS.KStar
                                , BS.tcon_sort = BS.TIstruct (BS.SInterface []) []
                                }))))
        [ BS.CClause [BS.CPVar ifcmodid] [] $
          BS.Cdo False
            [ BS.CSBind (BS.CPVar ifcargid) Nothing [] (BS.CVar ifcmodid)
              -- TODO RGS: Explain why we do this
            , BS.CSletrec $ map bindifcfield ifcfields
            , BS.CSExpr Nothing $
              BS.Cmodule BS.NoPos $
               [ BS.CMStmt $ BS.CSletrec $ genfuns streams triggers
               ] ++
               [ BS.CMrules $
                 BS.Crules [] rules
               ]
            ]
        ]

    ifcargid = BS.mkId BS.NoPos "ifc"
    ifcmodid = BS.mkId BS.NoPos "ifcMod"

    rules :: [BS.CRule]
    rules = map (rule streams) triggers

    rule :: [Stream] -> Trigger -> BS.CRule
    rule streams trigger =
        BS.CRule
          []
          (Just (stringExpr ruleName))
          [ BS.CQFilter $
            BS.CVar $ BS.mkId BS.NoPos $
            fromString $ guardname name
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

    -- One register definition per extern
    -- TODO RGS: Registers should be passed in an interface.
    {-
    registers = map regDecl exts
    regDecl _ = ""
    -}

    streams  = specStreams spec
    triggers = specTriggers spec
    exts     = gatherexts streams triggers

    ifcid     = BS.mkId BS.NoPos $ fromString $ specinterfacename prefix
    ifcfields = mkspecifcfields triggers exts

    ifcDef :: BS.CDefn
    ifcDef = BS.Cstruct
               True
               (BS.SInterface [])
               (BS.IdK ifcid)
               [] -- No type variables
               ifcfields
               [] -- No derived instances

    bindifcfield :: BS.CField -> BS.CDefl
    bindifcfield (BS.CField { BS.cf_name = name }) =
      BS.CLValue name [BS.CClause [] [] (BS.CSelect (BS.CVar ifcmodid) name)] []

    -- Make generator functions, including trigger arguments.
    genfuns :: [Stream] -> [Trigger] -> [BS.CDefl]
    genfuns streams triggers =  concatMap accessdecln streams
                             ++ concatMap streamgen streams
                             ++ concatMap triggergen triggers
      where

        accessdecln :: Stream -> [BS.CDefl]
        accessdecln (Stream sid buff _ ty) = mkaccessdecln sid ty buff

        streamgen :: Stream -> [BS.CDefl]
        streamgen (Stream sid _ expr ty) = genfun (generatorname sid) expr ty

        triggergen :: Trigger -> [BS.CDefl]
        triggergen (Trigger name guard _) =
          genfun (guardname name) guard Bool
