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
    imports :: [BS.CImport]
    imports =
      [ BS.CImpId False (BS.mkId BS.NoPos "Real")
      , BS.CImpId False (BS.mkId BS.NoPos "Vector")
      ]

    moduleDef :: BS.CDefn
    moduleDef = BS.CValueSign $
      BS.CDef
        (BS.mkId BS.NoPos $ fromString $ "mk" ++ prefix)
        -- :: Module <prefix>Ifc -> Module Empty
        (BS.CQType
          []
          (BS.tArrow
            `BS.TAp` (BS.tModule `BS.TAp`
                      BS.TCon (BS.TyCon
                                { BS.tcon_name = ifcid
                                , BS.tcon_kind = Just BS.KStar
                                , BS.tcon_sort = BS.TIstruct
                                                   (BS.SInterface [])
                                                   (map BS.cf_name ifcfields)
                                }))
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
               map BS.CMStmt (mkglobals streams) ++
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
    rules = map mktriggerrule triggers ++ [mksteprule streams]

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
      BS.CLValue name [BS.CClause [] [] (BS.CSelect (BS.CVar ifcargid) name)] []

    -- Make buffer and index declarations for streams.
    mkglobals :: [Stream] -> [BS.CStmt]
    mkglobals streams = concatMap buffdecln streams ++ map indexdecln streams
      where
        buffdecln  (Stream sid buff _ ty) = mkbuffdecln  sid ty buff
        indexdecln (Stream sid _    _ _ ) = mkindexdecln sid

    -- Make generator functions, including trigger arguments.
    genfuns :: [Stream] -> [Trigger] -> [BS.CDefl]
    genfuns streams triggers =  map accessdecln streams
                             ++ map streamgen streams
                             ++ map triggergen triggers
      where

        accessdecln :: Stream -> BS.CDefl
        accessdecln (Stream sid buff _ ty) = mkaccessdecln sid ty buff

        streamgen :: Stream -> BS.CDefl
        streamgen (Stream sid _ expr ty) = genfun (generatorname sid) expr ty

        triggergen :: Trigger -> BS.CDefl
        triggergen (Trigger name guard _) =
          genfun (guardname name) guard Bool
