{-# LANGUAGE OverloadedStrings #-}

-- | Compile Copilot specifications to Bluespec code.
module Copilot.Compile.Bluespec.Compile
  ( compile
  , compileWith
  ) where

import Data.List                      (nub)
import Data.Maybe                     (catMaybes)
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
compileWith bsSettings prefix spec
  | null (specTriggers spec)
  = do hPutStrLn stderr $
         "Copilot error: attempt at compiling empty specification.\n"
         ++ "You must define at least one trigger to generate Bluespec monitors."
       exitFailure

  | otherwise
  = do let typesBsFile = render $ pPrint $ compileTypesBS bsSettings prefix spec
           ifcBsFile   = render $ pPrint $ compileIfcBS   bsSettings prefix spec
           bsFile      = render $ pPrint $ compileBS      bsSettings prefix spec

       let dir = bluespecSettingsOutputDirectory bsSettings
       createDirectoryIfMissing True dir
       writeFile (dir </> spectypesname prefix ++ ".bs") typesBsFile
       writeFile (dir </> specinterfacename prefix ++ ".bs") ifcBsFile
       writeFile (dir </> prefix ++ ".bs") bsFile

-- | Compile a specification to a Bluespec.
--
-- The first argument is used as a prefix for the generated .bs files.
compile :: String -> Spec -> IO ()
compile = compileWith mkDefaultBluespecSettings

-- | Generate a @<prefix>.bs@ file from a 'Spec'. This is the main payload of
-- the Bluespec backend.
--
-- The generated Bluespec file will import a handful of files from the standard
-- library, as well as the following generated files:
--
-- * @<prefix>Ifc.bs@, which defines the interface containing the trigger
--   functions and external variables.
--
-- * @<prefix>Types.bs@, which defines any structs used in the 'Spec'.
--
-- It will also generate a @mk<prefix> :: Module <prefix>Ifc -> Module Empty@
-- function, which defines the module structure for this 'Spec'. The
-- @mk<prefix>@ function has the following structure:
--
-- * First, bind the argument of type @Module <prefix>Ifc@ so that trigger
--   functions can be invoked and external variables can be used.
--
-- * Next, declare stream buffers and indices.
--
-- * Next, declare generator functions for streams, accessor functions for
--   streams, and guard functions for triggers.
--
-- * Next, declare rules for each trigger function.
--
-- * Finally, declare a single rule that updates the stream buffers and
--   indices.
compileBS :: BluespecSettings -> String -> Spec -> BS.CPackage
compileBS _bsSettings prefix spec =
    BS.CPackage
      (BS.mkId BS.NoPos (fromString prefix))
      (Right [])
      (stdLibImports ++ genImports)
      []
      [moduleDef]
      []
  where
    -- import <prefix>Types
    -- import <prefix>Ifc
    genImports :: [BS.CImport]
    genImports =
      [ BS.CImpId False $ BS.mkId BS.NoPos $ fromString
                        $ spectypesname prefix
      , BS.CImpId False $ BS.mkId BS.NoPos $ fromString
                        $ specinterfacename prefix
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

    ifcargid = BS.mkId BS.NoPos $ fromString ifcargname
    ifcmodid = BS.mkId BS.NoPos "ifcMod"

    rules :: [BS.CRule]
    rules = map mktriggerrule triggers ++ [mksteprule streams]

    streams  = specStreams spec
    triggers = specTriggers spec
    exts     = gatherexts streams triggers

    ifcid     = BS.mkId BS.NoPos $ fromString $ specinterfacename prefix
    ifcfields = mkspecifcfields triggers exts

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
                             ++ concatMap triggergen triggers
      where

        accessdecln :: Stream -> BS.CDefl
        accessdecln (Stream sid buff _ ty) = mkaccessdecln sid ty buff

        streamgen :: Stream -> BS.CDefl
        streamgen (Stream sid _ expr ty) = genfun (generatorname sid) expr ty

        triggergen :: Trigger -> [BS.CDefl]
        triggergen (Trigger name guard args) = guarddef : argdefs
          where
            guarddef = genfun (guardname name) guard Bool
            argdefs  = map arggen (zip (argnames name) args)

            arggen :: (String, UExpr) -> BS.CDefl
            arggen (argname, UExpr ty expr) = genfun argname expr ty

-- | Generate a @<prefix>Ifc.bs@ file from a 'Spec'. This contains the
-- definition of the @<prefix>Ifc@ interface, which declares the types of all
-- trigger functions and external variables. This is put in a separate file so
-- that larger applications can use it separately.
compileIfcBS :: BluespecSettings -> String -> Spec -> BS.CPackage
compileIfcBS _bsSettings prefix spec =
    BS.CPackage
      ifcid
      (Right [])
      (stdLibImports ++ genImports)
      []
      [ifcDef]
      []
  where
    -- import <prefix>Types
    genImports :: [BS.CImport]
    genImports =
      [ BS.CImpId False $ BS.mkId BS.NoPos $ fromString
                        $ spectypesname prefix
      ]

    ifcid     = BS.mkId BS.NoPos $ fromString $ specinterfacename prefix
    ifcfields = mkspecifcfields triggers exts

    streams  = specStreams spec
    triggers = specTriggers spec
    exts     = gatherexts streams triggers

    ifcDef :: BS.CDefn
    ifcDef = BS.Cstruct
               True
               (BS.SInterface [])
               (BS.IdK ifcid)
               [] -- No type variables
               ifcfields
               [] -- No derived instances

-- | Generate a @<prefix>Types.bs@ file from a 'Spec'. This declares the types
-- of any structs used by the Copilot specification. This is put in a separate
-- file so that larger applications can more easily substitute their own struct
-- definitions if desired.
compileTypesBS :: BluespecSettings -> String -> Spec -> BS.CPackage
compileTypesBS _bsSettings prefix spec =
    BS.CPackage
      typesid
      (Right [])
      stdLibImports
      []
      structDefs
      []
  where
    typesid = BS.mkId BS.NoPos $ fromString $ spectypesname prefix

    structDefs = mkTypeDeclns exprs

    exprs    = gatherexprs streams triggers
    streams  = specStreams spec
    triggers = specTriggers spec

    -- Generate type declarations.
    mkTypeDeclns :: [UExpr] -> [BS.CDefn]
    mkTypeDeclns es = catMaybes $ map mkTypeDecln uTypes
      where
        uTypes = nub $ concatMap (\(UExpr _ e) -> exprtypes e) es

        mkTypeDecln (UType ty) = case ty of
          Struct _ -> Just $ mkstructdecln ty
          _        -> Nothing

-- | Imports from the Bluespec standard library.
stdLibImports :: [BS.CImport]
stdLibImports =
  [ BS.CImpId False $ BS.mkId BS.NoPos "FloatingPoint"
  , BS.CImpId False $ BS.mkId BS.NoPos "Vector"
  ]
