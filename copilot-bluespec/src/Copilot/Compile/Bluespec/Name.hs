-- | Naming of variables and functions in Bluespec.
module Copilot.Compile.Bluespec.Name
  ( argNames
  , generatorName
  , guardName
  , ifcArgName
  , indexName
  , specIfcName
  , specTypesName
  , streamAccessorName
  , streamElemName
  , streamName
  , structName
  ) where

-- External imports: Copilot
import Copilot.Core (Id)

-- | Turn a specification name into the name of its module interface.
specIfcName :: String -> String
specIfcName prefix = prefix ++ "Ifc"

-- | Turn a specification name into the name of the module that declares its
-- struct types.
specTypesName :: String -> String
specTypesName prefix = prefix ++ "Types"

-- | Turn a stream id into a stream element name.
streamElemName :: Id -> Int -> String
streamElemName sId n = streamName sId ++ "_" ++ show n

-- | The name of the variable of type @<prefix>Ifc@. This is used to select
-- trigger functions and external variables.
ifcArgName :: String
ifcArgName = "ifc"

-- | Turn a Copilot struct name into the name of a Bluespec struct by prepending
-- the @BS_@ prefix (short for \"Bluespec\") at the front. This is done because
-- Bluespec requires all struct definitions to begin with an uppercase letter,
-- so prepending a prefix ensures that this requirement is meant while
-- regardless of how the original Copilot struct name is capitalized.
structName :: String -> String
structName n = "BS_" ++ n

-----
-- TODO RGS: Everything below is copy-pasted directly from copilot-c99. Factor it out somewhere?
-----

-- | Turn a stream id into a suitable Bluespec variable name.
streamName :: Id -> String
streamName sId = "s" ++ show sId

-- | Turn a stream id into the global varname for indices.
indexName :: Id -> String
indexName sId = streamName sId ++ "_idx"

-- | Turn a stream id into the name of its accessor function
streamAccessorName :: Id -> String
streamAccessorName sId = streamName sId ++ "_get"

-- | Turn stream id into name of its generator function.
generatorName :: Id -> String
generatorName sId = streamName sId ++ "_gen"

-- | Turn the name of a trigger into a guard generator.
guardName :: String -> String
guardName name = name ++ "_guard"

-- | Turn a trigger name into a an trigger argument name.
argName :: String -> Int -> String
argName name n = name ++ "_arg" ++ show n

-- | Enumerate all argument names based on trigger name.
argNames :: String -> [String]
argNames base = map (argName base) [0..]
