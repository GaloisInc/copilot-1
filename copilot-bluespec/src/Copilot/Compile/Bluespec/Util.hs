-- | Auxiliary helper functions to generate Bluespec code.
module Copilot.Compile.Bluespec.Util where

import Copilot.Core (Id)

-- | Turn a stream id into a suitable Bluespec variable name.
streamname :: Id -> String
streamname sid = "s" ++ show sid

-- | Turn a stream id into a stream element name.
streamelemname :: Id -> Int -> String
streamelemname sid n = streamname sid ++ "_" ++ show n

-- | Turn a stream id into the global varname for indices.
indexname :: Id -> String
indexname sid = streamname sid ++ "_idx"

-- | Turn a stream id into the name of its accessor function
streamaccessorname :: Id -> String
streamaccessorname sid = streamname sid ++ "_get"

-- | Turn stream id into name of its generator function.
generatorname :: Id -> String
generatorname sid = streamname sid ++ "_gen"

-- | Turn the name of a trigger into a guard generator.
guardname :: String -> String
guardname name = name ++ "_guard"

-- | Turn a trigger name into a an trigger argument name.
argname :: String -> Int -> String
argname name n = name ++ "_arg" ++ show n

-- | Turn a handler function name into a name for a temporary variable for a
-- handler argument.
argTempName :: String -> Int -> String
argTempName name n = name ++ "_arg_temp" ++ show n

-- | Enumerate all argument names based on trigger name.
argnames :: String -> [String]
argnames base = map (argname base) [0..]

-- | Turn a specification name into the name of its module interface
specinterfacename :: String -> String
specinterfacename prefix = prefix ++ "Ifc"
