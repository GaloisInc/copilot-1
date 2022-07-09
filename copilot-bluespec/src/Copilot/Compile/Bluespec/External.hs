{-# LANGUAGE ExistentialQuantification #-}
-- | Represent information about externs needed in the generation of Bluespec code
-- for stream declarations and triggers.
module Copilot.Compile.Bluespec.External where

-- External modules
import Data.List  (nubBy)
import Data.Maybe (catMaybes)

-- External modules: Copilot
import Copilot.Core (Expr (ExternVar), Stream, Trigger, Type)

-- Internal modules
import Copilot.Compile.Bluespec.Util (excpyname)
import Copilot.Core.Extra       (flattenStreams, flattenTriggers)

-- | Representation of external variables.
data External = forall a. External
  { extname    :: String
  , extcpyname :: String
  , exttype    :: Type a
  }

-- | Collect all external variables from the streams and triggers.
--
-- Although Copilot specifications can contain also properties and theorems,
-- the Bluespec backend currently only generates code for streams and triggers.
gatherexts :: [Stream] -> [Trigger] -> [External]
gatherexts streams triggers
    = nubBy (\a b -> extname a == extname b)
    $ catMaybes
    $ concatMap (flattenStreams exprext) streams
      ++ concatMap (flattenTriggers exprext) triggers
  where
    exprext :: Expr a -> Maybe External
    exprext (ExternVar ty name _) = Just (External name (excpyname name) ty)
    exprext _                     = Nothing
