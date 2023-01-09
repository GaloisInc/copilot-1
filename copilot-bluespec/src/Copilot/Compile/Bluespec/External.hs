{-# LANGUAGE ExistentialQuantification #-}
-- | Represent information about externs needed in the generation of Bluespec code
-- for stream declarations and triggers.
module Copilot.Compile.Bluespec.External where

-- External modules
import Data.List  (unionBy)
import Data.Maybe (catMaybes)

-- External modules: Copilot
import Copilot.Core
import Copilot.Core.Extra

-- | Representation of external variables.
data External = forall a. External
  { extname :: String
  , exttype :: Type a
  }

-- | Union over lists of External, we solely base the equality on the
-- extname's.
extunion :: [External] -> [External] -> [External]
extunion = unionBy (\a b -> extname a == extname b)

-- | Collect all external variables from the streams and triggers.
--
-- Although Copilot specifications can contain also properties and theorems,
-- the Bluespec backend currently only generates code for streams and triggers.
gatherexts :: [Stream] -> [Trigger] -> [External]
gatherexts streams triggers = streamsexts `extunion` triggersexts
  where
    streamsexts  = foldr extunion mempty $ map streamexts streams
    triggersexts = foldr extunion mempty $ map triggerexts triggers

    streamexts :: Stream -> [External]
    streamexts (Stream _ _ expr _) = exprexts expr

    triggerexts :: Trigger -> [External]
    triggerexts (Trigger _ guard args) = guardexts `extunion` argexts
      where
        guardexts = exprexts guard
        argexts   = concat $ map uexprexts args

    uexprexts :: UExpr -> [External]
    uexprexts (UExpr _ expr) = exprexts expr

    exprexts :: Expr a -> [External]
    exprexts expr = let rec = exprexts in case expr of
      Local _ _ _ e1 e2   -> rec e1 `extunion` rec e2
      ExternVar ty name _ -> [External name ty]
      Op1 _ e             -> rec e
      Op2 _ e1 e2         -> rec e1 `extunion` rec e2
      Op3 _ e1 e2 e3      -> rec e1 `extunion` rec e2 `extunion` rec e3
      Label _ _ e         -> rec e
      _                   -> []
