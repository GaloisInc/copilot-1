-- Copyright © 2011 National Institute of Aerospace / Galois, Inc.

-- | Transform a Copilot Language specification into a Copilot Core
-- specification.

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE Safe                      #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Copilot.Language.Reify
  ( reify
  ) where

import qualified Copilot.Core as Core
import Copilot.Core (Typed, Id, typeOf)

import Copilot.Language.Analyze (analyze)
import Copilot.Language.Error   (impossible)
import Copilot.Language.Spec
import Copilot.Language.Stream (FunctionHandle (..), Stream (..))

import Copilot.Theorem.Prove

import Prelude hiding (id)
import Data.IORef
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import System.Mem.StableName.Dynamic
import System.Mem.StableName.Map (Map)
import qualified System.Mem.StableName.Map as M
import Control.Monad (liftM, unless)

-- | Transform a Copilot Language specification into a Copilot Core
-- specification.
reify :: Spec' a -> IO Core.Spec
reify spec = do
  analyze spec
  let trigs = triggers   $ runSpec spec
  let obsvs = observers  $ runSpec spec
  let props = properties $ runSpec spec
  let thms  = reverse $ theorems $ runSpec spec
  let fns   = functions $ runSpec spec
  refMkId         <- newIORef 0
  refVisited      <- newIORef M.empty
  refMap          <- newIORef []
  (fnNames, coreFunctions) <- mapAccumLM (mkFunction refMkId refVisited refMap) IntMap.empty fns
  coreTriggers    <- mapM (mkTrigger  refMkId refVisited refMap fnNames) trigs
  coreObservers   <- mapM (mkObserver refMkId refVisited refMap fnNames) obsvs
  coreProperties  <- mapM (mkProperty refMkId refVisited refMap fnNames) $ props ++ (map fst thms)
  coreStreams     <- readIORef refMap

  let cspec = Core.Spec
        { Core.specStreams    = reverse coreStreams
        , Core.specFunctions  = coreFunctions
        , Core.specObservers  = coreObservers
        , Core.specTriggers   = coreTriggers
        , Core.specProperties = coreProperties }

  results <- sequence $ zipWith (prove cspec) (map (\(Property n _,_) -> n) thms) $ map snd thms
  unless (and results) $ putStrLn "Warning: failed to check some proofs."

  return cspec

mapAccumLM :: Monad m => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, [y])
mapAccumLM _ acc [] = return (acc, [])
mapAccumLM f acc (x:xs) = do
    (acc', y) <- f acc x
    (acc'', ys) <- mapAccumLM f acc' xs
    return (acc'', y:ys)

-- | Transform a Copilot observer specification into a Copilot Core
-- observer specification.
{-# INLINE mkObserver #-}
mkObserver
  :: IORef Int
  -> IORef (Map Core.Id)
  -> IORef [Core.Stream]
  -> IntMap Core.Name
  -> Observer
  -> IO Core.Observer
mkObserver refMkId refStreams refMap fnNames (Observer name e) = do
  w <- mkExpr refMkId refStreams refMap fnNames e
  return Core.Observer
    { Core.observerName     = name
    , Core.observerExpr     = w
    , Core.observerExprType = typeOf }

-- | Transform a Copilot trigger specification into a Copilot Core
-- trigger specification.
{-# INLINE mkTrigger #-}
mkTrigger
  :: IORef Int
  -> IORef (Map Core.Id)
  -> IORef [Core.Stream]
  -> IntMap Core.Name
  -> Trigger
  -> IO Core.Trigger
mkTrigger refMkId refStreams refMap fnNames (Trigger name guard args) = do
  w1 <- mkExpr refMkId refStreams refMap fnNames guard
  args' <- mapM mkTriggerArg args
  return Core.Trigger
    { Core.triggerName  = name
    , Core.triggerGuard = w1
    , Core.triggerArgs  = args' }

  where

  mkTriggerArg :: Arg -> IO Core.UExpr
  mkTriggerArg (Arg e) = do
    w <- mkExpr refMkId refStreams refMap fnNames e
    return $ Core.UExpr typeOf w

-- | Transform a Copilot property specification into a Copilot Core
-- property specification.
{-# INLINE mkProperty #-}
mkProperty
  :: IORef Int
  -> IORef (Map Core.Id)
  -> IORef [Core.Stream]
  -> IntMap Core.Name
  -> Property
  -> IO Core.Property
mkProperty refMkId refStreams refMap fnNames (Property name p) = do
  p' <- mkProp refMkId refStreams refMap fnNames p
  return Core.Property
    { Core.propertyName  = name
    , Core.propertyProp  = p' }

-- | Transform a Copilot proposition into a Copilot Core proposition.
mkProp :: IORef Int
       -> IORef (Map Core.Id)
       -> IORef [Core.Stream]
       -> IntMap Core.Name
       -> Prop a
       -> IO Core.Prop
mkProp refMkId refStreams refMap fnNames prop =
  case prop of
    Forall e -> Core.Forall <$> mkExpr refMkId refStreams refMap fnNames e
    Exists e -> Core.Exists <$> mkExpr refMkId refStreams refMap fnNames e

mkFunction :: IORef Int
           -> IORef (Map Core.Id)
           -> IORef [Core.Stream]
           -> IntMap Core.Name
           -> Function
           -> IO (IntMap Core.Name, Core.Function)
mkFunction refMkId refStreams refMap fnNames (Function fHdlId (f :: Stream arg -> Stream res)) = do
  fnNameId <- mkId refMkId
  let fnName = "__function_" ++ show fnNameId
  let fnHdl :: Core.FunctionHandle arg res
      fnHdl =
        Core.FunctionHandle
          { Core.fnHdlName = fnName
          , Core.fnHdlArgType = typeOf
          , Core.fnHdlResType = typeOf
          }
  fnArgNameId <- mkId refMkId
  let fnArgName = "arg_" ++ show fnArgNameId
  body <- mkExpr refMkId refStreams refMap fnNames (f (Var fnArgName))
  let fnNames' = IntMap.insert fHdlId fnName fnNames
  let fn = Core.Function $ Core.FunctionDef
             { Core.fnDefHandle = fnHdl
             , Core.fnDefArgName = fnArgName
             , Core.fnDefBody = body
             }
  pure (fnNames', fn)

-- | Transform a Copilot stream expression into a Copilot Core expression.
{-# INLINE mkExpr #-}
mkExpr
  :: Typed a
  => IORef Int
  -> IORef (Map Core.Id)
  -> IORef [Core.Stream]
  -> IntMap Core.Name
  -> Stream a
  -> IO (Core.Expr a)
mkExpr refMkId refStreams refMap fnNames = go

  where
  go :: Typed a => Stream a -> IO (Core.Expr a)
  go e0 = case e0 of

    ------------------------------------------------------

    Append _ _ _ -> do
      s <- mkStream refMkId refStreams refMap fnNames e0
      return $ Core.Drop typeOf 0 s

    ------------------------------------------------------

    Drop k e1 -> case e1 of
      Append _ _ _ -> do
          s <- mkStream refMkId refStreams refMap fnNames e1
          return $ Core.Drop typeOf (fromIntegral k) s
      _ -> impossible "mkExpr" "copilot-language"

    ------------------------------------------------------

    Const x -> return $ Core.Const typeOf x

    ------------------------------------------------------

    Local e f -> do
        id <- mkId refMkId
        let cs = "local_" ++ show id
        w1 <- go e
        w2 <- go (f (Var cs))
        return $ Core.Local typeOf typeOf cs w1 w2

    ------------------------------------------------------

    Label s e -> do
        w <- go e
        return $ Core.Label typeOf s w

    ------------------------------------------------------

    Var cs -> return $ Core.Var typeOf cs

    ------------------------------------------------------

    Extern cs mXs -> return $ Core.ExternVar typeOf cs mXs

    ------------------------------------------------------

    Op1 op e -> do
      w <- go e
      return $ Core.Op1 op w

    ------------------------------------------------------

    Op2 op e1 e2 -> do
      w1 <- go e1
      w2 <- go e2
      return $ Core.Op2 op w1 w2

    ------------------------------------------------------

    Op3 op e1 e2 e3 -> do
      w1 <- go e1
      w2 <- go e2
      w3 <- go e3
      return $ Core.Op3 op w1 w2 w3

    ------------------------------------------------------

    CallFunction fnHdl x -> do
      fnName <-
        case IntMap.lookup (fnHdlId fnHdl) fnNames of
          Nothing -> error "Could not look up function"
          Just fnName -> pure fnName
      let fnHdl' =
            Core.FunctionHandle
              { Core.fnHdlName = fnName
              , Core.fnHdlArgType = typeOf
              , Core.fnHdlResType = typeOf
              }
      x' <- go x
      pure $ Core.CallFunction fnHdl' x'

    ------------------------------------------------------

  mkFunArg :: Arg -> IO Core.UExpr
  mkFunArg (Arg e) = do
    w <- mkExpr refMkId refStreams refMap fnNames e
    return $ Core.UExpr typeOf w

  mkStrArg :: (Core.Name, Arg) -> IO (Core.Name, Core.UExpr)
  mkStrArg (name, Arg e) = do
    w <- mkExpr refMkId refStreams refMap fnNames e
    return $ (name, Core.UExpr typeOf w)

-- | Transform a Copilot stream expression into a Copilot Core stream
-- expression.
{-# INLINE mkStream #-}
mkStream
  :: Typed a
  => IORef Int
  -> IORef (Map Core.Id)
  -> IORef [Core.Stream]
  -> IntMap Core.Name
  -> Stream a
  -> IO Id
mkStream refMkId refStreams refMap fnNames e0 = do
  dstn <- makeDynStableName e0
  let Append buf _ e = e0 -- avoids warning
  mk <- haveVisited dstn
  case mk of
    Just id_ -> return id_
    Nothing  -> addToVisited dstn buf e

  where

  {-# INLINE haveVisited #-}
  haveVisited :: DynStableName -> IO (Maybe Int)
  haveVisited dstn = do
    tab <- readIORef refStreams
    return (M.lookup dstn tab)

  {-# INLINE addToVisited #-}
  addToVisited
    :: Typed a
    => DynStableName
    -> [a]
    -> Stream a
    -> IO Id
  addToVisited dstn buf e = do
    id <- mkId refMkId
    modifyIORef refStreams (M.insert dstn id)
    w <- mkExpr refMkId refStreams refMap fnNames e
    modifyIORef refMap $ (:)
      Core.Stream
        { Core.streamId         = id
        , Core.streamBuffer     = buf
        , Core.streamExpr       = w
        , Core.streamExprType   = typeOf }
    return id

-- | Create a fresh, unused 'Id'.
mkId :: IORef Int -> IO Id
mkId refMkId = atomicModifyIORef refMkId $ \ n -> (succ n, n)
