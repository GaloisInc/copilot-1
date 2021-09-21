{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

-- |
-- Module      : Copilot.Theorem.What4
-- Description : Prove spec properties using What4.
-- Copyright   : (c) Ben Selfridge, 2020
-- Maintainer  : benselfridge@galois.com
-- Stability   : experimental
-- Portability : POSIX
--
-- Spec properties are translated into the language of SMT solvers using
-- @What4@. A backend solver is then used to prove the property is true. The
-- technique is sound, but incomplete. If a property is proved true by this
-- technique, then it can be guaranteed to be true. However, if a property is
-- not proved true, that does not mean it isn't true. Very simple specifications
-- are unprovable by this technique, including:
--
-- @
-- a = True : a
-- @
--
-- The above specification will not be proved true. The reason is that this
-- technique does not perform any sort of induction. When proving the inner @a@
-- expression, the technique merely allocates a fresh constant standing for
-- "@a@, one timestep in the past." Nothing is asserted about the fresh
-- constant.
--
-- An example of a property that is provable by this approach is:
--
-- @
-- a = True : b
-- b = not a
--
-- -- Property: a || b
-- @
--
-- By allocating a fresh constant, @b_-1@, standing for "the value of @b@ one
-- timestep in the past", the equation for @a || b@ at some arbitrary point in
-- the future reduces to @b_-1 || not b_-1@, which is always true.
--
-- In addition to proving that the stream expression is true at some arbitrary
-- point in the future, we also prove it for the first @k@ timesteps, where @k@
-- is the maximum buffer length of all streams in the given spec. This amounts
-- to simply interpreting the spec, although external variables are still
-- represented as constants with unknown values.

module Copilot.Theorem.What4 where
--  ( prove, Solver(..), SatResult(..)
--  ) where

import qualified Copilot.Core.Expr as CE
import qualified Copilot.Core.Spec as CS
import qualified Copilot.Core.Type as CT

import qualified What4.Config           as WC
import qualified What4.Expr.Builder     as WB
import qualified What4.Interface        as WI
import qualified What4.Solver           as WS
import qualified What4.Solver.DReal     as WS

import Control.Monad.State
import Data.Foldable (foldrM)
import Data.List (genericLength)
import qualified Data.Map as Map
import Data.Parameterized.NatRepr
import Data.Parameterized.Nonce
import Data.Parameterized.Some

import Copilot.Theorem.What4.Translate

-- 'prove' function
--
-- To prove properties of a spec, we translate them into What4 using the TransM
-- monad (transformer on top of IO), then negate each property and ask a backend
-- solver to produce a model for the negation.

-- | The solvers supported by the what4 backend.
data Solver = CVC4 | DReal | Yices | Z3

-- | The 'prove' function returns results of this form for each property in a
-- spec.
data SatResult = Valid | Invalid | Unknown
  deriving Show

type CounterExample = [(String, Some CopilotValue)]

-- | Attempt to prove all of the properties in a spec via an SMT solver (which
-- must be installed locally on the host). Return an association list mapping
-- the names of each property to the result returned by the solver.
prove :: Solver
      -- ^ Solver to use
      -> CS.Spec
      -- ^ Spec
      -> IO [(CE.Name, SatResult)]
prove solver spec = do
  -- Setup symbolic backend
  Some ng <- newIONonceGenerator
  sym <- WB.newExprBuilder WB.FloatIEEERepr EmptyState ng

  -- Solver-specific options
  case solver of
    CVC4 -> WC.extendConfig WS.cvc4Options (WI.getConfiguration sym)
    DReal -> WC.extendConfig WS.drealOptions (WI.getConfiguration sym)
    Yices -> WC.extendConfig WS.yicesOptions (WI.getConfiguration sym)
    Z3 -> WC.extendConfig WS.z3Options (WI.getConfiguration sym)

  -- Define TransM action for proving properties. Doing this in TransM rather
  -- than IO allows us to reuse the state for each property.
  let proveProperties = forM (CS.specProperties spec) $ \pr -> do
        let bufLen (CS.Stream _ buf _ _) = genericLength buf
            maxBufLen = maximum (0 : (bufLen <$> CS.specStreams spec))
        prefix <- forM [0 .. maxBufLen - 1] $ \k -> do
          XBool p <- translateExpr sym mempty (CS.propertyExpr pr) (AbsoluteOffset k)
          return p

        -- translate the induction hypothesis for all values up to maxBufLen in the past
        ind_hyps <- forM [0 .. maxBufLen-1] $ \k -> do
          XBool hyp <- translateExpr sym mempty (CS.propertyExpr pr) (RelativeOffset k)
          return hyp

        -- translate the predicate for the "current" value
        XBool p <- translateExpr sym mempty (CS.propertyExpr pr) (RelativeOffset maxBufLen)

        -- compute the predicate (ind_hyps ==> p)
        p' <- liftIO $ foldrM (WI.impliesPred sym) p ind_hyps

        p_and_prefix <- liftIO $ foldrM (WI.andPred sym) p' prefix
        not_p_and_prefix <- liftIO $ WI.notPred sym p_and_prefix

        let clauses = [not_p_and_prefix]
        case solver of
          CVC4 -> liftIO $ WS.runCVC4InOverride sym WS.defaultLogData clauses $ \case
            WS.Sat (_ge, _) -> return (CS.propertyName pr, Invalid)
            WS.Unsat _ -> return (CS.propertyName pr, Valid)
            WS.Unknown -> return (CS.propertyName pr, Unknown)
          DReal -> liftIO $ WS.runDRealInOverride sym WS.defaultLogData clauses $ \case
            WS.Sat (_ge, _) -> return (CS.propertyName pr, Invalid)
            WS.Unsat _ -> return (CS.propertyName pr, Valid)
            WS.Unknown -> return (CS.propertyName pr, Unknown)
          Yices -> liftIO $ WS.runYicesInOverride sym WS.defaultLogData clauses $ \case
            WS.Sat _ge -> return (CS.propertyName pr, Invalid)
            WS.Unsat _ -> return (CS.propertyName pr, Valid)
            WS.Unknown -> return (CS.propertyName pr, Unknown)
          Z3 -> liftIO $ WS.runZ3InOverride sym WS.defaultLogData clauses $ \case
            WS.Sat (_ge, _) -> return (CS.propertyName pr, Invalid)
            WS.Unsat _ -> return (CS.propertyName pr, Valid)
            WS.Unknown -> return (CS.propertyName pr, Unknown)

  -- Execute the action and return the results for each property
  runTransM sym spec proveProperties


data BisimulationProofState t =
  BisimulationProofState
  { streamState :: [(CE.Id, Some CT.Type, [XExpr t])]
  }

data BisimulationProofBundle t =
  BisimulationProofBundle
  { initialStreamState :: BisimulationProofState t
  , preStreamState     :: BisimulationProofState t
  , postStreamState    :: BisimulationProofState t
  , externalInputs     :: [(CE.Name, Some CT.Type, XExpr t)]
  , triggerState       :: [(CE.Name, WB.BoolExpr t, [(Some CT.Type, XExpr t)])]
  , assumptions        :: [WB.BoolExpr t]
  }


computeBisimulationProofBundle ::
  WB.ExprBuilder t st fs ->
  [String] ->
  CS.Spec ->
  IO (BisimulationProofBundle t)
computeBisimulationProofBundle sym properties spec =
  do iss <- computeInitialStreamState sym spec
     runTransM sym spec $
       do prestate  <- computePrestate sym spec
          poststate <- computePoststate sym spec
          triggers  <- computeTriggerState sym spec
          assms     <- computeAssumptions sym properties spec
          externs   <- computeExternalInputs sym
          return
            BisimulationProofBundle
            { initialStreamState = iss
            , preStreamState  = prestate
            , postStreamState = poststate
            , externalInputs  = externs
            , triggerState    = triggers
            , assumptions     = assms
            }


computeInitialStreamState ::
  WB.ExprBuilder t st fs ->
  CS.Spec ->
  IO (BisimulationProofState t)
computeInitialStreamState sym spec =
  do xs <- forM (CS.specStreams spec) $
            \CS.Stream{ CS.streamId = nm, CS.streamExprType = tp, CS.streamBuffer = buf }  ->
            do vs <- mapM (translateConstExpr sym tp) buf
               return (nm, Some tp, vs)
     return (BisimulationProofState xs)

computePrestate ::
  WB.ExprBuilder t st fs ->
  CS.Spec ->
  TransM t (BisimulationProofState t)
computePrestate sym spec =
  do xs <- forM (CS.specStreams spec) $
             \CS.Stream{ CS.streamId = nm, CS.streamExprType = tp, CS.streamBuffer = buf } ->
             do let buflen = genericLength buf
                let idxes = RelativeOffset <$> [ 0 .. buflen-1 ]
                vs <- mapM (getStreamValue sym nm) idxes
                return (nm, Some tp, vs)
     return (BisimulationProofState xs)

computePoststate ::
  WB.ExprBuilder t st fs ->
  CS.Spec ->
  TransM t (BisimulationProofState t)
computePoststate sym spec =
  do xs <- forM (CS.specStreams spec) $
             \CS.Stream{ CS.streamId = nm, CS.streamExprType = tp, CS.streamBuffer = buf } ->
             do let buflen = genericLength buf
                let idxes = RelativeOffset <$> [ 1 .. buflen ]
                vs <- mapM (getStreamValue sym nm) idxes
                return (nm, Some tp, vs)
     return (BisimulationProofState xs)

computeTriggerState ::
  WB.ExprBuilder t st fs ->
  CS.Spec ->
  TransM t [(CE.Name, WB.BoolExpr t, [(Some CT.Type, XExpr t)])]
computeTriggerState sym spec = forM (CS.specTriggers spec) $
    \CS.Trigger{ CS.triggerName = nm, CS.triggerGuard = guard, CS.triggerArgs = args } ->
      do XBool guard' <- translateExpr sym mempty guard (RelativeOffset 0)
         args' <- mapM computeArg args
         return (nm, guard', args')
  where
   computeArg CE.UExpr{ CE.uExprType = tp, CE.uExprExpr = ex } =
     do v <- translateExpr sym mempty ex (RelativeOffset 0)
        return (Some tp, v)

computeExternalInputs ::
  WB.ExprBuilder t st fs ->
  TransM t [(CE.Name, Some CT.Type, XExpr t)]
computeExternalInputs sym =
  do exts <- Map.toList <$> gets mentionedExternals
     forM exts $ \(nm, Some tp) ->
       do v <- getExternConstant sym tp nm (RelativeOffset 0)
          return (nm, Some tp, v)

computeAssumptions ::
  WB.ExprBuilder t st fs ->
  [String] ->
  CS.Spec ->
  TransM t [WB.BoolExpr t]
computeAssumptions sym properties spec =
  concat <$>
  forM [ CS.propertyExpr p | p <- CS.specProperties spec, elem (CS.propertyName p) properties ] (\e ->
    forM [ 0 .. maxBufLen ] (\i ->
      do XBool b <- translateExpr sym mempty e (RelativeOffset i)
         return b))
 where
  bufLen (CS.Stream _ buf _ _) = genericLength buf
  maxBufLen = maximum (0 : (bufLen <$> CS.specStreams spec))
