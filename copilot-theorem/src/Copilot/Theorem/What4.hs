{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

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
-- not proved true, that does not mean it isn't true; the proof may fail
-- because the given property is not inductive.
--
-- We perform @k@-induction on all the properties in a given specifiaction where
-- @k@ is chosen to be the maximum amount of delay on any of the involved streams.
-- This is a heuristic choice, but often effective.
--
-- TODO, we should reogranize this proof technique into the API of "Copilot.Theorem.Prove",
-- which allows users more control over what properties are proved and how the proofs
-- are constructed.
module Copilot.Theorem.What4
  ( Solver(..)
  , SatResult(..)
  , prove

  , BisimulationProofState(..)
  , BisimulationProofBundle(..)
  , computeBisimulationProofBundle

  , module Copilot.Theorem.What4.Translate
  ) where

import qualified Copilot.Core.Expr as CE
import qualified Copilot.Core.Spec as CS
import qualified Copilot.Core.Type as CT

import qualified What4.Config                   as WC
import qualified What4.Expr.Builder             as WB
import qualified What4.Interface                as WI
import qualified What4.InterpretedFloatingPoint as WFP
import qualified What4.Solver                   as WS
import qualified What4.Solver.DReal             as WS

import Control.Monad.State
import Data.Foldable (foldrM)
import Data.List (genericLength)
import qualified Data.Map as Map
import Data.Parameterized.NatRepr
import Data.Parameterized.Nonce
import Data.Parameterized.Some

import Copilot.Theorem.What4.Translate

--------------------------------------------------------------------------------
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

  -- Compute the maximum amount of delay for any stream in this spec
  let bufLen (CS.Stream _ buf _ _) = genericLength buf
      maxBufLen = maximum (0 : (bufLen <$> CS.specStreams spec))

  -- This process performs k-induction where we use @k = maxBufLen@.
  -- The choice for @k@ is heuristic, but often effective.
  -- TODO We should allow users to specify alternate k values, including 0 (no induction).
  let proveProperties = forM (CS.specProperties spec) $ \pr -> do

        -- State the base cases for k induction.
        base_cases <- forM [0 .. maxBufLen - 1] $ \i -> do
          translateExpr sym mempty (CS.propertyExpr pr) (AbsoluteOffset i) >>= \case
            XBool p -> return p
            xe -> panic ["Property expected to have boolean result", show xe]

        -- Translate the induction hypothesis for all values up to maxBufLen in the past
        ind_hyps <- forM [0 .. maxBufLen-1] $ \i -> do
          translateExpr sym mempty (CS.propertyExpr pr) (RelativeOffset i) >>= \case
            XBool hyp -> return hyp
            xe -> panic ["Property expected to have boolean result", show xe]

        -- Translate the predicate for the "current" value
        ind_goal <-
          translateExpr sym mempty (CS.propertyExpr pr) (RelativeOffset maxBufLen) >>= \case
            XBool p -> return p
            xe -> panic ["Property expected to have boolean result", show xe]

        -- Compute the predicate (ind_hyps ==> p)
        ind_case <- liftIO $ foldrM (WI.impliesPred sym) ind_goal ind_hyps

        -- Compute the conjunction of the base and inductive cases
        p <- liftIO $ foldrM (WI.andPred sym) ind_case base_cases

        -- Negate the goals for for SAT search
        not_p <- liftIO $ WI.notPred sym p
        let clauses = [not_p]

        -- TODO, we could determine if the property fails in one of the base cases
        --  (a true model-checking failure) or in the inductive step and report
        --  to the user.
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


data BisimulationProofState sym =
  BisimulationProofState
  { streamState :: [(CE.Id, Some CT.Type, [XExpr sym])]
  }

data BisimulationProofBundle sym =
  BisimulationProofBundle
  { initialStreamState :: BisimulationProofState sym
  , preStreamState     :: BisimulationProofState sym
  , postStreamState    :: BisimulationProofState sym
  , externalInputs     :: [(CE.Name, Some CT.Type, XExpr sym)]
  , triggerState       :: [(CE.Name, WI.Pred sym, [(Some CT.Type, XExpr sym)])]
  , assumptions        :: [WI.Pred sym]
  }


computeBisimulationProofBundle ::
  WFP.IsInterpretedFloatSymExprBuilder sym =>
  sym ->
  [String] ->
  CS.Spec ->
  IO (BisimulationProofBundle sym)
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
  WFP.IsInterpretedFloatSymExprBuilder sym =>
  sym ->
  CS.Spec ->
  IO (BisimulationProofState sym)
computeInitialStreamState sym spec =
  do xs <- forM (CS.specStreams spec) $
            \CS.Stream{ CS.streamId = nm, CS.streamExprType = tp, CS.streamBuffer = buf }  ->
            do vs <- mapM (translateConstExpr sym tp) buf
               return (nm, Some tp, vs)
     return (BisimulationProofState xs)

computePrestate ::
  WFP.IsInterpretedFloatSymExprBuilder sym =>
  sym ->
  CS.Spec ->
  TransM sym (BisimulationProofState sym)
computePrestate sym spec =
  do xs <- forM (CS.specStreams spec) $
             \CS.Stream{ CS.streamId = nm, CS.streamExprType = tp, CS.streamBuffer = buf } ->
             do let buflen = genericLength buf
                let idxes = RelativeOffset <$> [ 0 .. buflen-1 ]
                vs <- mapM (getStreamValue sym nm) idxes
                return (nm, Some tp, vs)
     return (BisimulationProofState xs)

computePoststate ::
  WFP.IsInterpretedFloatSymExprBuilder sym =>
  sym ->
  CS.Spec ->
  TransM sym (BisimulationProofState sym)
computePoststate sym spec =
  do xs <- forM (CS.specStreams spec) $
             \CS.Stream{ CS.streamId = nm, CS.streamExprType = tp, CS.streamBuffer = buf } ->
             do let buflen = genericLength buf
                let idxes = RelativeOffset <$> [ 1 .. buflen ]
                vs <- mapM (getStreamValue sym nm) idxes
                return (nm, Some tp, vs)
     return (BisimulationProofState xs)

computeTriggerState ::
  WFP.IsInterpretedFloatSymExprBuilder sym =>
  sym ->
  CS.Spec ->
  TransM sym [(CE.Name, WI.Pred sym, [(Some CT.Type, XExpr sym)])]
computeTriggerState sym spec = forM (CS.specTriggers spec) $
    \CS.Trigger{ CS.triggerName = nm, CS.triggerGuard = guard, CS.triggerArgs = args } ->
      do guard' <- translateExpr sym mempty guard (RelativeOffset 0) >>= \case
                     XBool guard' -> return guard'
                     xe -> panic ["Trigger guard expected to have boolean result", show xe]
         args' <- mapM computeArg args
         return (nm, guard', args')
  where
   computeArg CE.UExpr{ CE.uExprType = tp, CE.uExprExpr = ex } =
     do v <- translateExpr sym mempty ex (RelativeOffset 0)
        return (Some tp, v)

computeExternalInputs ::
  WFP.IsInterpretedFloatSymExprBuilder sym =>
  sym ->
  TransM sym [(CE.Name, Some CT.Type, XExpr sym)]
computeExternalInputs sym =
  do exts <- Map.toList <$> gets mentionedExternals
     forM exts $ \(nm, Some tp) ->
       do v <- getExternConstant sym tp nm (RelativeOffset 0)
          return (nm, Some tp, v)

computeAssumptions ::
  WFP.IsInterpretedFloatSymExprBuilder sym =>
  sym ->
  [String] ->
  CS.Spec ->
  TransM sym [WI.Pred sym]
computeAssumptions sym properties spec =
  concat <$>
  forM [ CS.propertyExpr p | p <- CS.specProperties spec, elem (CS.propertyName p) properties ] (\e ->
    forM [ 0 .. maxBufLen ] (\i ->
      translateExpr sym mempty e (RelativeOffset i) >>= \case
        XBool b -> return b
        xe -> panic ["Property expected to have boolean result", show xe]))
 where
  bufLen (CS.Stream _ buf _ _) = genericLength buf
  maxBufLen = maximum (0 : (bufLen <$> CS.specStreams spec))
