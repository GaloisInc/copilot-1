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

module Copilot.Theorem.What4
  ( prove, Solver(..), SatResult(..)
  ) where

import qualified Copilot.Core.Expr       as CE
import qualified Copilot.Core.Spec       as CS
import qualified Copilot.Core.Type       as CT

import qualified What4.Config           as WC
import qualified What4.Expr.Builder     as WB
import qualified What4.Expr.GroundEval  as WG
import qualified What4.Interface        as WI
import qualified What4.InterpretedFloatingPoint as WFP
import qualified What4.Solver           as WS
import qualified What4.Solver.DReal     as WS

import Control.Monad.State
import qualified Data.BitVector.Sized as BV
import Data.Foldable (foldrM)
import Data.List (genericLength)
import Data.Parameterized.NatRepr
import Data.Parameterized.Nonce
import Data.Parameterized.Some
import GHC.Float (castWord32ToFloat, castWord64ToDouble)
import LibBF (BigFloat, bfToDouble, pattern NearEven)
import qualified Panic as Panic

import           Copilot.Theorem.What4.Translate

-- 'prove' function
--
-- To prove properties of a spec, we translate them into What4 using the TransM
-- monad (transformer on top of IO), then negate each property and ask a backend
-- solver to produce a model for the negation.

-- | No builder state needed.
data BuilderState a = EmptyState

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
          xe <- translateExpr sym mempty (CS.propertyExpr pr) (AbsoluteOffset k)
          case xe of
            XBool p -> return p
            _ -> expectedBool xe
        p <- do
          xe <- translateExpr sym
                              mempty
                              (CS.propertyExpr pr)
                              (RelativeOffset maxBufLen)
          case xe of
            XBool p -> return p
            _ -> expectedBool xe
        p_and_prefix <- liftIO $ foldrM (WI.andPred sym) p prefix
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
  runTransM spec proveProperties
  where
    expectedBool :: forall m sym a.
                    (Panic.HasCallStack, MonadIO m, WI.IsExprBuilder sym)
                 => XExpr sym
                 -> m a
    expectedBool xe =
      panic ["Property expected to have boolean result", show xe]

data CopilotValue a = CopilotValue { cvType :: CT.Type a
                                   , cvVal :: a
                                   }

valFromExpr :: forall sym t st fm.
               ( sym ~ WB.ExprBuilder t st (WB.Flags fm)
               , WI.KnownRepr WB.FloatModeRepr fm
               )
            => WG.GroundEvalFn t
            -> XExpr sym
            -> IO (Some CopilotValue)
valFromExpr ge xe = case xe of
  XBool e -> Some . CopilotValue CT.Bool <$> WG.groundEval ge e
  XInt8 e -> Some . CopilotValue CT.Int8 . fromBV <$> WG.groundEval ge e
  XInt16 e -> Some . CopilotValue CT.Int16 . fromBV <$> WG.groundEval ge e
  XInt32 e -> Some . CopilotValue CT.Int32 . fromBV <$> WG.groundEval ge e
  XInt64 e -> Some . CopilotValue CT.Int64 . fromBV <$> WG.groundEval ge e
  XWord8 e -> Some . CopilotValue CT.Word8 . fromBV <$> WG.groundEval ge e
  XWord16 e -> Some . CopilotValue CT.Word16 . fromBV <$> WG.groundEval ge e
  XWord32 e -> Some . CopilotValue CT.Word32 . fromBV <$> WG.groundEval ge e
  XWord64 e -> Some . CopilotValue CT.Word64 . fromBV <$> WG.groundEval ge e
  XFloat e ->
    Some . CopilotValue CT.Float <$>
      iFloatGroundEval WFP.SingleFloatRepr e
                       (realToFrac . fst . bfToDouble NearEven)
                       fromRational
                       (castWord32ToFloat . fromInteger . BV.asUnsigned)
  XDouble e ->
    Some . CopilotValue CT.Double <$>
      iFloatGroundEval WFP.DoubleFloatRepr e
                       (fst . bfToDouble NearEven)
                       fromRational
                       (castWord64ToDouble . fromInteger . BV.asUnsigned)
  _ -> error "valFromExpr unhandled case"
  where
    fromBV :: forall a w . Num a => BV.BV w -> a
    fromBV = fromInteger . BV.asUnsigned

    -- Evaluate a (possibly symbolic) floating-point value to a concrete result.
    -- Depending on which @what4@ floating-point mode is in use, the result will
    -- be passed to one of three different continuation arguments.
    iFloatGroundEval ::
      forall fi r.
      WFP.FloatInfoRepr fi ->
      WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi) ->
      (BigFloat -> r) ->
      -- ^ Continuation to use if the IEEE floating-point mode is in use.
      (Rational -> r) ->
      -- ^ Continuation to use if the real floating-point mode is in use.
      (forall w. BV.BV w -> r) ->
      -- ^ Continuation to use if the uninterpreted floating-point mode is in
      -- use.
      IO r
    iFloatGroundEval _ e ieeeK realK uninterpK =
      case WI.knownRepr :: WB.FloatModeRepr fm of
        WB.FloatIEEERepr          -> ieeeK <$> WG.groundEval ge e
        WB.FloatRealRepr          -> realK <$> WG.groundEval ge e
        WB.FloatUninterpretedRepr -> uninterpK <$> WG.groundEval ge e
