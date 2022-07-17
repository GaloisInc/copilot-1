{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

-- |
-- Module      : Copilot.Theorem.What4.Translate
-- Description : Translate Copilot specifications into What4
-- Copyright   : (c) Galois Inc., 2021-2022
-- Maintainer  : robdockins@galois.com
-- Stability   : experimental
-- Portability : POSIX
--
-- Translate Copilot specifications to What4 formulas using the 'TransM' monad.
module Copilot.Theorem.What4.Translate
  ( -- * Translation into What4
    TransState(..)
  , TransM
  , runTransM
  , translateExpr
  , translateExprAt
    -- * What4 representations of Copilot expressions
  , XExpr(..)
    -- * Auxiliary functions
  , panic
  ) where

import           Control.Monad                  (forM, zipWithM)
import           Control.Monad.IO.Class         (MonadIO (..))
import           Control.Monad.State            (MonadState (..), StateT (..),
                                                 gets, modify)
import qualified Data.BitVector.Sized           as BV
import           Data.List                      (elemIndex, genericLength)
import qualified Data.Map                       as Map
import           Data.Maybe                     (fromJust)
import           Data.Parameterized.Classes     (KnownRepr (..))
import           Data.Parameterized.Context     (EmptyCtx, type (::>))
import           Data.Parameterized.NatRepr     (LeqProof (..), NatCases (..),
                                                 NatRepr, decNat, isZeroOrGT1,
                                                 knownNat, minusPlusCancel,
                                                 mkNatRepr, testNatCases)
import           Data.Parameterized.Some        (Some (..))
import           Data.Parameterized.SymbolRepr  (SymbolRepr, knownSymbol)
import qualified Data.Parameterized.Vector      as V
import           Data.Type.Equality             (TestEquality (..), (:~:) (..))
import           Data.Word                      (Word32)
import           GHC.TypeLits                   (KnownSymbol)
import           GHC.TypeNats                   (KnownNat, type (<=))
import qualified Panic                          as Panic

import qualified What4.BaseTypes                as WT
import qualified What4.Interface                as WI
import qualified What4.InterpretedFloatingPoint as WFP
import qualified What4.SpecialFunctions         as WSF

import qualified Copilot.Core.Expr              as CE
import qualified Copilot.Core.Operators         as CE
import qualified Copilot.Core.PrettyPrint       as CP
import qualified Copilot.Core.Spec              as CS
import qualified Copilot.Core.Type              as CT
import qualified Copilot.Core.Type.Array        as CT

-- Translation into What4

-- | The state for translating Copilot expressions into What4 expressions. As we
-- translate, we generate fresh symbolic constants for external variables and
-- for stream variables. We need to only generate one constant per variable, so
-- we allocate them in a map. When we need the constant for a particular
-- variable, we check if it is already in the map, and return it if it is; if it
-- isn't, we generate a fresh constant at that point, store it in the map, and
-- return it.
--
-- We also store 'streams', an immutable field, in this state, rather than wrap
-- it up in another monad transformer layer. This is initialized prior to
-- translation and is never modified. This maps from stream ids to the
-- core stream definitions.
data TransState sym = TransState {
  -- | Map of all external variables we encounter during translation. These are
  -- just fresh constants. The offset indicates how many timesteps in the past
  -- this constant represents for that stream.
  externVars :: Map.Map (CE.Name, Int) (XExpr sym),
  -- | Map of external variables at specific indices (positive), rather than
  -- offset into the past. This is for interpreting streams at specific offsets.
  externVarsAt :: Map.Map (CE.Name, Int) (XExpr sym),
  -- | Map from (stream id, negative offset) to fresh constant. These are all
  -- constants representing the values of a stream at some point in the past.
  -- The offset (ALWAYS NEGATIVE) indicates how many timesteps in the past
  -- this constant represents for that stream.
  streamConstants :: Map.Map (CE.Id, Int) (XExpr sym),
  -- | Map from stream ids to the streams themselves. This value is never
  -- modified, but I didn't want to make this an RWS, so it's represented as a
  -- stateful value.
  streams :: Map.Map CE.Id CS.Stream
  }

-- | A monad that tracks state needed when translating Copilot specifications to
-- What4 formulas.
newtype TransM sym a = TransM { unTransM :: StateT (TransState sym) IO a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadFail
           , MonadIO
           , MonadState (TransState sym)
           )

-- | Translate a Copilot specification using the given 'TransM' computation.
runTransM :: CS.Spec -> TransM sym a -> IO a
runTransM spec m = do
  -- Build up initial translation state
  let streamMap = Map.fromList $
        (\stream -> (CS.streamId stream, stream)) <$> CS.specStreams spec
      st = TransState
           { externVars = mempty
           , externVarsAt = mempty
           , streamConstants = mempty
           , streams = streamMap
           }

  (res, _) <- runStateT (unTransM m) st
  return res

-- | Translate an expression into a what4 representation. The int offset keeps
-- track of how many timesteps into the past each variable is referring to.
-- Initially the value should be zero, but when we translate a stream, the
-- offset is recomputed based on the length of that stream's prefix (subtracted)
-- and the drop index (added).
translateExpr :: WFP.IsInterpretedFloatSymExprBuilder sym
              => sym
              -> Int
              -- ^ number of timesteps in the past we are currently looking
              -- (must always be <= 0)
              -> CE.Expr a
              -> TransM sym (XExpr sym)
translateExpr sym offset e = case e of
  CE.Const tp a -> liftIO $ translateConstExpr sym tp a
  CE.Drop _tp ix streamId
    -- If we are referencing a past value of this stream, just return an
    -- unconstrained constant.
    | offset + fromIntegral ix < 0 ->
        getStreamConstant sym streamId (offset + fromIntegral ix)
    -- If we are referencing a current or future value of this stream, we need
    -- to translate the stream's expression, using an offset computed based on
    -- the current offset (negative or 0), the drop index (positive or 0), and
    -- the length of the stream's buffer (subtracted).
    | otherwise -> do
        CS.Stream _ buf e _ <- getStreamDef streamId
        translateExpr sym (offset + fromIntegral ix - length buf) e
  CE.Local _ _ _ _ _ -> error "translateExpr: Local unimplemented"
  CE.Var _ _ -> error "translateExpr: Var unimplemented"
  CE.ExternVar tp nm _prefix -> getExternConstant sym tp nm offset
  CE.Op1 op e1 -> do
    xe1 <- translateExpr sym offset e1
    liftIO $ translateOp1 sym e op xe1
  CE.Op2 op e1 e2 -> do
    xe1 <- translateExpr sym offset e1
    xe2 <- translateExpr sym offset e2
    liftIO $ translateOp2 sym e op xe1 xe2
  CE.Op3 op e1 e2 e3 -> do
    xe1 <- translateExpr sym offset e1
    xe2 <- translateExpr sym offset e2
    xe3 <- translateExpr sym offset e3
    liftIO $ translateOp3 sym e op xe1 xe2 xe3
  CE.Label _ _ _ -> error "translateExpr: Label unimplemented"

-- | Translate an expression into a what4 representation at a /specific/
-- timestep, rather than "at some indeterminate point in the future."
translateExprAt :: WFP.IsInterpretedFloatSymExprBuilder sym
                => sym
                -> Int
                -- ^ Index of timestep
                -> CE.Expr a
                -- ^ stream expression
                -> TransM sym (XExpr sym)
translateExprAt sym k e =
  case e of
    CE.Const tp a -> liftIO $ translateConstExpr sym tp a
    CE.Drop _tp ix streamId -> do
      CS.Stream _ buf e tp <- getStreamDef streamId
      if k' < length buf
        then liftIO $ translateConstExpr sym tp (buf !! k')
        else translateExprAt sym (k' - length buf) e
      where
        k' = k + fromIntegral ix
    CE.Local _ _ _ _ _ -> error "translateExpr: Local unimplemented"
    CE.Var _ _ -> error "translateExpr: Var unimplemented"
    CE.ExternVar tp nm _prefix -> getExternConstantAt sym tp nm k
    CE.Op1 op e1 -> do
      xe1 <- translateExprAt sym k e1
      liftIO $ translateOp1 sym e op xe1
    CE.Op2 op e1 e2 -> do
      xe1 <- translateExprAt sym k e1
      xe2 <- translateExprAt sym k e2
      liftIO $ translateOp2 sym e op xe1 xe2
    CE.Op3 op e1 e2 e3 -> do
      xe1 <- translateExprAt sym k e1
      xe2 <- translateExprAt sym k e2
      xe3 <- translateExprAt sym k e3
      liftIO $ translateOp3 sym e op xe1 xe2 xe3
    CE.Label _ _ _ -> error "translateExpr: Label unimplemented"

-- | A view of an XExpr as a bitvector expression, a natrepr for its width, its
-- signed/unsigned status, and the constructor used to reconstruct an XExpr from
-- it. This is a useful view for translation, as many of the operations can be
-- grouped together for all words\/ints\/floats.
data SomeBVExpr sym where
  SomeBVExpr ::
    1 <= w =>
    WI.SymBV sym w ->
    NatRepr w ->
    BVSign ->
    (WI.SymBV sym w -> XExpr sym) ->
    SomeBVExpr sym

-- | The sign of a bitvector -- this indicates whether it is to be interpreted
-- as a signed 'Int' or an unsigned 'Word'.
data BVSign = Signed | Unsigned

-- | If the inner expression can be viewed as a bitvector, we project out a view
-- of it as such.
asBVExpr :: XExpr sym -> Maybe (SomeBVExpr sym)
asBVExpr xe = case xe of
  XInt8 e -> Just (SomeBVExpr e knownNat Signed XInt8)
  XInt16 e -> Just (SomeBVExpr e knownNat Signed XInt16)
  XInt32 e -> Just (SomeBVExpr e knownNat Signed XInt32)
  XInt64 e -> Just (SomeBVExpr e knownNat Signed XInt64)
  XWord8 e -> Just (SomeBVExpr e knownNat Unsigned XWord8)
  XWord16 e -> Just (SomeBVExpr e knownNat Unsigned XWord16)
  XWord32 e -> Just (SomeBVExpr e knownNat Unsigned XWord32)
  XWord64 e -> Just (SomeBVExpr e knownNat Unsigned XWord64)
  _ -> Nothing

-- | Translate a constant expression by creating a what4 literal and packaging
-- it up into an 'XExpr'.
translateConstExpr :: forall sym a.
                      WFP.IsInterpretedFloatExprBuilder sym
                   => sym
                   -> CT.Type a
                   -> a
                   -> IO (XExpr sym)
translateConstExpr sym tp a = case tp of
  CT.Bool -> case a of
    True  -> return $ XBool (WI.truePred sym)
    False -> return $ XBool (WI.falsePred sym)
  CT.Int8 -> XInt8 <$> WI.bvLit sym knownNat (BV.int8 a)
  CT.Int16 -> XInt16 <$> WI.bvLit sym knownNat (BV.int16 a)
  CT.Int32 -> XInt32 <$> WI.bvLit sym knownNat (BV.int32 a)
  CT.Int64 -> XInt64 <$> WI.bvLit sym knownNat (BV.int64 a)
  CT.Word8 -> XWord8 <$> WI.bvLit sym knownNat (BV.word8 a)
  CT.Word16 -> XWord16 <$> WI.bvLit sym knownNat (BV.word16 a)
  CT.Word32 -> XWord32 <$> WI.bvLit sym knownNat (BV.word32 a)
  CT.Word64 -> XWord64 <$> WI.bvLit sym knownNat (BV.word64 a)
  CT.Float -> XFloat <$> WFP.iFloatLitSingle sym a
  CT.Double -> XDouble <$> WFP.iFloatLitDouble sym a
  CT.Array tp -> do
    elts <- traverse (translateConstExpr sym tp) (CT.arrayelems a)
    Some n <- return $ mkNatRepr (genericLength elts)
    case isZeroOrGT1 n of
      Left Refl -> return XEmptyArray
      Right LeqProof ->
        let Just v = V.fromList n elts in
        return $ XArray v
  CT.Struct _ -> do
    elts <- forM (CT.toValues a) $ \(CT.Value tp (CT.Field a)) ->
      translateConstExpr sym tp a
    return $ XStruct elts

-- | Retrieve the length of an 'CT.Array' type as a 'NatRepr'.
arrayLen :: KnownNat n => CT.Type (CT.Array n t) -> NatRepr n
arrayLen _ = knownNat

-- | Generate a fresh constant for a given copilot type. This will be called
-- whenever we attempt to get the constant for a given external variable or
-- stream variable, but that variable has not been accessed yet and therefore
-- has no constant allocated.
freshCPConstant :: forall sym a.
                   WFP.IsInterpretedFloatSymExprBuilder sym
                => sym
                -> String
                -> CT.Type a
                -> IO (XExpr sym)
freshCPConstant sym nm tp = case tp of
  CT.Bool -> XBool <$> WI.freshConstant sym (WI.safeSymbol nm) knownRepr
  CT.Int8 -> XInt8 <$> WI.freshConstant sym (WI.safeSymbol nm) knownRepr
  CT.Int16 -> XInt16 <$> WI.freshConstant sym (WI.safeSymbol nm) knownRepr
  CT.Int32 -> XInt32 <$> WI.freshConstant sym (WI.safeSymbol nm) knownRepr
  CT.Int64 -> XInt64 <$> WI.freshConstant sym (WI.safeSymbol nm) knownRepr
  CT.Word8 -> XWord8 <$> WI.freshConstant sym (WI.safeSymbol nm) knownRepr
  CT.Word16 -> XWord16 <$> WI.freshConstant sym (WI.safeSymbol nm) knownRepr
  CT.Word32 -> XWord32 <$> WI.freshConstant sym (WI.safeSymbol nm) knownRepr
  CT.Word64 -> XWord64 <$> WI.freshConstant sym (WI.safeSymbol nm) knownRepr
  CT.Float -> XFloat <$>
    WFP.freshFloatConstant sym (WI.safeSymbol nm) WFP.SingleFloatRepr
  CT.Double -> XDouble <$>
    WFP.freshFloatConstant sym (WI.safeSymbol nm) WFP.DoubleFloatRepr
  atp@(CT.Array itp) -> do
    let n = arrayLen atp
    case isZeroOrGT1 n of
      Left Refl -> return XEmptyArray
      Right LeqProof -> do
        Refl <- return $ minusPlusCancel n (knownNat @1)
        elts :: V.Vector n (XExpr t) <-
          V.generateM (decNat n) (const (freshCPConstant sym "" itp))
        return $ XArray elts
  CT.Struct stp -> do
    elts <- forM (CT.toValues stp) $ \(CT.Value ftp _) ->
      freshCPConstant sym "" ftp
    return $ XStruct elts

-- | Get the constant for a given stream id and some offset into the past. This
-- should only be called with a strictly negative offset. When this function
-- gets called for the first time for a given (streamId, offset) pair, it
-- generates a fresh constant and stores it in an internal map. Thereafter, this
-- function will just return that constant when called with the same pair.
getStreamConstant :: WFP.IsInterpretedFloatSymExprBuilder sym
                  => sym
                  -> CE.Id
                  -> Int
                  -> TransM sym (XExpr sym)
getStreamConstant sym streamId offset = do
  scs <- gets streamConstants
  case Map.lookup (streamId, offset) scs of
    Just xe -> return xe
    Nothing -> do
      CS.Stream _ _ _ tp <- getStreamDef streamId
      let nm = show streamId ++ "_" ++ show offset
      xe <- liftIO $ freshCPConstant sym nm tp
      modify (\st ->
        st { streamConstants =
               Map.insert (streamId, offset) xe scs })
      return xe

-- | Get the constant for a given external variable and some offset into the
-- past. This should only be called with a strictly negative offset. When this
-- function gets called for the first time for a given (var, offset) pair, it
-- generates a fresh constant and stores it in an internal map. Thereafter, this
-- function will just return that constant when called with the same pair.
getExternConstant :: WFP.IsInterpretedFloatSymExprBuilder sym
                  => sym
                  -> CT.Type a
                  -> CE.Name
                  -> Int
                  -> TransM sym (XExpr sym)
getExternConstant sym tp var offset = do
  es <- gets externVars
  case Map.lookup (var, offset) es of
    Just xe -> return xe
    Nothing -> do
      xe <- liftIO $ freshCPConstant sym var tp
      modify (\st -> st { externVars = Map.insert (var, offset) xe es} )
      return xe

-- | Get the constant for a given external variable at some specific timestep.
getExternConstantAt :: WFP.IsInterpretedFloatSymExprBuilder sym
                    => sym
                    -> CT.Type a
                    -> CE.Name
                    -> Int
                    -> TransM sym (XExpr sym)
getExternConstantAt sym tp var ix = do
  es <- gets externVarsAt
  case Map.lookup (var, ix) es of
    Just xe -> return xe
    Nothing -> do
      xe <- liftIO $ freshCPConstant sym var tp
      modify (\st -> st { externVarsAt = Map.insert (var, ix) xe es} )
      return xe

-- | Retrieve a stream definition given its id.
getStreamDef :: CE.Id -> TransM sym CS.Stream
getStreamDef streamId = fromJust <$> gets (Map.lookup streamId . streams)

-- | A unary operation over bitvector values.
type BVOp1 sym w = (KnownNat w, 1 <= w) => WI.SymBV sym w -> IO (WI.SymBV sym w)

-- | A unary operation over floating-point values.
type FPOp1 sym fi =
     WFP.FloatInfoRepr fi
  -> WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi)
  -> IO (WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi))

-- | Retrieve a 'CT.Field' name as a 'SymbolRepr'.
fieldName :: KnownSymbol s => CT.Field s a -> SymbolRepr s
fieldName _ = knownSymbol

-- | Retrieve a 'CT.Value' name as a 'SymbolRepr'.
valueName :: CT.Value a -> Some SymbolRepr
valueName (CT.Value _ f) = Some (fieldName f)

-- | Translate a unary operation and its argument into a what4 representation of
-- the operation applied to the argument.
translateOp1 :: forall sym a b.
                WFP.IsInterpretedFloatExprBuilder sym
             => sym
             -> CE.Expr b
             -- ^ Original value we are translating (only used for error
             -- messages)
             -> CE.Op1 a b
             -> XExpr sym
             -> IO (XExpr sym)
translateOp1 sym origExpr op xe = case (op, xe) of
  (CE.Not, XBool e) -> XBool <$> WI.notPred sym e
  (CE.Not, _) -> panic ["Expected bool", show xe]
  (CE.Abs _, xe) -> translateAbs xe
  (CE.Sign _, xe) -> translateSign xe
  (CE.Recip _, xe) -> fpOp recip xe
    where
      recip :: forall fi . FPOp1 sym fi
      recip fiRepr e = do
        one <- fpLit fiRepr 1.0
        WFP.iFloatDiv @_ @fi sym fpRM one e
  (CE.Exp _, xe) -> fpSpecialOp WSF.Exp xe
  (CE.Sqrt _, xe) ->
    fpOp (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatSqrt @_ @fi sym fpRM) xe
  (CE.Log _, xe) -> fpSpecialOp WSF.Log xe
  (CE.Sin _, xe) -> fpSpecialOp WSF.Sin xe
  (CE.Cos _, xe) -> fpSpecialOp WSF.Cos xe
  (CE.Tan _, xe) -> fpSpecialOp WSF.Tan xe
  (CE.Sinh _, xe) -> fpSpecialOp WSF.Sinh xe
  (CE.Cosh _, xe) -> fpSpecialOp WSF.Cosh xe
  (CE.Tanh _, xe) -> fpSpecialOp WSF.Tanh xe
  (CE.Asin _, xe) -> fpSpecialOp WSF.Arcsin xe
  (CE.Acos _, xe) -> fpSpecialOp WSF.Arccos xe
  (CE.Atan _, xe) -> fpSpecialOp WSF.Arctan xe
  (CE.Asinh _, xe) -> fpSpecialOp WSF.Arcsinh xe
  (CE.Acosh _, xe) -> fpSpecialOp WSF.Arccosh xe
  (CE.Atanh _, xe) -> fpSpecialOp WSF.Arctanh xe
  (CE.Ceiling _, xe) ->
    fpOp (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatRound @_ @fi sym WI.RTP) xe
  (CE.Floor _, xe) ->
    fpOp (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatRound @_ @fi sym WI.RTN) xe
  (CE.BwNot _, xe) -> case xe of
    XBool e -> XBool <$> WI.notPred sym e
    _ -> bvOp (WI.bvNotBits sym) xe
  (CE.Cast _ tp, xe) -> castOp sym origExpr tp xe
  (CE.GetField atp _ftp extractor, xe) -> translateGetField atp extractor xe
  where
    -- Translate an 'CE.Abs' operation and its argument into a what4
    -- representation of the appropriate type.
    translateAbs :: XExpr sym -> IO (XExpr sym)
    translateAbs xe = numOp bvAbs fpAbs xe
      where
        bvAbs :: BVOp1 sym w
        bvAbs e = do
          zero <- WI.bvLit sym knownNat (BV.zero knownNat)
          e_neg <- WI.bvSlt sym e zero
          neg_e <- WI.bvSub sym zero e
          WI.bvIte sym e_neg neg_e e

        fpAbs :: forall fi . FPOp1 sym fi
        fpAbs _ e = WFP.iFloatAbs @_ @fi sym e

    -- Translate a 'CE.GetField' operation and its argument into a what4
    -- representation. If the argument is not a struct, panic.
    translateGetField :: forall struct s.
                         KnownSymbol s
                      => CT.Type struct
                      -- ^ The type of the argument
                      -> (struct -> CT.Field s b)
                      -- ^ Extract a struct field
                      -> XExpr sym
                      -- ^ The argument value (should be a struct)
                      -> IO (XExpr sym)
    translateGetField tp extractor xe = case (tp, xe) of
      (CT.Struct s, XStruct xes) ->
        case mIx s of
          Just ix -> return $ xes !! ix
          Nothing -> panic [ "Could not find field " ++ show fieldNameRepr
                           , show s
                           ]
      _ -> unexpectedValue "get-field operation"
      where
        fieldNameRepr :: SymbolRepr s
        fieldNameRepr = fieldName (extractor undefined)

        structFieldNameReprs :: CT.Struct struct => struct -> [Some SymbolRepr]
        structFieldNameReprs s = valueName <$> CT.toValues s

        mIx :: CT.Struct struct => struct -> Maybe Int
        mIx s = elemIndex (Some fieldNameRepr) (structFieldNameReprs s)

    -- Translate a 'CE.Sign' operation and its argument into a what4
    -- representation of the appropriate type.
    translateSign :: XExpr sym -> IO (XExpr sym)
    translateSign xe = numOp bvSign fpSign xe
      where
        bvSign :: BVOp1 sym w
        bvSign e = do
          zero <- WI.bvLit sym knownRepr (BV.zero knownNat)
          neg_one <- WI.bvLit sym knownNat (BV.mkBV knownNat (-1))
          pos_one <- WI.bvLit sym knownNat (BV.mkBV knownNat 1)
          e_zero <- WI.bvEq sym e zero
          e_neg <- WI.bvSlt sym e zero
          t <- WI.bvIte sym e_neg neg_one pos_one
          WI.bvIte sym e_zero zero t

        fpSign :: forall fi . FPOp1 sym fi
        fpSign fiRepr e = do
          zero <- WFP.iFloatPZero sym fiRepr
          neg_one <- fpLit fiRepr (-1.0)
          pos_one <- fpLit fiRepr   1.0
          e_zero <- WFP.iFloatEq @_ @fi sym e zero
          e_neg <- WFP.iFloatLt @_ @fi sym e zero
          t <- WFP.iFloatIte @_ @fi sym e_neg neg_one pos_one
          WFP.iFloatIte @_ @fi sym e_zero zero t

    -- Check the type of the argument. If the argument is a bitvector value,
    -- apply the 'BVOp1'. If the argument is a floating-point value, apply the
    -- 'FPOp1'. Otherwise, 'panic'.
    numOp :: (forall w . BVOp1 sym w)
          -> (forall fpp . FPOp1 sym fpp)
          -> XExpr sym
          -> IO (XExpr sym)
    numOp bvOp fpOp xe = case xe of
      XInt8 e -> XInt8 <$> bvOp e
      XInt16 e -> XInt16 <$> bvOp e
      XInt32 e -> XInt32 <$> bvOp e
      XInt64 e -> XInt64 <$> bvOp e
      XWord8 e -> XWord8 <$> bvOp e
      XWord16 e -> XWord16 <$> bvOp e
      XWord32 e -> XWord32 <$> bvOp e
      XWord64 e -> XWord64 <$> bvOp e
      XFloat e -> XFloat <$> fpOp WFP.SingleFloatRepr e
      XDouble e -> XDouble <$> fpOp WFP.DoubleFloatRepr e
      _ -> unexpectedValue "numOp"

    bvOp :: (forall w . BVOp1 sym w) -> XExpr sym -> IO (XExpr sym)
    bvOp f xe = case xe of
      XInt8 e -> XInt8 <$> f e
      XInt16 e -> XInt16 <$> f e
      XInt32 e -> XInt32 <$> f e
      XInt64 e -> XInt64 <$> f e
      XWord8 e -> XWord8 <$> f e
      XWord16 e -> XWord16 <$> f e
      XWord32 e -> XWord32 <$> f e
      XWord64 e -> XWord64 <$> f e
      _ -> unexpectedValue "bvOp"

    fpOp :: (forall fi . FPOp1 sym fi) -> XExpr sym -> IO (XExpr sym)
    fpOp g xe = case xe of
      XFloat e -> XFloat <$> g WFP.SingleFloatRepr e
      XDouble e -> XDouble <$> g WFP.DoubleFloatRepr e
      _ -> unexpectedValue "fpOp"

    -- Translate a special-floating operation to the corresponding what4
    -- operation. These operations will be treated as uninterpreted functions in
    -- the solver.
    fpSpecialOp :: WSF.SpecialFunction (EmptyCtx ::> WSF.R)
                -> XExpr sym -> IO (XExpr sym)
    fpSpecialOp fn = fpOp (\fiRepr -> WFP.iFloatSpecialFunction1 sym fiRepr fn)

    -- Construct a floating-point literal value of the appropriate type.
    fpLit :: forall fi.
             WFP.FloatInfoRepr fi
          -> (forall frac. Fractional frac => frac)
          -> IO (WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi))
    fpLit fiRepr fracLit =
      case fiRepr of
        WFP.SingleFloatRepr -> WFP.iFloatLitSingle sym fracLit
        WFP.DoubleFloatRepr -> WFP.iFloatLitDouble sym fracLit
        _ -> panic ["Expected single- or double-precision float", show fiRepr]

    -- A catch-all error message to use when translation cannot proceed.
    unexpectedValue :: forall m x.
                       (Panic.HasCallStack, MonadIO m)
                    => String
                    -> m x
    unexpectedValue op =
      panic [ "Unexpected value in " ++ op ++ ": " ++ show (CP.ppExpr origExpr)
            , show xe
            ]

-- | A binary operation over bitvector values.
type BVOp2 sym w =
     (KnownNat w, 1 <= w)
  => WI.SymBV sym w
  -> WI.SymBV sym w
  -> IO (WI.SymBV sym w)

-- | A binary operation over floating-point values.
type FPOp2 sym fi =
     WFP.FloatInfoRepr fi
  -> WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi)
  -> WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi)
  -> IO (WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi))

-- | A binary predicate that checks if two boolean values are equal.
type BoolCmp2 sym =
     WI.Pred sym
  -> WI.Pred sym
  -> IO (WI.Pred sym)

-- | A binary predicate that checks if two bitvector values are equal.
type BVCmp2 sym w =
     (KnownNat w, 1 <= w)
  => WI.SymBV sym w
  -> WI.SymBV sym w
  -> IO (WI.Pred sym)

-- | A predicate that checks if two floating-point values are equal.
type FPCmp2 sym fi =
     WFP.FloatInfoRepr fi
  -> WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi)
  -> WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi)
  -> IO (WI.Pred sym)

-- | Translate a binary operation and its arguments into a what4 representation
-- of the operation applied to the arguments.
translateOp2 :: forall sym a b c.
                WFP.IsInterpretedFloatExprBuilder sym
             => sym
             -> CE.Expr c
             -- ^ Original value we are translating (only used for error
             -- messages)
             -> CE.Op2 a b c
             -> XExpr sym
             -> XExpr sym
             -> IO (XExpr sym)
translateOp2 sym origExpr op xe1 xe2 = case (op, xe1, xe2) of
  (CE.And, XBool e1, XBool e2) -> XBool <$> WI.andPred sym e1 e2
  (CE.And, _, _) -> unexpectedValues "and operation"
  (CE.Or, XBool e1, XBool e2) -> XBool <$> WI.orPred sym e1 e2
  (CE.Or, _, _) -> unexpectedValues "or operation"
  (CE.Add _, xe1, xe2) ->
    numOp (WI.bvAdd sym)
          (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatAdd @_ @fi sym fpRM)
          xe1
          xe2
  (CE.Sub _, xe1, xe2) ->
    numOp (WI.bvSub sym)
          (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatSub @_ @fi sym fpRM)
          xe1
          xe2
  (CE.Mul _, xe1, xe2) ->
    numOp (WI.bvMul sym)
          (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatMul @_ @fi sym fpRM)
          xe1
          xe2
  (CE.Mod _, xe1, xe2) -> bvOp (WI.bvSrem sym) (WI.bvUrem sym) xe1 xe2
  (CE.Div _, xe1, xe2) -> bvOp (WI.bvSdiv sym) (WI.bvUdiv sym) xe1 xe2
  (CE.Fdiv _, xe1, xe2) ->
    fpOp (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatDiv @_ @fi sym fpRM)
         xe1
         xe2
  (CE.Pow _, xe1, xe2) -> fpSpecialOp WSF.Pow xe1 xe2
  (CE.Logb _, xe1, xe2) -> fpOp logbFn xe1 xe2
    where
      logbFn :: forall fi . FPOp2 sym fi
      -- Implement logb(e1,e2) as log(e2)/log(e1). This matches how copilot-c99
      -- translates Logb to C code.
      logbFn fiRepr e1 e2 = do
        re1 <- WFP.iFloatSpecialFunction1 sym fiRepr WSF.Log e1
        re2 <- WFP.iFloatSpecialFunction1 sym fiRepr WSF.Log e2
        WFP.iFloatDiv @_ @fi sym fpRM re2 re1
  (CE.Atan2 _, xe1, xe2) -> fpSpecialOp WSF.Arctan2 xe1 xe2
  (CE.Eq _, xe1, xe2) ->
    cmp (WI.eqPred sym)
        (WI.bvEq sym)
        (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatEq @_ @fi sym)
        xe1
        xe2
  (CE.Ne _, xe1, xe2) -> translateNe xe1 xe2
  (CE.Le _, xe1, xe2) ->
    numCmp (WI.bvSle sym)
           (WI.bvUle sym)
           (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatLe @_ @fi sym)
           xe1
           xe2
  (CE.Ge _, xe1, xe2) ->
    numCmp (WI.bvSge sym)
           (WI.bvUge sym)
           (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatGe @_ @fi sym)
           xe1
           xe2
  (CE.Lt _, xe1, xe2) ->
    numCmp (WI.bvSlt sym)
           (WI.bvUlt sym)
           (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatLt @_ @fi sym)
           xe1
           xe2
  (CE.Gt _, xe1, xe2) ->
    numCmp (WI.bvSgt sym)
           (WI.bvUgt sym)
           (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatGt @_ @fi sym)
           xe1
           xe2
  (CE.BwAnd _, xe1, xe2) ->
    bvOp (WI.bvAndBits sym) (WI.bvAndBits sym) xe1 xe2
  (CE.BwOr _, xe1, xe2) ->
    bvOp (WI.bvOrBits sym) (WI.bvOrBits sym) xe1 xe2
  (CE.BwXor _, xe1, xe2) ->
    bvOp (WI.bvXorBits sym) (WI.bvXorBits sym) xe1 xe2
  (CE.BwShiftL _ _, xe1, xe2) -> translateBwShiftL xe1 xe2
  (CE.BwShiftR _ _, xe1, xe2) -> translateBwShiftR xe1 xe2
  -- Note: Currently, copilot does not check if array indices are out of bounds,
  -- even for constant expressions. The method of translation we are using
  -- simply creates a nest of if-then-else expression to check the index
  -- expression against all possible indices. If the index expression is known
  -- by the solver to be out of bounds (for instance, if it is a constant 5 for
  -- an array of 5 elements), then the if-then-else will trivially resolve to
  -- true.
  (CE.Index _, xe1, xe2) ->
    case (xe1, xe2) of
      (XArray xes, XWord32 ix) -> buildIndexExpr sym ix xes
      _ -> unexpectedValues "index operation"
  where
    -- Translate an 'CE.Ne' operation and its arguments into a what4
    -- representation of the appropriate type.
    translateNe :: XExpr sym -> XExpr sym -> IO (XExpr sym)
    translateNe xe1 xe2 = cmp neqPred bvNeq fpNeq xe1 xe2
      where
        neqPred :: BoolCmp2 sym
        neqPred e1 e2 = do
          e <- WI.eqPred sym e1 e2
          WI.notPred sym e

        bvNeq :: forall w . BVCmp2 sym w
        bvNeq e1 e2 = do
          e <- WI.bvEq sym e1 e2
          WI.notPred sym e

        fpNeq :: forall fi . FPCmp2 sym fi
        fpNeq _ e1 e2 = do
          e <- WFP.iFloatEq @_ @fi sym e1 e2
          WI.notPred sym e

    -- Translate a 'CE.BwShiftL' operation and its arguments into a what4
    -- representation.
    --
    -- Note: we are interpreting the shifter as an unsigned bitvector regardless
    -- of whether it is a word or an int.
    translateBwShiftL :: XExpr sym -> XExpr sym -> IO (XExpr sym)
    translateBwShiftL xe1 xe2 = do
      -- These partial pattern matches on Just should always succeed because
      -- BwShiftL should always have bitvectors as arguments.
      Just (SomeBVExpr e1 w1 _ ctor1) <- return $ asBVExpr xe1
      Just (SomeBVExpr e2 w2 _ _    ) <- return $ asBVExpr xe2
      e2' <- case testNatCases w1 w2 of
        NatCaseLT LeqProof -> WI.bvTrunc sym w1 e2
        NatCaseEQ -> return e2
        NatCaseGT LeqProof -> WI.bvZext sym w1 e2
      ctor1 <$> WI.bvShl sym e1 e2'

    -- Translate a 'CE.BwShiftL' operation and its arguments into a what4
    -- representation.
    --
    -- Note: we are interpreting the shifter as an unsigned bitvector regardless
    -- of whether it is a word or an int.
    translateBwShiftR :: XExpr sym -> XExpr sym -> IO (XExpr sym)
    translateBwShiftR xe1 xe2 = do
      -- These partial pattern matches on Just should always succeed because
      -- BwShiftL should always have bitvectors as arguments.
      Just (SomeBVExpr e1 w1 sgn1 ctor1) <- return $ asBVExpr xe1
      Just (SomeBVExpr e2 w2 _    _    ) <- return $ asBVExpr xe2
      e2' <- case testNatCases w1 w2 of
        NatCaseLT LeqProof -> WI.bvTrunc sym w1 e2
        NatCaseEQ -> return e2
        NatCaseGT LeqProof -> WI.bvZext sym w1 e2
      ctor1 <$> case sgn1 of
        Signed -> WI.bvAshr sym e1 e2'
        Unsigned -> WI.bvLshr sym e1 e2'

    -- Check the types of the arguments. If the arguments are bitvector values,
    -- apply the 'BVOp2'. If the arguments are floating-point values, apply the
    -- 'FPOp2'. Otherwise, 'panic'.
    numOp :: (forall w . BVOp2 sym w)
          -> (forall fi . FPOp2 sym fi)
          -> XExpr sym
          -> XExpr sym
          -> IO (XExpr sym)
    numOp bvOp fpOp xe1 xe2 = case (xe1, xe2) of
      (XInt8 e1, XInt8 e2) -> XInt8 <$> bvOp e1 e2
      (XInt16 e1, XInt16 e2) -> XInt16 <$> bvOp e1 e2
      (XInt32 e1, XInt32 e2) -> XInt32 <$> bvOp e1 e2
      (XInt64 e1, XInt64 e2) -> XInt64 <$> bvOp e1 e2
      (XWord8 e1, XWord8 e2) -> XWord8 <$> bvOp e1 e2
      (XWord16 e1, XWord16 e2) -> XWord16 <$> bvOp e1 e2
      (XWord32 e1, XWord32 e2) -> XWord32 <$> bvOp e1 e2
      (XWord64 e1, XWord64 e2) -> XWord64 <$> bvOp e1 e2
      (XFloat e1, XFloat e2) -> XFloat <$> fpOp WFP.SingleFloatRepr e1 e2
      (XDouble e1, XDouble e2) -> XDouble <$> fpOp WFP.DoubleFloatRepr e1 e2
      _ -> unexpectedValues "numOp"

    -- Check the types of the arguments. If the arguments are signed bitvector
    -- values, apply the first 'BVOp2'. If the arguments are unsigned bitvector
    -- values, apply the second 'BVOp2'. Otherwise, 'panic'.
    bvOp :: (forall w . BVOp2 sym w)
         -> (forall w . BVOp2 sym w)
         -> XExpr sym
         -> XExpr sym
         -> IO (XExpr sym)
    bvOp opS opU xe1 xe2 = case (xe1, xe2) of
      (XInt8 e1, XInt8 e2) -> XInt8 <$> opS e1 e2
      (XInt16 e1, XInt16 e2) -> XInt16 <$> opS e1 e2
      (XInt32 e1, XInt32 e2) -> XInt32 <$> opS e1 e2
      (XInt64 e1, XInt64 e2) -> XInt64 <$> opS e1 e2
      (XWord8 e1, XWord8 e2) -> XWord8 <$> opU e1 e2
      (XWord16 e1, XWord16 e2) -> XWord16 <$> opU e1 e2
      (XWord32 e1, XWord32 e2) -> XWord32 <$> opU e1 e2
      (XWord64 e1, XWord64 e2) -> XWord64 <$> opU e1 e2
      _ -> unexpectedValues "bvOp"

    fpOp :: (forall fi . FPOp2 sym fi)
         -> XExpr sym
         -> XExpr sym
         -> IO (XExpr sym)
    fpOp op xe1 xe2 = case (xe1, xe2) of
      (XFloat e1, XFloat e2) -> XFloat <$> op WFP.SingleFloatRepr e1 e2
      (XDouble e1, XDouble e2) -> XDouble <$> op WFP.DoubleFloatRepr e1 e2
      _ -> unexpectedValues "fpOp"

    -- Translate a special-floating operation to the corresponding what4
    -- operation. These operations will be treated as uninterpreted functions in
    -- the solver.
    fpSpecialOp :: WSF.SpecialFunction (EmptyCtx ::> WSF.R ::> WSF.R)
                -> XExpr sym -> XExpr sym -> IO (XExpr sym)
    fpSpecialOp fn = fpOp (\fiRepr -> WFP.iFloatSpecialFunction2 sym fiRepr fn)

    -- Check the types of the arguments. If the arguments are bitvector values,
    -- apply the 'BVCmp2'. If the arguments are floating-point values, apply the
    -- 'FPCmp2'. Otherwise, 'panic'.
    cmp :: BoolCmp2 sym
        -> (forall w . BVCmp2 sym w)
        -> (forall fi . FPCmp2 sym fi)
        -> XExpr sym
        -> XExpr sym
        -> IO (XExpr sym)
    cmp boolOp bvOp fpOp xe1 xe2 = case (xe1, xe2) of
      (XBool e1, XBool e2) -> XBool <$> boolOp e1 e2
      (XInt8 e1, XInt8 e2) -> XBool <$> bvOp e1 e2
      (XInt16 e1, XInt16 e2) -> XBool <$> bvOp e1 e2
      (XInt32 e1, XInt32 e2) -> XBool <$> bvOp e1 e2
      (XInt64 e1, XInt64 e2) -> XBool <$> bvOp e1 e2
      (XWord8 e1, XWord8 e2) -> XBool <$> bvOp e1 e2
      (XWord16 e1, XWord16 e2) -> XBool <$> bvOp e1 e2
      (XWord32 e1, XWord32 e2) -> XBool <$> bvOp e1 e2
      (XWord64 e1, XWord64 e2) -> XBool <$> bvOp e1 e2
      (XFloat e1, XFloat e2) -> XBool <$> fpOp WFP.SingleFloatRepr e1 e2
      (XDouble e1, XDouble e2) -> XBool <$> fpOp WFP.DoubleFloatRepr e1 e2
      _ -> unexpectedValues "cmp"

    -- Check the types of the arguments. If the arguments are signed bitvector
    -- values, apply the first 'BVCmp2'. If the arguments are unsigned bitvector
    -- values, apply the second 'BVCmp2'. If the arguments are floating-point
    -- values, apply the 'FPCmp2'. Otherwise, 'panic'.
    numCmp :: (forall w . BVCmp2 sym w)
           -> (forall w . BVCmp2 sym w)
           -> (forall fi . FPCmp2 sym fi)
           -> XExpr sym
           -> XExpr sym
           -> IO (XExpr sym)
    numCmp bvSOp bvUOp fpOp xe1 xe2 = case (xe1, xe2) of
      (XInt8 e1, XInt8 e2) -> XBool <$> bvSOp e1 e2
      (XInt16 e1, XInt16 e2) -> XBool <$> bvSOp e1 e2
      (XInt32 e1, XInt32 e2) -> XBool <$> bvSOp e1 e2
      (XInt64 e1, XInt64 e2) -> XBool <$> bvSOp e1 e2
      (XWord8 e1, XWord8 e2) -> XBool <$> bvUOp e1 e2
      (XWord16 e1, XWord16 e2) -> XBool <$> bvUOp e1 e2
      (XWord32 e1, XWord32 e2) -> XBool <$> bvUOp e1 e2
      (XWord64 e1, XWord64 e2) -> XBool <$> bvUOp e1 e2
      (XFloat e1, XFloat e2) -> XBool <$> fpOp WFP.SingleFloatRepr e1 e2
      (XDouble e1, XDouble e2) -> XBool <$> fpOp WFP.DoubleFloatRepr e1 e2
      _ -> unexpectedValues "numCmp"

    -- A catch-all error message to use when translation cannot proceed.
    unexpectedValues :: forall m x.
                        (Panic.HasCallStack, MonadIO m)
                     => String
                     -> m x
    unexpectedValues op =
      panic [ "Unexpected values in " ++ op ++ ": " ++ show (CP.ppExpr origExpr)
            , show xe1, show xe2
            ]

-- | Translate a ternary operation and its arguments into a what4 representation
-- of the operation applied to the arguments.
translateOp3 :: forall sym a b c d.
                WFP.IsInterpretedFloatExprBuilder sym
             => sym
             -> CE.Expr d
             -- ^ Original value we are translating (only used for error
             -- messages)
             -> CE.Op3 a b c d
             -> XExpr sym
             -> XExpr sym
             -> XExpr sym
             -> IO (XExpr sym)
translateOp3 sym origExpr op xe1 xe2 xe3 = case (op, xe1, xe2, xe3) of
  (CE.Mux _, XBool te, xe1, xe2) -> liftIO $ mkIte sym te xe1 xe2
  (CE.Mux _, _, _, _) -> unexpectedValues "mux operation"
  where
    unexpectedValues :: forall m x. (Panic.HasCallStack, MonadIO m) =>
                        String -> m x
    unexpectedValues op =
      panic [ "Unexpected values in " ++ op ++ ":"
            , show (CP.ppExpr origExpr), show xe1, show xe2, show xe3
            ]

-- | Construct an expression that indexes into an array by building a chain of
-- @if@ expressions, where each expression checks if the current index is equal
-- to a given index in the array. If the indices are equal, return the element
-- of the array at that index. Otherwise, proceed to the next @if@ expression,
-- which checks the next index in the array.
buildIndexExpr :: forall sym n.
                  (1 <= n, WFP.IsInterpretedFloatExprBuilder sym)
               => sym
               -> WI.SymBV sym 32
               -- ^ Index
               -> V.Vector n (XExpr sym)
               -- ^ Elements
               -> IO (XExpr sym)
buildIndexExpr sym ix = loop 0
  where
    loop :: forall n'.
            (1 <= n')
         => Word32
         -> V.Vector n' (XExpr sym)
         -> IO (XExpr sym)
    loop curIx xelts = case V.uncons xelts of
      -- Base case, exactly one element left
      (xe, Left Refl) -> return xe
      -- Recursive case
      (xe, Right xelts') -> do
        LeqProof <- return $ V.nonEmpty xelts'
        rstExpr <- loop (curIx+1) xelts'
        curIxExpr <- WI.bvLit sym knownNat (BV.word32 curIx)
        ixEq <- WI.bvEq sym curIxExpr ix
        mkIte sym ixEq xe rstExpr

-- | Construct an @if@ expression of the appropriate type.
mkIte :: WFP.IsInterpretedFloatExprBuilder sym
      => sym
      -> WI.Pred sym
      -> XExpr sym
      -> XExpr sym
      -> IO (XExpr sym)
mkIte sym pred xe1 xe2 = case (xe1, xe2) of
  (XBool e1, XBool e2) -> XBool <$> WI.itePred sym pred e1 e2
  (XInt8 e1, XInt8 e2) -> XInt8 <$> WI.bvIte sym pred e1 e2
  (XInt16 e1, XInt16 e2) -> XInt16 <$> WI.bvIte sym pred e1 e2
  (XInt32 e1, XInt32 e2) -> XInt32 <$> WI.bvIte sym pred e1 e2
  (XInt64 e1, XInt64 e2) -> XInt64 <$> WI.bvIte sym pred e1 e2
  (XWord8 e1, XWord8 e2) -> XWord8 <$> WI.bvIte sym pred e1 e2
  (XWord16 e1, XWord16 e2) -> XWord16 <$> WI.bvIte sym pred e1 e2
  (XWord32 e1, XWord32 e2) -> XWord32 <$> WI.bvIte sym pred e1 e2
  (XWord64 e1, XWord64 e2) -> XWord64 <$> WI.bvIte sym pred e1 e2
  (XFloat e1, XFloat e2) ->
    XFloat <$> WFP.iFloatIte @_ @WFP.SingleFloat sym pred e1 e2
  (XDouble e1, XDouble e2) ->
    XDouble <$> WFP.iFloatIte @_ @WFP.DoubleFloat sym pred e1 e2
  (XStruct xes1, XStruct xes2) ->
    XStruct <$> zipWithM (mkIte sym pred) xes1 xes2
  (XEmptyArray, XEmptyArray) -> return XEmptyArray
  (XArray xes1, XArray xes2) ->
    case V.length xes1 `testEquality` V.length xes2 of
      Just Refl -> XArray <$> V.zipWithM (mkIte sym pred) xes1 xes2
      Nothing -> panic [ "Array length mismatch in ite"
                       , show (V.length xes1)
                       , show (V.length xes2)
                       ]
  _ -> panic ["Unexpected values in ite", show xe1, show xe2]

-- | Cast an 'XExpr' to another 'XExpr' of a possibly differing type.
castOp :: WFP.IsInterpretedFloatExprBuilder sym
       => sym
       -> CE.Expr b
       -- ^ Original value we are translating (only used for error
       -- messages)
       -> CT.Type a
       -- ^ Type we are casting to
       -> XExpr sym
       -- ^ Value to cast
       -> IO (XExpr sym)
castOp sym origExpr tp xe = case (xe, tp) of
  -- "safe" casts that cannot lose information
  (XBool _, CT.Bool)     -> return xe
  (XBool e, CT.Word8)    -> XWord8  <$> WI.predToBV sym e knownNat
  (XBool e, CT.Word16)   -> XWord16 <$> WI.predToBV sym e knownNat
  (XBool e, CT.Word32)   -> XWord32 <$> WI.predToBV sym e knownNat
  (XBool e, CT.Word64)   -> XWord64 <$> WI.predToBV sym e knownNat
  (XBool e, CT.Int8)     -> XInt8   <$> WI.predToBV sym e knownNat
  (XBool e, CT.Int16)    -> XInt16  <$> WI.predToBV sym e knownNat
  (XBool e, CT.Int32)    -> XInt32  <$> WI.predToBV sym e knownNat
  (XBool e, CT.Int64)    -> XInt64  <$> WI.predToBV sym e knownNat

  (XInt8 _, CT.Int8)     -> return xe
  (XInt8 e, CT.Int16)    -> XInt16  <$> WI.bvSext sym knownNat e
  (XInt8 e, CT.Int32)    -> XInt32  <$> WI.bvSext sym knownNat e
  (XInt8 e, CT.Int64)    -> XInt64  <$> WI.bvSext sym knownNat e
  (XInt16 _, CT.Int16)   -> return xe
  (XInt16 e, CT.Int32)   -> XInt32  <$> WI.bvSext sym knownNat e
  (XInt16 e, CT.Int64)   -> XInt64  <$> WI.bvSext sym knownNat e
  (XInt32 _, CT.Int32)   -> return xe
  (XInt32 e, CT.Int64)   -> XInt64  <$> WI.bvSext sym knownNat e
  (XInt64 _, CT.Int64)   -> return xe

  (XWord8 e, CT.Int16)   -> XInt16  <$> WI.bvZext sym knownNat e
  (XWord8 e, CT.Int32)   -> XInt32  <$> WI.bvZext sym knownNat e
  (XWord8 e, CT.Int64)   -> XInt64  <$> WI.bvZext sym knownNat e
  (XWord8 _, CT.Word8)   -> return xe
  (XWord8 e, CT.Word16)  -> XWord16 <$> WI.bvZext sym knownNat e
  (XWord8 e, CT.Word32)  -> XWord32 <$> WI.bvZext sym knownNat e
  (XWord8 e, CT.Word64)  -> XWord64 <$> WI.bvZext sym knownNat e
  (XWord16 e, CT.Int32)  -> XInt32  <$> WI.bvZext sym knownNat e
  (XWord16 e, CT.Int64)  -> XInt64  <$> WI.bvZext sym knownNat e
  (XWord16 _, CT.Word16) -> return xe
  (XWord16 e, CT.Word32) -> XWord32 <$> WI.bvZext sym knownNat e
  (XWord16 e, CT.Word64) -> XWord64 <$> WI.bvZext sym knownNat e
  (XWord32 e, CT.Int64)  -> XInt64  <$> WI.bvZext sym knownNat e
  (XWord32 _, CT.Word32) -> return xe
  (XWord32 e, CT.Word64) -> XWord64 <$> WI.bvZext sym knownNat e
  (XWord64 _, CT.Word64) -> return xe

  -- "unsafe" casts, which may lose information
  -- unsigned truncations
  (XWord64 e, CT.Word32) -> XWord32 <$> WI.bvTrunc sym knownNat e
  (XWord64 e, CT.Word16) -> XWord16 <$> WI.bvTrunc sym knownNat e
  (XWord64 e, CT.Word8)  -> XWord8  <$> WI.bvTrunc sym knownNat e
  (XWord32 e, CT.Word16) -> XWord16 <$> WI.bvTrunc sym knownNat e
  (XWord32 e, CT.Word8)  -> XWord8  <$> WI.bvTrunc sym knownNat e
  (XWord16 e, CT.Word8)  -> XWord8  <$> WI.bvTrunc sym knownNat e

  -- signed truncations
  (XInt64 e, CT.Int32)   -> XInt32  <$> WI.bvTrunc sym knownNat e
  (XInt64 e, CT.Int16)   -> XInt16  <$> WI.bvTrunc sym knownNat e
  (XInt64 e, CT.Int8)    -> XInt8   <$> WI.bvTrunc sym knownNat e
  (XInt32 e, CT.Int16)   -> XInt16  <$> WI.bvTrunc sym knownNat e
  (XInt32 e, CT.Int8)    -> XInt8   <$> WI.bvTrunc sym knownNat e
  (XInt16 e, CT.Int8)    -> XInt8   <$> WI.bvTrunc sym knownNat e

  -- signed integer to float
  (XInt64 e, CT.Float)   ->
    XFloat <$> WFP.iSBVToFloat sym WFP.SingleFloatRepr fpRM e
  (XInt32 e, CT.Float)   ->
    XFloat <$> WFP.iSBVToFloat sym WFP.SingleFloatRepr fpRM e
  (XInt16 e, CT.Float)   ->
    XFloat <$> WFP.iSBVToFloat sym WFP.SingleFloatRepr fpRM e
  (XInt8 e, CT.Float)    ->
    XFloat <$> WFP.iSBVToFloat sym WFP.SingleFloatRepr fpRM e

  -- unsigned integer to float
  (XWord64 e, CT.Float)  ->
    XFloat <$> WFP.iBVToFloat sym WFP.SingleFloatRepr fpRM e
  (XWord32 e, CT.Float)  ->
    XFloat <$> WFP.iBVToFloat sym WFP.SingleFloatRepr fpRM e
  (XWord16 e, CT.Float)  ->
    XFloat <$> WFP.iBVToFloat sym WFP.SingleFloatRepr fpRM e
  (XWord8 e, CT.Float)   ->
    XFloat <$> WFP.iBVToFloat sym WFP.SingleFloatRepr fpRM e

  -- signed integer to double
  (XInt64 e, CT.Double)  ->
    XDouble <$> WFP.iSBVToFloat sym WFP.DoubleFloatRepr fpRM e
  (XInt32 e, CT.Double)  ->
    XDouble <$> WFP.iSBVToFloat sym WFP.DoubleFloatRepr fpRM e
  (XInt16 e, CT.Double)  ->
    XDouble <$> WFP.iSBVToFloat sym WFP.DoubleFloatRepr fpRM e
  (XInt8 e, CT.Double)   ->
    XDouble <$> WFP.iSBVToFloat sym WFP.DoubleFloatRepr fpRM e

  -- unsigned integer to double
  (XWord64 e, CT.Double) ->
    XDouble <$> WFP.iBVToFloat sym WFP.DoubleFloatRepr fpRM e
  (XWord32 e, CT.Double) ->
    XDouble <$> WFP.iBVToFloat sym WFP.DoubleFloatRepr fpRM e
  (XWord16 e, CT.Double) ->
    XDouble <$> WFP.iBVToFloat sym WFP.DoubleFloatRepr fpRM e
  (XWord8 e, CT.Double)  ->
    XDouble <$> WFP.iBVToFloat sym WFP.DoubleFloatRepr fpRM e

  -- unsigned to signed conversion
  (XWord64 e, CT.Int64)  -> return $ XInt64 e
  (XWord32 e, CT.Int32)  -> return $ XInt32 e
  (XWord16 e, CT.Int16)  -> return $ XInt16 e
  (XWord8 e,  CT.Int8)   -> return $ XInt8 e

  -- signed to unsigned conversion
  (XInt64 e, CT.Word64)  -> return $ XWord64 e
  (XInt32 e, CT.Word32)  -> return $ XWord32 e
  (XInt16 e, CT.Word16)  -> return $ XWord16 e
  (XInt8 e, CT.Word8)    -> return $ XWord8 e

  _ -> panic ["Could not compute cast", show (CP.ppExpr origExpr), show xe]

-- What4 representations of Copilot expressions

-- | The What4 representation of a copilot expression. We do not attempt to
-- track the type of the inner expression at the type level, but instead lump
-- everything together into the @XExpr sym@ type. The only reason this is a GADT
-- is for the array case; we need to know that the array length is strictly
-- positive.
data XExpr sym where
  XBool       :: WI.SymExpr sym WT.BaseBoolType -> XExpr sym
  XInt8       :: WI.SymExpr sym (WT.BaseBVType 8) -> XExpr sym
  XInt16      :: WI.SymExpr sym (WT.BaseBVType 16) -> XExpr sym
  XInt32      :: WI.SymExpr sym (WT.BaseBVType 32) -> XExpr sym
  XInt64      :: WI.SymExpr sym (WT.BaseBVType 64) -> XExpr sym
  XWord8      :: WI.SymExpr sym (WT.BaseBVType 8) -> XExpr sym
  XWord16     :: WI.SymExpr sym (WT.BaseBVType 16) -> XExpr sym
  XWord32     :: WI.SymExpr sym (WT.BaseBVType 32) -> XExpr sym
  XWord64     :: WI.SymExpr sym (WT.BaseBVType 64) -> XExpr sym
  XFloat      :: WI.SymExpr
                   sym
                   (WFP.SymInterpretedFloatType sym WFP.SingleFloat)
              -> XExpr sym
  XDouble     :: WI.SymExpr
                   sym
                   (WFP.SymInterpretedFloatType sym WFP.DoubleFloat)
              -> XExpr sym
  XEmptyArray :: XExpr sym
  XArray      :: 1 <= n => V.Vector n (XExpr sym) -> XExpr sym
  XStruct     :: [XExpr sym] -> XExpr sym

instance WI.IsExprBuilder sym => Show (XExpr sym) where
  show (XBool e)    = "XBool " ++ show (WI.printSymExpr e)
  show (XInt8 e)    = "XInt8 " ++ show (WI.printSymExpr e)
  show (XInt16 e)   = "XInt16 " ++ show (WI.printSymExpr e)
  show (XInt32 e)   = "XInt32 " ++ show (WI.printSymExpr e)
  show (XInt64 e)   = "XInt64 " ++ show (WI.printSymExpr e)
  show (XWord8 e)   = "XWord8 " ++ show (WI.printSymExpr e)
  show (XWord16 e)  = "XWord16 " ++ show (WI.printSymExpr e)
  show (XWord32 e)  = "XWord32 " ++ show (WI.printSymExpr e)
  show (XWord64 e)  = "XWord64 " ++ show (WI.printSymExpr e)
  show (XFloat e)   = "XFloat " ++ show (WI.printSymExpr e)
  show (XDouble e)  = "XDouble " ++ show (WI.printSymExpr e)
  show XEmptyArray  = "[]"
  show (XArray vs)  = showList (V.toList vs) ""
  show (XStruct xs) = "XStruct " ++ showList xs ""

-- Auxiliary definitions

-- | We assume round-near-even throughout, but this variable can be changed if
-- needed.
fpRM :: WI.RoundingMode
fpRM = WI.RNE

-- | Indicates to the 'Panic.panic' function that a panic is
-- Copilot/What4-related.
data CopilotWhat4 = CopilotWhat4

instance Panic.PanicComponent CopilotWhat4 where
  panicComponentName _ = "Copilot/What4 translation"
  panicComponentIssues _ = "https://github.com/Copilot-Language/copilot/issues"

  {-# NOINLINE Panic.panicComponentRevision #-}
  panicComponentRevision = $(Panic.useGitRevision)

-- | Use this function rather than an error monad since it indicates that
-- something in the implementation of @copilot-theorem@ is incorrect.
panic :: (Panic.HasCallStack, MonadIO m) => [String] -> m a
panic msg = Panic.panic CopilotWhat4 "Copilot.Theorem.What4" msg
