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
  , TransM(..)
  , translateExpr
  , translateExprAt
    -- * What4 representations of Copilot expressions
  , XExpr(..)
  ) where

import           Control.Monad                 (forM, zipWithM, (<=<))
import qualified Control.Monad.Fail            as Fail
import           Control.Monad.IO.Class        (MonadIO (..))
import           Control.Monad.State           (MonadState (..), StateT (..),
                                                gets, modify)
import qualified Data.BitVector.Sized          as BV
import           Data.List                     (elemIndex)
import qualified Data.Map                      as Map
import           Data.Maybe                    (fromJust)
import           Data.Parameterized.Classes    (KnownRepr (..))
import           Data.Parameterized.Context    (EmptyCtx, pattern (:>),
                                                pattern Empty, type (::>))
import           Data.Parameterized.NatRepr    (LeqProof (..), NatCases (..),
                                                NatRepr, decNat, isZeroOrGT1,
                                                knownNat, minusPlusCancel,
                                                someNat, testNatCases)
import           Data.Parameterized.Some       (Some (..))
import           Data.Parameterized.SymbolRepr (SymbolRepr, knownSymbol)
import qualified Data.Parameterized.Vector     as V
import           Data.Type.Equality            (TestEquality (..), (:~:) (..))
import           Data.Word                     (Word32)
import           GHC.TypeLits                  (KnownSymbol)
import           GHC.TypeNats                  (KnownNat, type (<=))
import           LibBF                         (bfFromDouble, bfPosZero)
import qualified Panic                         as Panic

import qualified What4.BaseTypes               as WT
import qualified What4.Expr.Builder            as WB
import qualified What4.Interface               as WI

import qualified Copilot.Core.Expr             as CE
import qualified Copilot.Core.Operators        as CE
import qualified Copilot.Core.Spec             as CS
import qualified Copilot.Core.Type             as CT
import qualified Copilot.Core.Type.Array       as CT

-- What4 translation

-- | the state for translating Copilot expressions into What4 expressions. As we
-- translate, we generate fresh symbolic constants for external variables and
-- for stream variables. We need to only generate one constant per variable, so
-- we allocate them in a map. When we need the constant for a particular
-- variable, we check if it is already in the map, and return it if it is; if it
-- isn't, we generate a fresh constant at that point, store it in the map, and
-- return it.
--
-- We also store three immutable fields in this state, rather than wrap them up
-- in another monad transformer layer. These are initialized prior to
-- translation and are never modified. They are the map from stream ids to the
-- core stream definitions, a symbolic uninterpreted function for "pow", and a
-- symbolic uninterpreted function for "logb".
data TransState t = TransState {
  -- | Map of all external variables we encounter during translation. These are
  -- just fresh constants. The offset indicates how many timesteps in the past
  -- this constant represents for that stream.
  externVars :: Map.Map (CE.Name, Int) (XExpr t),
  -- | Map of external variables at specific indices (positive), rather than
  -- offset into the past. This is for interpreting streams at specific offsets.
  externVarsAt :: Map.Map (CE.Name, Int) (XExpr t),
  -- | Map from (stream id, negative offset) to fresh constant. These are all
  -- constants representing the values of a stream at some point in the past.
  -- The offset (ALWAYS NEGATIVE) indicates how many timesteps in the past
  -- this constant represents for that stream.
  streamConstants :: Map.Map (CE.Id, Int) (XExpr t),
  -- | Map from stream ids to the streams themselves. This value is never
  -- modified, but I didn't want to make this an RWS, so it's represented as a
  -- stateful value.
  streams :: Map.Map CE.Id CS.Stream,
  -- | Binary power operator, represented as an uninterpreted function.
  pow :: WB.ExprSymFn t
         (EmptyCtx ::> WT.BaseRealType ::> WT.BaseRealType)
         WT.BaseRealType,
  -- | Binary logarithm operator, represented as an uninterpreted function.
  logb :: WB.ExprSymFn t
          (EmptyCtx ::> WT.BaseRealType ::> WT.BaseRealType)
          WT.BaseRealType
  }

newtype TransM t a = TransM { unTransM :: StateT (TransState t) IO a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadIO
           , MonadState (TransState t)
           )

instance Fail.MonadFail (TransM t) where
  fail = error

-- | Translate an expression into a what4 representation. The int offset keeps
-- track of how many timesteps into the past each variable is referring to.
-- Initially the value should be zero, but when we translate a stream, the
-- offset is recomputed based on the length of that stream's prefix (subtracted)
-- and the drop index (added).
translateExpr :: WB.ExprBuilder t st fs
              -> Int
              -- ^ number of timesteps in the past we are currently looking
              -- (must always be <= 0)
              -> CE.Expr a
              -> TransM t (XExpr t)
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
  CE.Op1 op e -> liftIO . translateOp1 sym op =<< translateExpr sym offset e
  CE.Op2 op e1 e2 -> do
    xe1 <- translateExpr sym offset e1
    xe2 <- translateExpr sym offset e2
    powFn <- gets pow
    logbFn <- gets logb
    liftIO $ translateOp2 sym powFn logbFn op xe1 xe2
  CE.Op3 op e1 e2 e3 -> do
    xe1 <- translateExpr sym offset e1
    xe2 <- translateExpr sym offset e2
    xe3 <- translateExpr sym offset e3
    liftIO $ translateOp3 sym op xe1 xe2 xe3
  CE.Label _ _ _ -> error "translateExpr: Label unimplemented"

-- | Translate an expression into a what4 representation at a /specific/
-- timestep, rather than "at some indeterminate point in the future."
translateExprAt :: WB.ExprBuilder t st fs
                -> Int
                -- ^ Index of timestep
                -> CE.Expr a
                -- ^ stream expression
                -> TransM t (XExpr t)
translateExprAt sym k e = do
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
    CE.Op1 op e -> liftIO . translateOp1 sym op =<< translateExprAt sym k e
    CE.Op2 op e1 e2 -> do
      xe1 <- translateExprAt sym k e1
      xe2 <- translateExprAt sym k e2
      powFn <- gets pow
      logbFn <- gets logb
      liftIO $ translateOp2 sym powFn logbFn op xe1 xe2
    CE.Op3 op e1 e2 e3 -> do
      xe1 <- translateExprAt sym k e1
      xe2 <- translateExprAt sym k e2
      xe3 <- translateExprAt sym k e3
      liftIO $ translateOp3 sym op xe1 xe2 xe3
    CE.Label _ _ _ -> error "translateExpr: Label unimplemented"

-- | A view of an XExpr as a bitvector expression, a natrepr for its width, its
-- signed/unsigned status, and the constructor used to reconstruct an XExpr from
-- it. This is a useful view for translation, as many of the operations can be
-- grouped together for all words\/ints\/floats.
data SomeBVExpr t where
  SomeBVExpr :: 1 <= w
             => WB.BVExpr t w
             -> NatRepr w
             -> BVSign
             -> (WB.BVExpr t w -> XExpr t)
             -> SomeBVExpr t

-- | The sign of a bitvector -- this indicates whether it is to be interpreted
-- as a signed 'Int' or an unsigned 'Word'.
data BVSign = Signed | Unsigned

-- | If the inner expression can be viewed as a bitvector, we project out a view
-- of it as such.
asBVExpr :: XExpr t -> Maybe (SomeBVExpr t)
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
translateConstExpr :: forall a t st fs .
                      WB.ExprBuilder t st fs
                   -> CT.Type a
                   -> a
                   -> IO (XExpr t)
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
  CT.Float -> XFloat <$> WI.floatLit sym knownRepr (bfFromDouble (realToFrac a))
  CT.Double -> XDouble <$> WI.floatLit sym knownRepr (bfFromDouble a)
  CT.Array tp -> do
    elts <- traverse (translateConstExpr sym tp) (CT.arrayelems a)
    Just (Some n) <- return $ someNat (length elts)
    case isZeroOrGT1 n of
      Left Refl -> return XEmptyArray
      Right LeqProof -> do
        let Just v = V.fromList n elts
        return $ XArray v
  CT.Struct _ -> do
    elts <- forM (CT.toValues a) $ \(CT.Value tp (CT.Field a)) ->
      translateConstExpr sym tp a
    return $ XStruct elts

arrayLen :: KnownNat n => CT.Type (CT.Array n t) -> NatRepr n
arrayLen _ = knownNat

-- | Generate a fresh constant for a given copilot type. This will be called
-- whenever we attempt to get the constant for a given external variable or
-- stream variable, but that variable has not been accessed yet and therefore
-- has no constant allocated.
freshCPConstant :: forall t st fs a .
                   WB.ExprBuilder t st fs
                -> String
                -> CT.Type a
                -> IO (XExpr t)
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
  CT.Float -> XFloat <$> WI.freshConstant sym (WI.safeSymbol nm) knownRepr
  CT.Double -> XDouble <$> WI.freshConstant sym (WI.safeSymbol nm) knownRepr
  atp@(CT.Array itp) -> do
    n <- return $ arrayLen atp
    case isZeroOrGT1 n of
      Left Refl -> return XEmptyArray
      Right LeqProof -> do
        Refl <- return $ minusPlusCancel n (knownNat @1)
        elts :: V.Vector n (XExpr t) <- V.generateM (decNat n) (const (freshCPConstant sym "" itp))
        return $ XArray elts
  CT.Struct stp -> do
    elts <- forM (CT.toValues stp) $ \(CT.Value ftp _) -> freshCPConstant sym "" ftp
    return $ XStruct elts

-- | Get the constant for a given stream id and some offset into the past. This
-- should only be called with a strictly negative offset. When this function
-- gets called for the first time for a given (streamId, offset) pair, it
-- generates a fresh constant and stores it in an internal map. Thereafter, this
-- function will just return that constant when called with the same pair.
getStreamConstant :: WB.ExprBuilder t st fs -> CE.Id -> Int -> TransM t (XExpr t)
getStreamConstant sym streamId offset = do
  scs <- gets streamConstants
  case Map.lookup (streamId, offset) scs of
    Just xe -> return xe
    Nothing -> do
      CS.Stream _ _ _ tp <- getStreamDef streamId
      let nm = show streamId ++ "_" ++ show offset
      xe <- liftIO $ freshCPConstant sym nm tp
      modify (\st -> st { streamConstants = Map.insert (streamId, offset) xe scs })
      return xe

-- | Get the constant for a given external variable and some offset into the
-- past. This should only be called with a strictly negative offset. When this
-- function gets called for the first time for a given (var, offset) pair, it
-- generates a fresh constant and stores it in an internal map. Thereafter, this
-- function will just return that constant when called with the same pair.
getExternConstant :: WB.ExprBuilder t st fs
                  -> CT.Type a
                  -> CE.Name
                  -> Int
                  -> TransM t (XExpr t)
getExternConstant sym tp var offset = do
  es <- gets externVars
  case Map.lookup (var, offset) es of
    Just xe -> return xe
    Nothing -> do
      xe <- liftIO $ freshCPConstant sym var tp
      modify (\st -> st { externVars = Map.insert (var, offset) xe es} )
      return xe

-- | Get the constant for a given external variable at some specific timestep.
getExternConstantAt :: WB.ExprBuilder t st fs
                    -> CT.Type a
                    -> CE.Name
                    -> Int
                    -> TransM t (XExpr t)
getExternConstantAt sym tp var ix = do
  es <- gets externVarsAt
  case Map.lookup (var, ix) es of
    Just xe -> return xe
    Nothing -> do
      xe <- liftIO $ freshCPConstant sym var tp
      modify (\st -> st { externVarsAt = Map.insert (var, ix) xe es} )
      return xe

-- | Retrieve a stream definition given its id.
getStreamDef :: CE.Id -> TransM t CS.Stream
getStreamDef streamId = fromJust <$> gets (Map.lookup streamId . streams)

type BVOp1 w t = (KnownNat w, 1 <= w) => WB.BVExpr t w -> IO (WB.BVExpr t w)

type FPOp1 fpp t = KnownRepr WT.FloatPrecisionRepr fpp => WB.Expr t (WT.BaseFloatType fpp) -> IO (WB.Expr t (WT.BaseFloatType fpp))

type RealOp1 t = WB.Expr t WT.BaseRealType -> IO (WB.Expr t WT.BaseRealType)

fieldName :: KnownSymbol s => CT.Field s a -> SymbolRepr s
fieldName _ = knownSymbol

valueName :: CT.Value a -> Some SymbolRepr
valueName (CT.Value _ f) = Some (fieldName f)

translateOp1 :: forall t st fs a b .
                WB.ExprBuilder t st fs
             -> CE.Op1 a b
             -> XExpr t
             -> IO (XExpr t)
translateOp1 sym op xe = case (op, xe) of
  (CE.Not, XBool e) -> XBool <$> WI.notPred sym e
  (CE.Not, _) -> panic
  (CE.Abs _, xe) -> numOp bvAbs fpAbs xe
    where
      bvAbs :: BVOp1 w t
      bvAbs e = do zero <- WI.bvLit sym knownNat (BV.zero knownNat)
                   e_neg <- WI.bvSlt sym e zero
                   neg_e <- WI.bvSub sym zero e
                   WI.bvIte sym e_neg neg_e e
      fpAbs :: FPOp1 fpp t
      fpAbs e = do zero <- WI.floatLit sym knownRepr bfPosZero
                   e_neg <- WI.floatLt sym e zero
                   neg_e <- WI.floatSub sym fpRM zero e
                   WI.floatIte sym e_neg neg_e e
  (CE.Sign _, xe) -> numOp bvSign fpSign xe
    where
      bvSign :: BVOp1 w t
      bvSign e = do zero <- WI.bvLit sym knownRepr (BV.zero knownNat)
                    neg_one <- WI.bvLit sym knownNat (BV.mkBV knownNat (-1))
                    pos_one <- WI.bvLit sym knownNat (BV.mkBV knownNat 1)
                    e_zero <- WI.bvEq sym e zero
                    e_neg <- WI.bvSlt sym e zero
                    t <- WI.bvIte sym e_neg neg_one pos_one
                    WI.bvIte sym e_zero zero t
      fpSign :: FPOp1 fpp t
      fpSign e = do zero <- WI.floatLit sym knownRepr bfPosZero
                    neg_one <- WI.floatLit sym knownRepr (bfFromDouble (-1.0))
                    pos_one <- WI.floatLit sym knownRepr (bfFromDouble 1.0)
                    e_zero <- WI.floatEq sym e zero
                    e_neg <- WI.floatLt sym e zero
                    t <- WI.floatIte sym e_neg neg_one pos_one
                    WI.floatIte sym e_zero zero t
  (CE.Recip _, xe) -> fpOp recip xe
    where
      recip :: FPOp1 fpp t
      recip e = do one <- WI.floatLit sym knownRepr (bfFromDouble 1.0)
                   WI.floatDiv sym fpRM one e
  (CE.Exp _, xe) -> realOp (WI.realExp sym) xe
  (CE.Sqrt _, xe) -> fpOp (WI.floatSqrt sym fpRM) xe
  (CE.Log _, xe) -> realOp (WI.realLog sym) xe
  (CE.Sin _, xe) -> realOp (WI.realSin sym) xe
  (CE.Cos _, xe) -> realOp (WI.realCos sym) xe
  (CE.Tan _, xe) -> realOp (WI.realTan sym) xe
  (CE.Asin _, xe) -> realOp (realRecip <=< WI.realSin sym) xe
  (CE.Acos _, xe) -> realOp (realRecip <=< WI.realCos sym) xe
  (CE.Atan _, xe) -> realOp (realRecip <=< WI.realTan sym) xe
  (CE.Sinh _, xe) -> realOp (WI.realSinh sym) xe
  (CE.Cosh _, xe) -> realOp (WI.realCosh sym) xe
  (CE.Tanh _, xe) -> realOp (WI.realTanh sym) xe
  (CE.Asinh _, xe) -> realOp (realRecip <=< WI.realSinh sym) xe
  (CE.Acosh _, xe) -> realOp (realRecip <=< WI.realCosh sym) xe
  (CE.Atanh _, xe) -> realOp (realRecip <=< WI.realTanh sym) xe
  (CE.BwNot _, xe) -> case xe of
    XBool e -> XBool <$> WI.notPred sym e
    _ -> bvOp (WI.bvNotBits sym) xe
  (CE.Cast _ tp, xe) -> case (xe, tp) of
    (XBool e, CT.Bool) -> return $ XBool e
    (XBool e, CT.Word8) -> XWord8 <$> WI.predToBV sym e knownNat
    (XBool e, CT.Word16) -> XWord16 <$> WI.predToBV sym e knownNat
    (XBool e, CT.Word32) -> XWord32 <$> WI.predToBV sym e knownNat
    (XBool e, CT.Word64) -> XWord64 <$> WI.predToBV sym e knownNat
    (XBool e, CT.Int8) -> XInt8 <$> WI.predToBV sym e knownNat
    (XBool e, CT.Int16) -> XInt16 <$> WI.predToBV sym e knownNat
    (XBool e, CT.Int32) -> XInt32 <$> WI.predToBV sym e knownNat
    (XBool e, CT.Int64) -> XInt64 <$> WI.predToBV sym e knownNat
    (XInt8 e, CT.Int8) -> return $ XInt8 e
    (XInt8 e, CT.Int16) -> XInt16 <$> WI.bvSext sym knownNat e
    (XInt8 e, CT.Int32) -> XInt32 <$> WI.bvSext sym knownNat e
    (XInt8 e, CT.Int64) -> XInt64 <$> WI.bvSext sym knownNat e
    (XInt16 e, CT.Int16) -> return $ XInt16 e
    (XInt16 e, CT.Int32) -> XInt32 <$> WI.bvSext sym knownNat e
    (XInt16 e, CT.Int64) -> XInt64 <$> WI.bvSext sym knownNat e
    (XInt32 e, CT.Int32) -> return $ XInt32 e
    (XInt32 e, CT.Int64) -> XInt64 <$> WI.bvSext sym knownNat e
    (XInt64 e, CT.Int64) -> return $ XInt64 e
    (XWord8 e, CT.Int16) -> XInt16 <$> WI.bvZext sym knownNat e
    (XWord8 e, CT.Int32) -> XInt32 <$> WI.bvZext sym knownNat e
    (XWord8 e, CT.Int64) -> XInt64 <$> WI.bvZext sym knownNat e
    (XWord8 e, CT.Word8) -> return $ XWord8 e
    (XWord8 e, CT.Word16) -> XWord16 <$> WI.bvZext sym knownNat e
    (XWord8 e, CT.Word32) -> XWord32 <$> WI.bvZext sym knownNat e
    (XWord8 e, CT.Word64) -> XWord64 <$> WI.bvZext sym knownNat e
    (XWord16 e, CT.Int32) -> XInt32 <$> WI.bvZext sym knownNat e
    (XWord16 e, CT.Int64) -> XInt64 <$> WI.bvZext sym knownNat e
    (XWord16 e, CT.Word16) -> return $ XWord16 e
    (XWord16 e, CT.Word32) -> XWord32 <$> WI.bvZext sym knownNat e
    (XWord16 e, CT.Word64) -> XWord64 <$> WI.bvZext sym knownNat e
    (XWord32 e, CT.Int64) -> XInt64 <$> WI.bvZext sym knownNat e
    (XWord32 e, CT.Word32) -> return $ XWord32 e
    (XWord32 e, CT.Word64) -> XWord64 <$> WI.bvZext sym knownNat e
    (XWord64 e, CT.Word64) -> return $ XWord64 e
    _ -> panic
  (CE.GetField (CT.Struct s) _ftp extractor, XStruct xes) -> do
    let fieldNameRepr = fieldName (extractor undefined)
    let structFieldNameReprs = valueName <$> CT.toValues s
    let mIx = elemIndex (Some fieldNameRepr) structFieldNameReprs
    case mIx of
      Just ix -> return $ xes !! ix
      Nothing -> panic
  _ -> panic
  where
    numOp :: (forall w . BVOp1 w t)
          -> (forall fpp . FPOp1 fpp t)
          -> XExpr t
          -> IO (XExpr t)
    numOp bvOp fpOp xe = case xe of
      XInt8 e -> XInt8 <$> bvOp e
      XInt16 e -> XInt16 <$> bvOp e
      XInt32 e -> XInt32 <$> bvOp e
      XInt64 e -> XInt64 <$> bvOp e
      XWord8 e -> XWord8 <$> bvOp e
      XWord16 e -> XWord16 <$> bvOp e
      XWord32 e -> XWord32 <$> bvOp e
      XWord64 e -> XWord64 <$> bvOp e
      XFloat e -> XFloat <$> fpOp e
      XDouble e -> XDouble <$> fpOp e
      _ -> panic

    bvOp :: (forall w . BVOp1 w t) -> XExpr t -> IO (XExpr t)
    bvOp f xe = case xe of
      XInt8 e -> XInt8 <$> f e
      XInt16 e -> XInt16 <$> f e
      XInt32 e -> XInt32 <$> f e
      XInt64 e -> XInt64 <$> f e
      XWord8 e -> XWord8 <$> f e
      XWord16 e -> XWord16 <$> f e
      XWord32 e -> XWord32 <$> f e
      XWord64 e -> XWord64 <$> f e
      _ -> panic

    fpOp :: (forall fpp . FPOp1 fpp t) -> XExpr t -> IO (XExpr t)
    fpOp g xe = case xe of
      XFloat e -> XFloat <$> g e
      XDouble e -> XDouble <$> g e
      _ -> panic

    realOp :: RealOp1 t -> XExpr t -> IO (XExpr t)
    realOp h xe = fpOp hf xe
      where
        hf :: (forall fpp . FPOp1 fpp t)
        hf e = do re <- WI.floatToReal sym e
                  hre <- h re
                  WI.realToFloat sym knownRepr fpRM hre

    realRecip :: RealOp1 t
    realRecip e = do one <- WI.realLit sym 1
                     WI.realDiv sym one e

type BVOp2 w t = (KnownNat w, 1 <= w) => WB.BVExpr t w -> WB.BVExpr t w -> IO (WB.BVExpr t w)

type FPOp2 fpp t = KnownRepr WT.FloatPrecisionRepr fpp => WB.Expr t (WT.BaseFloatType fpp) -> WB.Expr t (WT.BaseFloatType fpp) -> IO (WB.Expr t (WT.BaseFloatType fpp))

type RealOp2 t = WB.Expr t WT.BaseRealType -> WB.Expr t WT.BaseRealType -> IO (WB.Expr t WT.BaseRealType)

type BoolCmp2 t = WB.BoolExpr t -> WB.BoolExpr t -> IO (WB.BoolExpr t)

type BVCmp2 w t = (KnownNat w, 1 <= w) => WB.BVExpr t w -> WB.BVExpr t w -> IO (WB.BoolExpr t)

type FPCmp2 fpp t = KnownRepr WT.FloatPrecisionRepr fpp => WB.Expr t (WT.BaseFloatType fpp) -> WB.Expr t (WT.BaseFloatType fpp) -> IO (WB.BoolExpr t)

translateOp2 :: forall t st fs a b c .
                WB.ExprBuilder t st fs
             -> (WB.ExprSymFn t
                 (EmptyCtx ::> WT.BaseRealType ::> WT.BaseRealType)
                 WT.BaseRealType)
             -- ^ Pow function
             -> (WB.ExprSymFn t
                 (EmptyCtx ::> WT.BaseRealType ::> WT.BaseRealType)
                 WT.BaseRealType)
             -- ^ Logb function
             -> CE.Op2 a b c
             -> XExpr t
             -> XExpr t
             -> IO (XExpr t)
translateOp2 sym powFn logbFn op xe1 xe2 = case (op, xe1, xe2) of
  (CE.And, XBool e1, XBool e2) -> XBool <$> WI.andPred sym e1 e2
  (CE.Or, XBool e1, XBool e2) -> XBool <$> WI.orPred sym e1 e2
  (CE.Add _, xe1, xe2) -> numOp (WI.bvAdd sym) (WI.floatAdd sym fpRM) xe1 xe2
  (CE.Sub _, xe1, xe2) -> numOp (WI.bvSub sym) (WI.floatSub sym fpRM) xe1 xe2
  (CE.Mul _, xe1, xe2) -> numOp (WI.bvMul sym) (WI.floatMul sym fpRM) xe1 xe2
  (CE.Mod _, xe1, xe2) -> bvOp (WI.bvSrem sym) (WI.bvUrem sym) xe1 xe2
  (CE.Div _, xe1, xe2) -> bvOp (WI.bvSdiv sym) (WI.bvUdiv sym) xe1 xe2
  (CE.Fdiv _, xe1, xe2) -> fpOp (WI.floatDiv sym fpRM) xe1 xe2
  (CE.Pow _, xe1, xe2) -> fpOp powFn' xe1 xe2
    where
      powFn' :: FPOp2 fpp t
      powFn' e1 e2 = do re1 <- WI.floatToReal sym e1
                        re2 <- WI.floatToReal sym e2
                        let args = (Empty :> re1 :> re2)
                        rpow <- WI.applySymFn sym powFn args
                        WI.realToFloat sym knownRepr fpRM rpow
  (CE.Logb _, xe1, xe2) -> fpOp logbFn' xe1 xe2
    where
      logbFn' :: FPOp2 fpp t
      logbFn' e1 e2 = do re1 <- WI.floatToReal sym e1
                         re2 <- WI.floatToReal sym e2
                         let args = (Empty :> re1 :> re2)
                         rpow <- WI.applySymFn sym logbFn args
                         WI.realToFloat sym knownRepr fpRM rpow
  (CE.Eq _, xe1, xe2) -> cmp (WI.eqPred sym) (WI.bvEq sym) (WI.floatEq sym) xe1 xe2
  (CE.Ne _, xe1, xe2) -> cmp neqPred bvNeq fpNeq xe1 xe2
    where
      neqPred :: BoolCmp2 t
      neqPred e1 e2 = do e <- WI.eqPred sym e1 e2
                         WI.notPred sym e
      bvNeq :: forall w . BVCmp2 w t
      bvNeq e1 e2 = do e <- WI.bvEq sym e1 e2
                       WI.notPred sym e
      fpNeq :: forall fpp . FPCmp2 fpp t
      fpNeq e1 e2 = do e <- WI.floatEq sym e1 e2
                       WI.notPred sym e
  (CE.Le _, xe1, xe2) -> numCmp (WI.bvSle sym) (WI.bvUle sym) (WI.floatLe sym) xe1 xe2
  (CE.Ge _, xe1, xe2) -> numCmp (WI.bvSge sym) (WI.bvUge sym) (WI.floatGe sym) xe1 xe2
  (CE.Lt _, xe1, xe2) -> numCmp (WI.bvSlt sym) (WI.bvUlt sym) (WI.floatLt sym) xe1 xe2
  (CE.Gt _, xe1, xe2) -> numCmp (WI.bvSgt sym) (WI.bvUgt sym) (WI.floatGt sym) xe1 xe2
  (CE.BwAnd _, xe1, xe2) -> bvOp (WI.bvAndBits sym) (WI.bvAndBits sym) xe1 xe2
  (CE.BwOr _, xe1, xe2) -> bvOp (WI.bvOrBits sym) (WI.bvOrBits sym) xe1 xe2
  (CE.BwXor _, xe1, xe2) -> bvOp (WI.bvXorBits sym) (WI.bvXorBits sym) xe1 xe2
  -- Note: For both shift operators, we are interpreting the shifter as an
  -- unsigned bitvector regardless of whether it is a word or an int.
  (CE.BwShiftL _ _, xe1, xe2) -> do
    Just (SomeBVExpr e1 w1 _ ctor1) <- return $ asBVExpr xe1
    Just (SomeBVExpr e2 w2 _ _    ) <- return $ asBVExpr xe2
    e2' <- case testNatCases w1 w2 of
      NatCaseLT LeqProof -> WI.bvTrunc sym w1 e2
      NatCaseEQ -> return e2
      NatCaseGT LeqProof -> WI.bvZext sym w1 e2
    ctor1 <$> WI.bvShl sym e1 e2'
  (CE.BwShiftR _ _, xe1, xe2) -> do
    Just (SomeBVExpr e1 w1 sgn1 ctor1) <- return $ asBVExpr xe1
    Just (SomeBVExpr e2 w2 _    _    ) <- return $ asBVExpr xe2
    e2' <- case testNatCases w1 w2 of
      NatCaseLT LeqProof -> WI.bvTrunc sym w1 e2
      NatCaseEQ -> return e2
      NatCaseGT LeqProof -> WI.bvZext sym w1 e2
    ctor1 <$> case sgn1 of
      Signed -> WI.bvAshr sym e1 e2'
      Unsigned -> WI.bvLshr sym e1 e2'
  -- Note: Currently, copilot does not check if array indices are out of bounds,
  -- even for constant expressions. The method of translation we are using
  -- simply creates a nest of if-then-else expression to check the index
  -- expression against all possible indices. If the index expression is known
  -- by the solver to be out of bounds (for instance, if it is a constant 5 for
  -- an array of 5 elements), then the if-then-else will trivially resolve to
  -- true.
  (CE.Index _, xe1, xe2) -> do
    case (xe1, xe2) of
      (XArray xes, XWord32 ix) -> buildIndexExpr sym 0 ix xes
      _ -> panic
  _ -> panic
  where
    numOp :: (forall w . BVOp2 w t)
          -> (forall fpp . FPOp2 fpp t)
          -> XExpr t
          -> XExpr t
          -> IO (XExpr t)
    numOp bvOp fpOp xe1 xe2 = case (xe1, xe2) of
      (XInt8 e1, XInt8 e2) -> XInt8 <$> bvOp e1 e2
      (XInt16 e1, XInt16 e2) -> XInt16 <$> bvOp e1 e2
      (XInt32 e1, XInt32 e2)-> XInt32 <$> bvOp e1 e2
      (XInt64 e1, XInt64 e2)-> XInt64 <$> bvOp e1 e2
      (XWord8 e1, XWord8 e2)-> XWord8 <$> bvOp e1 e2
      (XWord16 e1, XWord16 e2)-> XWord16 <$> bvOp e1 e2
      (XWord32 e1, XWord32 e2)-> XWord32 <$> bvOp e1 e2
      (XWord64 e1, XWord64 e2)-> XWord64 <$> bvOp e1 e2
      (XFloat e1, XFloat e2)-> XFloat <$> fpOp e1 e2
      (XDouble e1, XDouble e2)-> XDouble <$> fpOp e1 e2
      _ -> panic

    bvOp :: (forall w . BVOp2 w t)
         -> (forall w . BVOp2 w t)
         -> XExpr t
         -> XExpr t
         -> IO (XExpr t)
    bvOp opS opU xe1 xe2 = case (xe1, xe2) of
      (XInt8 e1, XInt8 e2) -> XInt8 <$> opS e1 e2
      (XInt16 e1, XInt16 e2) -> XInt16 <$> opS e1 e2
      (XInt32 e1, XInt32 e2) -> XInt32 <$> opS e1 e2
      (XInt64 e1, XInt64 e2) -> XInt64 <$> opS e1 e2
      (XWord8 e1, XWord8 e2) -> XWord8 <$> opU e1 e2
      (XWord16 e1, XWord16 e2) -> XWord16 <$> opU e1 e2
      (XWord32 e1, XWord32 e2) -> XWord32 <$> opU e1 e2
      (XWord64 e1, XWord64 e2) -> XWord64 <$> opU e1 e2
      _ -> panic

    fpOp :: (forall fpp . FPOp2 fpp t)
         -> XExpr t
         -> XExpr t
         -> IO (XExpr t)
    fpOp op xe1 xe2 = case (xe1, xe2) of
      (XFloat e1, XFloat e2) -> XFloat <$> op e1 e2
      (XDouble e1, XDouble e2) -> XDouble <$> op e1 e2
      _ -> panic

    cmp :: BoolCmp2 t
        -> (forall w . BVCmp2 w t)
        -> (forall fpp . FPCmp2 fpp t)
        -> XExpr t
        -> XExpr t
        -> IO (XExpr t)
    cmp boolOp bvOp fpOp xe1 xe2 = case (xe1, xe2) of
      (XBool e1, XBool e2) -> XBool <$> boolOp e1 e2
      (XInt8 e1, XInt8 e2) -> XBool <$> bvOp e1 e2
      (XInt16 e1, XInt16 e2) -> XBool <$> bvOp e1 e2
      (XInt32 e1, XInt32 e2)-> XBool <$> bvOp e1 e2
      (XInt64 e1, XInt64 e2)-> XBool <$> bvOp e1 e2
      (XWord8 e1, XWord8 e2)-> XBool <$> bvOp e1 e2
      (XWord16 e1, XWord16 e2)-> XBool <$> bvOp e1 e2
      (XWord32 e1, XWord32 e2)-> XBool <$> bvOp e1 e2
      (XWord64 e1, XWord64 e2)-> XBool <$> bvOp e1 e2
      (XFloat e1, XFloat e2)-> XBool <$> fpOp e1 e2
      (XDouble e1, XDouble e2)-> XBool <$> fpOp e1 e2
      _ -> panic

    numCmp :: (forall w . BVCmp2 w t)
           -> (forall w . BVCmp2 w t)
           -> (forall fpp . FPCmp2 fpp t)
           -> XExpr t
           -> XExpr t
           -> IO (XExpr t)
    numCmp bvSOp bvUOp fpOp xe1 xe2 = case (xe1, xe2) of
      (XInt8 e1, XInt8 e2) -> XBool <$> bvSOp e1 e2
      (XInt16 e1, XInt16 e2) -> XBool <$> bvSOp e1 e2
      (XInt32 e1, XInt32 e2)-> XBool <$> bvSOp e1 e2
      (XInt64 e1, XInt64 e2)-> XBool <$> bvSOp e1 e2
      (XWord8 e1, XWord8 e2)-> XBool <$> bvUOp e1 e2
      (XWord16 e1, XWord16 e2)-> XBool <$> bvUOp e1 e2
      (XWord32 e1, XWord32 e2)-> XBool <$> bvUOp e1 e2
      (XWord64 e1, XWord64 e2)-> XBool <$> bvUOp e1 e2
      (XFloat e1, XFloat e2)-> XBool <$> fpOp e1 e2
      (XDouble e1, XDouble e2)-> XBool <$> fpOp e1 e2
      _ -> panic

    buildIndexExpr :: 1 <= n
                   => WB.ExprBuilder t st fs
                   -> Word32
                   -- ^ Index
                   -> WB.Expr t (WT.BaseBVType 32)
                   -- ^ Index
                   -> V.Vector n (XExpr t)
                   -- ^ Elements
                   -> IO (XExpr t)
    buildIndexExpr sym curIx ix xelts = case V.uncons xelts of
      (xe, Left Refl) -> return xe
      (xe, Right xelts') -> do
        LeqProof <- return $ V.nonEmpty xelts'
        rstExpr <- buildIndexExpr sym (curIx+1) ix xelts'
        curIxExpr <- WI.bvLit sym knownNat (BV.word32 curIx)
        ixEq <- WI.bvEq sym curIxExpr ix
        mkIte sym ixEq xe rstExpr

    mkIte :: WB.ExprBuilder t st fs
          -> WB.Expr t WT.BaseBoolType
          -> XExpr t
          -> XExpr t
          -> IO (XExpr t)
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
          (XFloat e1, XFloat e2) -> XFloat <$> WI.floatIte sym pred e1 e2
          (XDouble e1, XDouble e2) -> XDouble <$> WI.floatIte sym pred e1 e2
          (XStruct xes1, XStruct xes2) ->
            XStruct <$> zipWithM (mkIte sym pred) xes1 xes2
          (XArray xes1, XArray xes2) ->
            case V.length xes1 `testEquality` V.length xes2 of
              Just Refl -> XArray <$> V.zipWithM (mkIte sym pred) xes1 xes2
              Nothing -> panic
          _ -> panic

translateOp3 :: forall t st fs a b c d .
                WB.ExprBuilder t st fs
             -> CE.Op3 a b c d
             -> XExpr t
             -> XExpr t
             -> XExpr t
             -> IO (XExpr t)
translateOp3 sym (CE.Mux _) (XBool te) xe1 xe2 = case (xe1, xe2) of
  (XBool e1, XBool e2) -> XBool <$> WI.itePred sym te e1 e2
  (XInt8 e1, XInt8 e2) -> XInt8 <$> WI.bvIte sym te e1 e2
  (XInt16 e1, XInt16 e2) -> XInt16 <$> WI.bvIte sym te e1 e2
  (XInt32 e1, XInt32 e2) -> XInt32 <$> WI.bvIte sym te e1 e2
  (XInt64 e1, XInt64 e2) -> XInt64 <$> WI.bvIte sym te e1 e2
  (XWord8 e1, XWord8 e2) -> XWord8 <$> WI.bvIte sym te e1 e2
  (XWord16 e1, XWord16 e2) -> XWord16 <$> WI.bvIte sym te e1 e2
  (XWord32 e1, XWord32 e2) -> XWord32 <$> WI.bvIte sym te e1 e2
  (XWord64 e1, XWord64 e2) -> XWord64 <$> WI.bvIte sym te e1 e2
  (XFloat e1, XFloat e2) -> XFloat <$> WI.floatIte sym te e1 e2
  (XDouble e1, XDouble e2) -> XDouble <$> WI.floatIte sym te e1 e2
  _ -> panic
translateOp3 _ _ _ _ _ = panic

-- | The What4 representation of a copilot expression. We do not attempt to
-- track the type of the inner expression at the type level, but instead lump
-- everything together into the 'XExpr t' type. The only reason this is a GADT
-- is for the array case; we need to know that the array length is strictly
-- positive.
data XExpr t where
  XBool       :: WB.Expr t WT.BaseBoolType -> XExpr t
  XInt8       :: WB.Expr t (WT.BaseBVType 8) -> XExpr t
  XInt16      :: WB.Expr t (WT.BaseBVType 16) -> XExpr t
  XInt32      :: WB.Expr t (WT.BaseBVType 32) -> XExpr t
  XInt64      :: WB.Expr t (WT.BaseBVType 64) -> XExpr t
  XWord8      :: WB.Expr t (WT.BaseBVType 8) -> XExpr t
  XWord16     :: WB.Expr t (WT.BaseBVType 16) -> XExpr t
  XWord32     :: WB.Expr t (WT.BaseBVType 32) -> XExpr t
  XWord64     :: WB.Expr t (WT.BaseBVType 64) -> XExpr t
  XFloat      :: WB.Expr t (WT.BaseFloatType WT.Prec32) -> XExpr t
  XDouble     :: WB.Expr t (WT.BaseFloatType WT.Prec64) -> XExpr t
  XEmptyArray :: XExpr t
  XArray      :: 1 <= n => V.Vector n (XExpr t) -> XExpr t
  XStruct     :: [XExpr t] -> XExpr t
  -- XArray      :: NatRepr n
  --             -> BaseTypeRepr tp
  --             -> Some (WB.Expr t)
  -- XStruct     :: Assignment BaseTypeRepr tps
  --             -> WB.Expr t (BaseStructType tps)
  --             -> XExpr t

deriving instance Show (XExpr t)

-- | We assume round-near-even throughout, but this variable can be changed if
-- needed.
fpRM :: WI.RoundingMode
fpRM = WI.RNE

data CopilotWhat4 = CopilotWhat4

instance Panic.PanicComponent CopilotWhat4 where
  panicComponentName _ = "Copilot/What4 translation"
  panicComponentIssues _ = "https://github.com/Copilot-Language/copilot/issues"

  {-# NOINLINE Panic.panicComponentRevision #-}
  panicComponentRevision = $(Panic.useGitRevision)

-- | Use this function rather than an error monad since it indicates that
-- copilot-core's "reify" function did something incorrectly.
panic :: MonadIO m => m a
panic = Panic.panic CopilotWhat4 "Copilot.Theorem.What4"
        [ "Ill-typed core expression" ]
