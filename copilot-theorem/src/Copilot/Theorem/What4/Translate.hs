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
-- Module      : Copilot.Theorem.What4.Translate
-- Description : Translate Copilot specifications into What4
-- Copyright   : (c) Galois Inc., 2021
-- Maintainer  : robdockins@galois.com
-- Stability   : experimental
-- Portability : POSIX

-- Notes from Ben
--    Distrust floats...

module Copilot.Theorem.What4.Translate
  ( XExpr(..)
  , TransM
  , TransState(..)
  , runTransM
  , panic
  , valFromExpr
  , CopilotValue(..)
  , BuilderState(..)

  , StreamOffset(..)
  , LocalEnv
  , translateExpr
  , translateConstExpr
  , getStreamValue
  , getExternConstant
  )
where

import qualified Copilot.Core.Expr       as CE
import qualified Copilot.Core.Operators  as CE
import qualified Copilot.Core.PrettyPrint as CP
import qualified Copilot.Core.Spec       as CS
import qualified Copilot.Core.Type       as CT
import qualified Copilot.Core.Type.Array as CT

import qualified What4.Expr.Builder     as WB
import qualified What4.Expr.GroundEval  as WG
import qualified What4.Interface        as WI
import qualified What4.BaseTypes        as WT

import Control.Monad.State
import qualified Data.BitVector.Sized as BV
import Data.IORef (newIORef, readIORef, modifyIORef)
import Data.List (elemIndex, genericLength, genericIndex)
import Data.Maybe (fromJust)
import qualified Data.Map as Map
import Data.Parameterized.Classes
import Data.Parameterized.Context hiding (zipWithM)
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Data.Parameterized.SymbolRepr
import qualified Data.Parameterized.Vector as V
import Data.Word
import LibBF ( bfToDouble
             , bfFromDouble
             , bfPosZero
             , pattern NearEven )
import GHC.TypeNats (KnownNat)
import qualified Panic as Panic

-- | We assume round-near-even throughout, but this variable can be changed if
-- needed.
fpRM :: WI.RoundingMode
fpRM = WI.RNE

-- | No builder state needed.
data BuilderState a = EmptyState

-- What4 translation

-- | Streams expressions are evaluated in two possible modes.
--   The \"absolute\" mode computes the value of a stream expression
--   relative to the beginning of time @t=0@.  The \"relative\" mode is
--   useful for inductive proofs and the offset values are conceptually relative to
--   some arbitrary, but fixed, index @j>=0@.  In both cases, negative indexes
--   are not allowed.
--
--   The main difference between these modes is the interpretation of streams
--   for the first values, which are in the \"buffer\" range.  For absolute
--   indices, the actual fixed values for the streams are returned; for relative
--   indices, uninterpreted values are generated for the values in the stream buffer.
--   For both modes, stream values after their buffer region are defined by their
--   recurrence expression.
data StreamOffset
  = AbsoluteOffset !Integer
  | RelativeOffset !Integer
 deriving (Eq, Ord, Show)

-- | Increment a stream offset by a drop amount.
addOffset :: StreamOffset -> CE.DropIdx -> StreamOffset
addOffset (AbsoluteOffset i) j = AbsoluteOffset (i + toInteger j)
addOffset (RelativeOffset i) j = RelativeOffset (i + toInteger j)

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
data TransState sym = TransState {
  -- | Map keeping track of all external variables encountered during translation.
  mentionedExternals :: Map.Map CE.Name (Some CT.Type),

  -- | Memo table for external variables, indexed by the external stream name
  --   and a stream offset.
  externVars :: Map.Map (CE.Name, StreamOffset) (XExpr sym),

  -- | Memo table for stream values, indexed by the stream Id and offset.
  streamValues :: Map.Map (CE.Id, StreamOffset) (XExpr sym),

  -- | A cache to look up stream definitions by their Id.
  streams :: Map.Map CE.Id CS.Stream,

  -- | Binary power operator, represented as an uninterpreted function.
  pow :: WI.SymFn sym
         (EmptyCtx ::> WT.BaseRealType ::> WT.BaseRealType)
         WT.BaseRealType,
  -- | Binary logarithm operator, represented as an uninterpreted function.
  logb :: WI.SymFn sym
          (EmptyCtx ::> WT.BaseRealType ::> WT.BaseRealType)
          WT.BaseRealType
  }

newtype TransM sym a = TransM { unTransM :: StateT (TransState sym) IO a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadIO
           , MonadState (TransState sym)
           )

data CopilotWhat4 = CopilotWhat4

instance Panic.PanicComponent CopilotWhat4 where
  panicComponentName _ = "Copilot/What4 translation"
  panicComponentIssues _ = "https://github.com/Copilot-Language/copilot/issues"

  {-# NOINLINE Panic.panicComponentRevision #-}
  panicComponentRevision = $(Panic.useGitRevision)

-- | Use this function rather than an error monad since it indicates that
-- copilot-core's "reify" function did something incorrectly.
panic :: (Panic.HasCallStack, MonadIO m) => [String] -> m a
panic msg = Panic.panic CopilotWhat4 "Ill-typed core expression" msg

runTransM :: WI.IsSymExprBuilder sym => sym -> CS.Spec -> TransM sym a -> IO a
runTransM sym spec m =
  do -- Build up initial translation state
     let streamMap = Map.fromList $
           (\stream -> (CS.streamId stream, stream)) <$> CS.specStreams spec
     pow <- WI.freshTotalUninterpFn sym (WI.safeSymbol "pow") knownRepr knownRepr
     logb <- WI.freshTotalUninterpFn sym (WI.safeSymbol "logb") knownRepr knownRepr
     let st = TransState
              { mentionedExternals = mempty
              , externVars = mempty
              , streamValues = mempty
              , streams = streamMap
              , pow = pow
              , logb = logb
              }

     (res, _) <- runStateT (unTransM m) st
     return res

-- | Retrieve a stream definition given its id.
getStreamDef :: CE.Id -> TransM sym CS.Stream
getStreamDef streamId = fromJust <$> gets (Map.lookup streamId . streams)

fieldName :: KnownSymbol s => CT.Field s a -> SymbolRepr s
fieldName _ = knownSymbol

valueName :: CT.Value a -> Some SymbolRepr
valueName (CT.Value _ f) = Some (fieldName f)


-- | The What4 representation of a copilot expression. We do not attempt to
-- track the type of the inner expression at the type level, but instead lump
-- everything together into the 'XExpr t' type. The only reason this is a GADT
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
  XFloat      :: WI.SymExpr sym (WT.BaseFloatType WT.Prec32) -> XExpr sym
  XDouble     :: WI.SymExpr sym (WT.BaseFloatType WT.Prec64) -> XExpr sym
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

data CopilotValue a = CopilotValue { cvType :: CT.Type a
                                   , cvVal :: a
                                   }

valFromExpr :: sym ~ WB.ExprBuilder t st fs =>
  WG.GroundEvalFn t -> XExpr sym -> IO (Some CopilotValue)
valFromExpr ge xe = case xe of
  XBool e -> Some . CopilotValue CT.Bool <$> WG.groundEval ge e
  XInt8 e -> Some . CopilotValue CT.Int8 . fromSBV <$> WG.groundEval ge e
  XInt16 e -> Some . CopilotValue CT.Int16 . fromSBV <$> WG.groundEval ge e
  XInt32 e -> Some . CopilotValue CT.Int32 . fromSBV <$> WG.groundEval ge e
  XInt64 e -> Some . CopilotValue CT.Int64 . fromSBV <$> WG.groundEval ge e
  XWord8 e -> Some . CopilotValue CT.Word8 . fromBV <$> WG.groundEval ge e
  XWord16 e -> Some . CopilotValue CT.Word16 . fromBV <$> WG.groundEval ge e
  XWord32 e -> Some . CopilotValue CT.Word32 . fromBV <$> WG.groundEval ge e
  XWord64 e -> Some . CopilotValue CT.Word64 . fromBV <$> WG.groundEval ge e
  XFloat e ->
    Some . CopilotValue CT.Float . realToFrac . fst . bfToDouble NearEven <$> WG.groundEval ge e
  XDouble e ->
    Some . CopilotValue CT.Double . fst . bfToDouble NearEven <$> WG.groundEval ge e
  _ -> error "valFromExpr unhandled case"
  where
    fromBV :: forall a w . Num a => BV.BV w -> a
    fromBV = fromInteger . BV.asUnsigned

    fromSBV :: forall a w . (1 <= w, KnownNat w, Num a) => BV.BV w -> a
    fromSBV = fromInteger . BV.asSigned knownRepr

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
  WI.IsExprBuilder sym =>
  sym ->
  CT.Type a ->
  a ->
  IO (XExpr sym)
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
freshCPConstant :: forall a sym.
  WI.IsSymExprBuilder sym =>
  sym ->
  String ->
  CT.Type a ->
  IO (XExpr sym)
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


-- | Compute and cache the value of a stream with the given identifier
--   at the given offset.
getStreamValue :: WI.IsSymExprBuilder sym =>
  sym -> CE.Id -> StreamOffset -> TransM sym (XExpr sym)
getStreamValue sym streamId offset =
  do svs <- gets streamValues
     case Map.lookup (streamId, offset) svs of
       Just xe -> return xe
       Nothing ->
         do streamDef <- getStreamDef streamId
            xe <- computeStreamValue streamDef
            modify (\st -> st{ streamValues = Map.insert (streamId, offset) xe (streamValues st) })
            return xe

  where
  computeStreamValue
     CS.Stream
     { CS.streamId = id, CS.streamBuffer = buf, CS.streamExpr = ex, CS.streamExprType = tp } =
     let len = genericLength buf in
     case offset of
       AbsoluteOffset i
         | i < 0     -> panic ["Invalid absolute offset " ++ show i ++ " for stream " ++ show id]
         | i < len   -> liftIO (translateConstExpr sym tp (genericIndex buf i))
         | otherwise -> translateExpr sym mempty ex (AbsoluteOffset (i - len))
       RelativeOffset i
         | i < 0     -> panic ["Invalid relative offset " ++ show i ++ " for stream " ++ show id]
         | i < len   -> let nm = "s" ++ show id ++ "_r" ++ show i
                        in liftIO (freshCPConstant sym nm tp)
         | otherwise -> translateExpr sym mempty ex (RelativeOffset (i - len))


-- | Compute and cache the value of an external stream with the given name
--   at the given offset.
getExternConstant :: WI.IsSymExprBuilder sym =>
  sym -> CT.Type a -> CE.Name -> StreamOffset -> TransM sym (XExpr sym)
getExternConstant sym tp nm offset =
  do es <- gets externVars
     case Map.lookup (nm, offset) es of
       Just xe -> return xe
       Nothing -> do
         xe <- computeExternConstant
         modify (\st -> st { externVars = Map.insert (nm, offset) xe (externVars st)
                           , mentionedExternals = Map.insert nm (Some tp) (mentionedExternals st)
                           } )
         return xe
 where
 computeExternConstant =
    case offset of
      AbsoluteOffset i
        | i < 0     -> panic ["Invalid absolute offset " ++ show i ++ " for external stream " ++ nm]
        | otherwise -> let nm' = nm ++ "_a" ++ show i
                       in liftIO (freshCPConstant sym nm' tp)
      RelativeOffset i
        | i < 0     -> panic ["Invalid relative offset " ++ show i ++ " for external stream " ++ nm]
        | otherwise -> let nm' = nm ++ "_r" ++ show i
                       in liftIO (freshCPConstant sym nm' tp)


type LocalEnv sym = Map.Map CE.Name (StreamOffset -> TransM sym (XExpr sym))

-- | Compute the value of a stream expression at the given offset in the
--   given local environment.
translateExpr ::
  WI.IsSymExprBuilder sym =>
  sym ->
  LocalEnv sym {- ^ Enviornment for local variables -} ->
  CE.Expr a {- ^ Expression to translate -} ->
  StreamOffset {- ^ Offset to compute -} ->
  TransM sym (XExpr sym)
translateExpr sym localEnv e offset = case e of
  CE.Const tp a -> liftIO $ translateConstExpr sym tp a
  CE.Drop _tp ix streamId -> getStreamValue sym streamId (addOffset offset ix)
  CE.ExternVar tp nm _prefix -> getExternConstant sym tp nm offset
  CE.Op1 op e1 ->
    do xe1 <- translateExpr sym localEnv e1 offset
       liftIO $ translateOp1 e sym op xe1
  CE.Op2 op e1 e2 ->
    do xe1 <- translateExpr sym localEnv e1 offset
       xe2 <- translateExpr sym localEnv e2 offset
       powFn <- gets pow
       logbFn <- gets logb
       liftIO $ translateOp2 e sym powFn logbFn op xe1 xe2
  CE.Op3 op e1 e2 e3 ->
    do xe1 <- translateExpr sym localEnv e1 offset
       xe2 <- translateExpr sym localEnv e2 offset
       xe3 <- translateExpr sym localEnv e3 offset
       liftIO $ translateOp3 e sym op xe1 xe2 xe3
  CE.Label _ _ e1 ->
    translateExpr sym localEnv e1 offset
  CE.Local _tpa _tpb nm e1 body ->
    do ref <- liftIO (newIORef mempty)
       let f o = do m <- liftIO (readIORef ref)
                    case Map.lookup o m of
                      Just x -> return x
                      Nothing ->
                        do x <- translateExpr sym localEnv e1 o
                           liftIO (modifyIORef ref (Map.insert o x))
                           return x
       let localEnv' = Map.insert nm f localEnv
       translateExpr sym localEnv' body offset
  CE.Var _tp nm ->
    case Map.lookup nm localEnv of
      Nothing -> panic ["translateExpr: unknown var " ++ show nm]
      Just f  -> f offset


type BVOp1 sym w = (KnownNat w, 1 <= w) => WI.SymBV sym w -> IO (WI.SymBV sym w)

type FPOp1 sym fpp =
  KnownRepr WT.FloatPrecisionRepr fpp =>
  WI.SymExpr sym (WT.BaseFloatType fpp) -> IO (WI.SymExpr sym (WT.BaseFloatType fpp))

type RealOp1 sym = WI.SymExpr sym WT.BaseRealType -> IO (WI.SymExpr sym WT.BaseRealType)

translateOp1 :: forall sym a b.
  WI.IsExprBuilder sym =>
  CE.Expr b {- ^ Original value we are translating -} ->
  sym ->
  CE.Op1 a b ->
  XExpr sym ->
  IO (XExpr sym)
translateOp1 origExpr sym op xe = case (op, xe) of
  (CE.Not, XBool e) -> XBool <$> WI.notPred sym e
  (CE.Not, _) -> panic ["Expected bool", show xe]
  (CE.Abs _, xe) -> numOp bvAbs fpAbs xe
    where
      bvAbs :: BVOp1 sym w
      bvAbs e = do zero <- WI.bvLit sym knownNat (BV.zero knownNat)
                   e_neg <- WI.bvSlt sym e zero
                   neg_e <- WI.bvSub sym zero e
                   WI.bvIte sym e_neg neg_e e
      fpAbs :: FPOp1 sym fpp
      fpAbs e = do zero <- WI.floatLit sym knownRepr bfPosZero
                   e_neg <- WI.floatLt sym e zero
                   neg_e <- WI.floatSub sym fpRM zero e
                   WI.floatIte sym e_neg neg_e e
  (CE.Sign _, xe) -> numOp bvSign fpSign xe
    where
      bvSign :: BVOp1 sym w
      bvSign e = do zero <- WI.bvLit sym knownRepr (BV.zero knownNat)
                    neg_one <- WI.bvLit sym knownNat (BV.mkBV knownNat (-1))
                    pos_one <- WI.bvLit sym knownNat (BV.mkBV knownNat 1)
                    e_zero <- WI.bvEq sym e zero
                    e_neg <- WI.bvSlt sym e zero
                    t <- WI.bvIte sym e_neg neg_one pos_one
                    WI.bvIte sym e_zero zero t
      fpSign :: FPOp1 sym fpp
      fpSign e = do zero <- WI.floatLit sym knownRepr bfPosZero
                    neg_one <- WI.floatLit sym knownRepr (bfFromDouble (-1.0))
                    pos_one <- WI.floatLit sym knownRepr (bfFromDouble 1.0)
                    e_zero <- WI.floatEq sym e zero
                    e_neg <- WI.floatLt sym e zero
                    t <- WI.floatIte sym e_neg neg_one pos_one
                    WI.floatIte sym e_zero zero t
  (CE.Recip _, xe) -> fpOp recip xe
    where
      recip :: FPOp1 sym fpp
      recip e = do one <- WI.floatLit sym knownRepr (bfFromDouble 1.0)
                   WI.floatDiv sym fpRM one e
  (CE.Sqrt _, xe) -> fpOp (WI.floatSqrt sym fpRM) xe

  (CE.Exp _, xe) -> realOp (WI.realExp sym) xe
  (CE.Log _, xe) -> realOp (WI.realLog sym) xe
  (CE.Sin _, xe) -> realOp (WI.realSin sym) xe
  (CE.Cos _, xe) -> realOp (WI.realCos sym) xe
  (CE.Tan _, xe) -> realOp (WI.realTan sym) xe
  (CE.Sinh _, xe) -> realOp (WI.realSinh sym) xe
  (CE.Cosh _, xe) -> realOp (WI.realCosh sym) xe
  (CE.Tanh _, xe) -> realOp (WI.realTanh sym) xe

  -- TODO, these inverse function definitions are bogus...
  (CE.Asin _, xe) -> realOp (realRecip <=< WI.realSin sym) xe
  (CE.Acos _, xe) -> realOp (realRecip <=< WI.realCos sym) xe
  (CE.Atan _, xe) -> realOp (realRecip <=< WI.realTan sym) xe
  (CE.Asinh _, xe) -> realOp (realRecip <=< WI.realSinh sym) xe
  (CE.Acosh _, xe) -> realOp (realRecip <=< WI.realCosh sym) xe
  (CE.Atanh _, xe) -> realOp (realRecip <=< WI.realTanh sym) xe

  (CE.BwNot _, xe) -> case xe of
    XBool e -> XBool <$> WI.notPred sym e
    _ -> bvOp (WI.bvNotBits sym) xe

  (CE.Cast _ tp, _) -> castOp origExpr sym tp xe
  (CE.GetField (CT.Struct s) _ftp extractor, XStruct xes) -> do
    let fieldNameRepr = fieldName (extractor undefined)
    let structFieldNameReprs = valueName <$> CT.toValues s
    let mIx = elemIndex (Some fieldNameRepr) structFieldNameReprs
    case mIx of
      Just ix -> return $ xes !! ix
      Nothing -> panic ["Could not find field " ++ show fieldNameRepr, show s ]
  _ -> panic ["Unexpected value for op: " ++ show (CP.ppExpr origExpr), show xe ]
  where
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
      XFloat e -> XFloat <$> fpOp e
      XDouble e -> XDouble <$> fpOp e
      _ -> panic [ "Unexpected value in numOp", show xe ]

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
      _ -> panic [ "Unexpected value in bvOp", show xe ]

    fpOp :: (forall fpp . FPOp1 sym fpp) -> XExpr sym -> IO (XExpr sym)
    fpOp g xe = case xe of
      XFloat e -> XFloat <$> g e
      XDouble e -> XDouble <$> g e
      _ -> panic [ "Unexpected value in fpOp", show xe ]

    realOp :: RealOp1 sym -> XExpr sym -> IO (XExpr sym)
    realOp h xe = fpOp hf xe
      where
        hf :: (forall fpp . FPOp1 sym fpp)
        hf e = do re <- WI.floatToReal sym e
                  hre <- h re
                  WI.realToFloat sym knownRepr fpRM hre

    realRecip :: RealOp1 sym
    realRecip e = do one <- WI.realLit sym 1
                     WI.realDiv sym one e

type BVOp2 sym w = (KnownNat w, 1 <= w) =>
  WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.SymBV sym w)

type FPOp2 sym fpp =
  KnownRepr WT.FloatPrecisionRepr fpp =>
  WI.SymExpr sym (WT.BaseFloatType fpp) ->
  WI.SymExpr sym (WT.BaseFloatType fpp) ->
  IO (WI.SymExpr sym (WT.BaseFloatType fpp))

type RealOp2 sym =
  WI.SymExpr sym WT.BaseRealType -> WI.SymExpr sym WT.BaseRealType -> IO (WI.SymExpr sym WT.BaseRealType)

type BoolCmp2 sym = WI.Pred sym -> WI.Pred sym -> IO (WI.Pred sym)

type BVCmp2 sym w = (KnownNat w, 1 <= w) => WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.Pred sym)

type FPCmp2 sym fpp =
  KnownRepr WT.FloatPrecisionRepr fpp =>
  WI.SymExpr sym (WT.BaseFloatType fpp) ->
  WI.SymExpr sym (WT.BaseFloatType fpp) ->
  IO (WI.Pred sym)

translateOp2 :: forall sym a b c.
   WI.IsSymExprBuilder sym =>
   CE.Expr c {- ^ Original value we are translating -} ->
   sym ->
   (WI.SymFn sym
       (EmptyCtx ::> WT.BaseRealType ::> WT.BaseRealType)
       WT.BaseRealType)
     {- ^ Pow function -} ->
   (WI.SymFn sym
       (EmptyCtx ::> WT.BaseRealType ::> WT.BaseRealType)
       WT.BaseRealType)
     {- ^ Logb function -} ->
   CE.Op2 a b c ->
   XExpr sym ->
   XExpr sym ->
   IO (XExpr sym)
translateOp2 origExpr sym powFn logbFn op xe1 xe2 = case (op, xe1, xe2) of
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
      powFn' :: FPOp2 sym fpp
      powFn' e1 e2 = do re1 <- WI.floatToReal sym e1
                        re2 <- WI.floatToReal sym e2
                        let args = (Empty :> re1 :> re2)
                        rpow <- WI.applySymFn sym powFn args
                        WI.realToFloat sym knownRepr fpRM rpow
  (CE.Logb _, xe1, xe2) -> fpOp logbFn' xe1 xe2
    where
      logbFn' :: FPOp2 sym fpp
      logbFn' e1 e2 = do re1 <- WI.floatToReal sym e1
                         re2 <- WI.floatToReal sym e2
                         let args = (Empty :> re1 :> re2)
                         rpow <- WI.applySymFn sym logbFn args
                         WI.realToFloat sym knownRepr fpRM rpow
  (CE.Eq _, xe1, xe2) -> cmp (WI.eqPred sym) (WI.bvEq sym) (WI.floatEq sym) xe1 xe2
  (CE.Ne _, xe1, xe2) -> cmp neqPred bvNeq fpNeq xe1 xe2
    where
      neqPred :: BoolCmp2 sym
      neqPred e1 e2 = do e <- WI.eqPred sym e1 e2
                         WI.notPred sym e
      bvNeq :: forall w . BVCmp2 sym w
      bvNeq e1 e2 = do e <- WI.bvEq sym e1 e2
                       WI.notPred sym e
      fpNeq :: forall fpp . FPCmp2 sym fpp
      fpNeq e1 e2 = do e <- WI.floatEq sym e1 e2
                       WI.notPred sym e
  (CE.Le _, xe1, xe2) -> numCmp (WI.bvSle sym) (WI.bvUle sym) (WI.floatLe sym) xe1 xe2
  (CE.Ge _, xe1, xe2) -> numCmp (WI.bvSge sym) (WI.bvUge sym) (WI.floatGe sym) xe1 xe2
  (CE.Lt _, xe1, xe2) -> numCmp (WI.bvSlt sym) (WI.bvUlt sym) (WI.floatLt sym) xe1 xe2
  (CE.Gt _, xe1, xe2) -> numCmp (WI.bvSgt sym) (WI.bvUgt sym) (WI.floatGt sym) xe1 xe2

  (CE.BwAnd _, xe1, xe2) -> bvOp (WI.bvAndBits sym) (WI.bvAndBits sym) xe1 xe2
  (CE.BwOr  _, xe1, xe2) -> bvOp (WI.bvOrBits sym)  (WI.bvOrBits sym)  xe1 xe2
  (CE.BwXor _, xe1, xe2) -> bvOp (WI.bvXorBits sym) (WI.bvXorBits sym) xe1 xe2

  -- Note: For both shift operators, we are interpreting the shifter as an
  -- unsigned bitvector regardless of whether it is a word or an int.
  -- TODO, does this match the intended semantics?
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
      (XArray xes, XWord32 ix) -> buildIndexExpr sym ix xes
      _ -> panic ["Unexpected values in index operation", show xe1, show xe2]
  _ -> panic [ "Unexpected values in binary op: "++ show (CP.ppExpr origExpr), show xe1, show xe2 ]

  where
    numOp :: (forall w . BVOp2 sym w)
          -> (forall fpp . FPOp2 sym fpp)
          -> XExpr sym
          -> XExpr sym
          -> IO (XExpr sym)
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
      _ -> panic ["Unexpected values in numOp", show xe1, show xe2]

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
      _ -> panic ["Unexpected values in bvOp", show xe1, show xe2]

    fpOp :: (forall fpp . FPOp2 sym fpp)
         -> XExpr sym
         -> XExpr sym
         -> IO (XExpr sym)
    fpOp op xe1 xe2 = case (xe1, xe2) of
      (XFloat e1, XFloat e2) -> XFloat <$> op e1 e2
      (XDouble e1, XDouble e2) -> XDouble <$> op e1 e2
      _ -> panic ["Unexpected values in fpOp", show xe1, show xe2]

    cmp :: BoolCmp2 sym
        -> (forall w . BVCmp2 sym w)
        -> (forall fpp . FPCmp2 sym fpp)
        -> XExpr sym
        -> XExpr sym
        -> IO (XExpr sym)
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
      _ -> panic ["Unexpected values in cmp", show xe1, show xe2 ]

    numCmp :: (forall w . BVCmp2 sym w)
           -> (forall w . BVCmp2 sym w)
           -> (forall fpp . FPCmp2 sym fpp)
           -> XExpr sym
           -> XExpr sym
           -> IO (XExpr sym)
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
      _ -> panic ["Unexpected values in numCmp", show xe1, show xe2]

translateOp3 :: forall sym a b c d .
  WI.IsExprBuilder sym =>
  CE.Expr d {- ^ Original value we are translating -} ->
  sym ->
  CE.Op3 a b c d ->
  XExpr sym ->
  XExpr sym ->
  XExpr sym ->
  IO (XExpr sym)
translateOp3 _ sym (CE.Mux _) (XBool te) xe1 xe2 = mkIte sym te xe1 xe2
translateOp3 origExpr _sym _op xe1 xe2 xe3 =
  panic ["Unexpected values in 3-place op"
        , show (CP.ppExpr origExpr), show xe1, show xe2, show xe3
        ]

-- | Build a mux tree for array indexing.
--   TODO, add special case for concrete index value.
buildIndexExpr :: forall sym n.
  (1 <= n, WI.IsExprBuilder sym) =>
  sym ->
  WI.SymBV sym 32 {- ^ Index -} ->
  V.Vector n (XExpr sym) {- ^ Elements -} ->
  IO (XExpr sym)
buildIndexExpr sym ix = loop 0
  where
    loop :: forall n'. (1 <= n') => Word32 -> V.Vector n' (XExpr sym) -> IO (XExpr sym)
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

mkIte ::
  WI.IsExprBuilder sym =>
  sym ->
  WI.Pred sym ->
  XExpr sym ->
  XExpr sym ->
  IO (XExpr sym)
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
      (XEmptyArray, XEmptyArray) -> return XEmptyArray
      (XArray xes1, XArray xes2) ->
        case V.length xes1 `testEquality` V.length xes2 of
          Just Refl -> XArray <$> V.zipWithM (mkIte sym pred) xes1 xes2
          Nothing -> panic ["Array length mismatch in ite", show (V.length xes1), show (V.length xes2)]
      _ -> panic ["Unexpected values in ite", show xe1, show xe2]

castOp ::
  WI.IsExprBuilder sym =>
  CE.Expr a {- ^ Original value we are translating -} ->
  sym ->
  CT.Type a {- ^ Type we are casting to -} ->
  XExpr sym {- ^ Value to cast -} ->
  IO (XExpr sym)
castOp origExpr sym tp xe = case (xe, tp) of
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
   (XInt64 e, CT.Float)   -> XFloat  <$> WI.sbvToFloat sym knownRepr fpRM e
   (XInt32 e, CT.Float)   -> XFloat  <$> WI.sbvToFloat sym knownRepr fpRM e
   (XInt16 e, CT.Float)   -> XFloat  <$> WI.sbvToFloat sym knownRepr fpRM e
   (XInt8 e, CT.Float)    -> XFloat  <$> WI.sbvToFloat sym knownRepr fpRM e

   -- unsigned integer to float
   (XWord64 e, CT.Float)  -> XFloat  <$> WI.bvToFloat sym knownRepr fpRM e
   (XWord32 e, CT.Float)  -> XFloat  <$> WI.bvToFloat sym knownRepr fpRM e
   (XWord16 e, CT.Float)  -> XFloat  <$> WI.bvToFloat sym knownRepr fpRM e
   (XWord8 e, CT.Float)   -> XFloat  <$> WI.bvToFloat sym knownRepr fpRM e

   -- signed integer to double
   (XInt64 e, CT.Double)  -> XDouble <$> WI.sbvToFloat sym knownRepr fpRM e
   (XInt32 e, CT.Double)  -> XDouble <$> WI.sbvToFloat sym knownRepr fpRM e
   (XInt16 e, CT.Double)  -> XDouble <$> WI.sbvToFloat sym knownRepr fpRM e
   (XInt8 e, CT.Double)   -> XDouble <$> WI.sbvToFloat sym knownRepr fpRM e

   -- unsigned integer to double
   (XWord64 e, CT.Double) -> XDouble <$> WI.bvToFloat sym knownRepr fpRM e
   (XWord32 e, CT.Double) -> XDouble <$> WI.bvToFloat sym knownRepr fpRM e
   (XWord16 e, CT.Double) -> XDouble <$> WI.bvToFloat sym knownRepr fpRM e
   (XWord8 e, CT.Double)  -> XDouble <$> WI.bvToFloat sym knownRepr fpRM e

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

   _ -> panic [ "Could not compute cast", show (CP.ppExpr origExpr), show xe ]
