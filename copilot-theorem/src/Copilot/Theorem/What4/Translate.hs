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

import qualified What4.Expr.Builder             as WB
import qualified What4.Expr.GroundEval          as WG
import qualified What4.Interface                as WI
import qualified What4.InterpretedFloatingPoint as WFP
import qualified What4.BaseTypes                as WT
import qualified What4.SpecialFunctions         as WSF

import Control.Monad.State
import qualified Data.Binary.IEEE754 as IEEE754
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
import LibBF ( BigFloat
             , bfToDouble
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

  -- | A list of side conditions that must be true in order for all
  --   applications of partial functions (e.g., 'Div') to be well defined.
  sidePreds :: [WI.Pred sym]
  }

newtype TransM sym a = TransM { unTransM :: StateT (TransState sym) IO a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadFail
           , MonadIO
           , MonadState (TransState sym)
           )

-- | Add a side condition originating from an application of a partial
-- function.
addSidePred :: WI.Pred sym -> TransM sym ()
addSidePred newPred = modify $ \st -> st{ sidePreds = newPred : sidePreds st }

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

runTransM :: CS.Spec -> TransM sym a -> IO a
runTransM spec m =
  do -- Build up initial translation state
     let streamMap = Map.fromList $
           (\stream -> (CS.streamId stream, stream)) <$> CS.specStreams spec
         st = TransState
              { mentionedExternals = mempty
              , externVars = mempty
              , streamValues = mempty
              , streams = streamMap
              , sidePreds = []
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
  XFloat      :: WI.SymExpr sym (WFP.SymInterpretedFloatType sym WFP.SingleFloat) -> XExpr sym
  XDouble     :: WI.SymExpr sym (WFP.SymInterpretedFloatType sym WFP.DoubleFloat) -> XExpr sym
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

valFromExpr ::
  forall sym t st fm.
  (sym ~ WB.ExprBuilder t st (WB.Flags fm), KnownRepr WB.FloatModeRepr fm) =>
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
    Some . CopilotValue CT.Float <$>
      iFloatGroundEval WFP.SingleFloatRepr e
                       (realToFrac . fst . bfToDouble NearEven)
                       fromRational
                       (IEEE754.wordToFloat . fromInteger . BV.asUnsigned)
  XDouble e ->
    Some . CopilotValue CT.Double <$>
      iFloatGroundEval WFP.DoubleFloatRepr e
                       (fst . bfToDouble NearEven)
                       fromRational
                       (IEEE754.wordToDouble . fromInteger . BV.asUnsigned)
  _ -> error "valFromExpr unhandled case"
  where
    fromBV :: forall a w . Num a => BV.BV w -> a
    fromBV = fromInteger . BV.asUnsigned

    fromSBV :: forall a w . (1 <= w, KnownNat w, Num a) => BV.BV w -> a
    fromSBV = fromInteger . BV.asSigned knownRepr

    iFloatGroundEval ::
      forall fi r.
      WFP.FloatInfoRepr fi ->
      WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi) ->
      (BigFloat -> r) ->
      (Rational -> r) ->
      (forall w. BV.BV w -> r) ->
      IO r
    iFloatGroundEval _ e ieeeK realK uninterpK =
      case (knownRepr :: WB.FloatModeRepr fm) of
        WB.FloatIEEERepr          -> ieeeK <$> WG.groundEval ge e
        WB.FloatRealRepr          -> realK <$> WG.groundEval ge e
        WB.FloatUninterpretedRepr -> uninterpK <$> WG.groundEval ge e

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
  deriving Eq

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

-- | If an 'XExpr' is a bitvector expression, use it to generate a side
-- condition involving an application of a partial function.
-- Otherwise, do nothing.
addBVSidePred1 ::
  WI.IsExprBuilder sym =>
  XExpr sym ->
  (forall w. 1 <= w => WI.SymBV sym w -> NatRepr w -> BVSign -> IO (WI.Pred sym)) ->
  TransM sym ()
addBVSidePred1 xe makeSidePred =
  case asBVExpr xe of
    Just (SomeBVExpr e w sgn _) -> do
      sidePred <- liftIO $ makeSidePred e w sgn
      addSidePred sidePred
    Nothing -> pure ()

-- | If two 'XExpr's are both bitvector expressions of the same type, use them
-- to generate a side condition involving an application of a partial function.
-- Otherwise, do nothing.
addBVSidePred2 ::
  WI.IsExprBuilder sym =>
  XExpr sym ->
  XExpr sym ->
  (forall w. 1 <= w => WI.SymBV sym w -> WI.SymBV sym w -> NatRepr w -> BVSign -> IO (WI.Pred sym)) ->
  TransM sym ()
addBVSidePred2 xe1 xe2 makeSidePred =
  case (asBVExpr xe1, asBVExpr xe2) of
    (Just (SomeBVExpr e1 w1 sgn1 _), Just (SomeBVExpr e2 w2 sgn2 _))
      |  Just Refl <- testEquality w1 w2
      ,  sgn1 == sgn2
      -> do sidePred <- liftIO $ makeSidePred e1 e2 w1 sgn1
            addSidePred sidePred
    _ -> pure ()

-- | Translate a constant expression by creating a what4 literal and packaging
-- it up into an 'XExpr'.
translateConstExpr :: forall sym a.
  WFP.IsInterpretedFloatExprBuilder sym =>
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
  CT.Float -> XFloat <$> WFP.iFloatLitSingle sym a
  CT.Double -> XDouble <$> WFP.iFloatLitDouble sym a
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
  WFP.IsInterpretedFloatSymExprBuilder sym =>
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
  CT.Float -> XFloat <$> WFP.freshFloatConstant sym (WI.safeSymbol nm) WFP.SingleFloatRepr
  CT.Double -> XDouble <$> WFP.freshFloatConstant sym (WI.safeSymbol nm) WFP.DoubleFloatRepr
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
getStreamValue :: WFP.IsInterpretedFloatSymExprBuilder sym =>
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
getExternConstant :: WFP.IsInterpretedFloatSymExprBuilder sym =>
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
  WFP.IsInterpretedFloatSymExprBuilder sym =>
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
       translateOp1 e sym op xe1
  CE.Op2 op e1 e2 ->
    do xe1 <- translateExpr sym localEnv e1 offset
       xe2 <- translateExpr sym localEnv e2 offset
       translateOp2 e sym op xe1 xe2
  CE.Op3 op e1 e2 e3 ->
    do xe1 <- translateExpr sym localEnv e1 offset
       xe2 <- translateExpr sym localEnv e2 offset
       xe3 <- translateExpr sym localEnv e3 offset
       translateOp3 e sym op xe1 xe2 xe3
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

type FPOp1 sym fi =
  WFP.FloatInfoRepr fi ->
  WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi) ->
  IO (WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi))

translateOp1 :: forall sym a b.
  WFP.IsInterpretedFloatExprBuilder sym =>
  CE.Expr b {- ^ Original value we are translating -} ->
  sym ->
  CE.Op1 a b ->
  XExpr sym ->
  TransM sym (XExpr sym)
translateOp1 origExpr sym op xe = case (op, xe) of
  (CE.Not, XBool e) -> liftIO $ XBool <$> WI.notPred sym e
  (CE.Not, _) -> panic ["Expected bool", show xe]
  (CE.Abs _, xe) -> do addBVSidePred1 xe $ \e w _ -> do
                         -- The argument should not be INT_MIN
                         bvIntMin <- liftIO $ WI.bvLit sym w (BV.minSigned w)
                         eqIntMin <- liftIO $ WI.bvEq sym e bvIntMin
                         WI.notPred sym eqIntMin
                       liftIO $ numOp bvAbs fpAbs xe
    where
      bvAbs :: BVOp1 sym w
      bvAbs e = do zero <- WI.bvLit sym knownNat (BV.zero knownNat)
                   e_neg <- WI.bvSlt sym e zero
                   neg_e <- WI.bvSub sym zero e
                   WI.bvIte sym e_neg neg_e e
      fpAbs :: forall fi . FPOp1 sym fi
      fpAbs _fiRepr e = WFP.iFloatAbs @_ @fi sym e

  (CE.Sign _, xe) -> liftIO $ numOp bvSign fpSign xe
    where
      -- Implement `signum x` as `x > 0 ? 1 : (x < 0 ? -1 : x)`.
      -- This matches how copilot-c99 translates Sign to C code.
      bvSign :: BVOp1 sym w
      bvSign e = do zero <- WI.bvLit sym knownRepr (BV.zero knownNat)
                    neg_one <- WI.bvLit sym knownNat (BV.mkBV knownNat (-1))
                    pos_one <- WI.bvLit sym knownNat (BV.mkBV knownNat 1)
                    e_neg <- WI.bvSlt sym e zero
                    e_pos <- WI.bvSgt sym e zero
                    t <- WI.bvIte sym e_neg neg_one e
                    WI.bvIte sym e_pos pos_one t
      fpSign :: forall fi . FPOp1 sym fi
      fpSign fiRepr  e = do zero    <- fpLit fiRepr   0.0
                            neg_one <- fpLit fiRepr (-1.0)
                            pos_one <- fpLit fiRepr   1.0
                            e_neg <- WFP.iFloatLt @_ @fi sym e zero
                            e_pos <- WFP.iFloatGt @_ @fi sym e zero
                            t <- WFP.iFloatIte @_ @fi sym e_neg neg_one e
                            WFP.iFloatIte @_ @fi sym e_pos pos_one t

  -- We do not track any side conditions for floating-point operations
  -- (see Note [Side conditions for floating-point operations]), but we will
  -- make a note of which operations have partial inputs.

  -- The argument should not be zero
  (CE.Recip _, xe) -> liftIO $ fpOp recip xe
    where
      recip :: forall fi . FPOp1 sym fi
      recip fiRepr e = do one <- fpLit fiRepr 1.0
                          WFP.iFloatDiv @_ @fi sym fpRM one e
  -- The argument is should not be less than -0
  (CE.Sqrt _, xe) -> liftIO $ fpOp (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatSqrt @_ @fi sym fpRM) xe
  -- The argument should not cause the result to overflow or underlow
  (CE.Exp _, xe) -> liftIO $ fpSpecialOp WSF.Exp xe
  -- The argument should not be negative or zero
  (CE.Log _, xe) -> liftIO $ fpSpecialOp WSF.Log xe
  -- The argument should not be infinite
  (CE.Sin _, xe) -> liftIO $ fpSpecialOp WSF.Sin xe
  -- The argument should not be infinite
  (CE.Cos _, xe) -> liftIO $ fpSpecialOp WSF.Cos xe
  -- The argument should not be infinite, nor should it cause the result to overflow
  (CE.Tan _, xe) -> liftIO $ fpSpecialOp WSF.Tan xe
  -- The argument should not cause the result to overflow
  (CE.Sinh _, xe) -> liftIO $ fpSpecialOp WSF.Sinh xe
  -- The argument should not cause the result to overflow
  (CE.Cosh _, xe) -> liftIO $ fpSpecialOp WSF.Cosh xe
  (CE.Tanh _, xe) -> liftIO $ fpSpecialOp WSF.Tanh xe
  -- The argument should not be outside the range [-1, 1]
  (CE.Asin _, xe) -> liftIO $ fpSpecialOp WSF.Arcsin xe
  -- The argument should not be outside the range [-1, 1]
  (CE.Acos _, xe) -> liftIO $ fpSpecialOp WSF.Arccos xe
  (CE.Atan _, xe) -> liftIO $ fpSpecialOp WSF.Arctan xe
  (CE.Asinh _, xe) -> liftIO $ fpSpecialOp WSF.Arcsinh xe
  -- The argument should not be less than 1
  (CE.Acosh _, xe) -> liftIO $ fpSpecialOp WSF.Arccosh xe
  -- The argument should not be less than or equal to -1,
  -- nor should it be greater than or equal to +1
  (CE.Atanh _, xe) -> liftIO $ fpSpecialOp WSF.Arctanh xe
  -- The argument should not cause the result to overflow
  (CE.Ceiling _, xe) -> liftIO $ fpOp (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatRound @_ @fi sym WI.RTP) xe
  -- The argument should not cause the result to overflow
  (CE.Floor _, xe) -> liftIO $ fpOp (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatRound @_ @fi sym WI.RTN) xe

  (CE.BwNot _, xe) -> liftIO $ case xe of
    XBool e -> XBool <$> WI.notPred sym e
    _ -> bvOp (WI.bvNotBits sym) xe

  (CE.Cast _ tp, _) -> liftIO $ castOp origExpr sym tp xe
  (CE.GetField (CT.Struct s) _ftp extractor, XStruct xes) -> do
    let fieldNameRepr = fieldName (extractor undefined)
    let structFieldNameReprs = valueName <$> CT.toValues s
    let mIx = elemIndex (Some fieldNameRepr) structFieldNameReprs
    case mIx of
      Just ix -> return $ xes !! ix
      Nothing -> panic ["Could not find field " ++ show fieldNameRepr, show s ]
  (CE.GetField{}, _) -> unexpectedValue "get-field operation"
  where
    numOp :: (forall w . BVOp1 sym w)
          -> (forall fi . FPOp1 sym fi)
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

    fpSpecialOp :: WSF.SpecialFunction (EmptyCtx ::> WSF.R)
                -> XExpr sym -> IO (XExpr sym)
    fpSpecialOp fn = fpOp (\fiRepr -> WFP.iFloatSpecialFunction1 sym fiRepr fn)

    fpLit :: forall fi.
             WFP.FloatInfoRepr fi ->
             (forall frac. Fractional frac => frac) ->
             IO (WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi))
    fpLit fiRepr fracLit =
      case fiRepr of
        WFP.SingleFloatRepr -> WFP.iFloatLitSingle sym fracLit
        WFP.DoubleFloatRepr -> WFP.iFloatLitDouble sym fracLit
        _ -> panic ["Expected single- or double-precision float", show fiRepr]

    unexpectedValue :: forall m x. (Panic.HasCallStack, MonadIO m) => String -> m x
    unexpectedValue op =
      panic [ "Unexpected value in " ++ op ++ ": " ++ show (CP.ppExpr origExpr)
            , show xe ]

type BVOp2 sym w = (KnownNat w, 1 <= w) =>
  WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.SymBV sym w)

type FPOp2 sym fi =
  WFP.FloatInfoRepr fi ->
  WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi) ->
  WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi) ->
  IO (WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi))

type BoolCmp2 sym = WI.Pred sym -> WI.Pred sym -> IO (WI.Pred sym)

type BVCmp2 sym w = (KnownNat w, 1 <= w) => WI.SymBV sym w -> WI.SymBV sym w -> IO (WI.Pred sym)

type FPCmp2 sym fi =
  WFP.FloatInfoRepr fi ->
  WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi) ->
  WI.SymExpr sym (WFP.SymInterpretedFloatType sym fi) ->
  IO (WI.Pred sym)

translateOp2 :: forall sym a b c.
   WFP.IsInterpretedFloatSymExprBuilder sym =>
   CE.Expr c {- ^ Original value we are translating -} ->
   sym ->
   CE.Op2 a b c ->
   XExpr sym ->
   XExpr sym ->
   TransM sym (XExpr sym)
translateOp2 origExpr sym op xe1 xe2 = case (op, xe1, xe2) of
  (CE.And, XBool e1, XBool e2) -> liftIO $ XBool <$> WI.andPred sym e1 e2
  (CE.Or, XBool e1, XBool e2) -> liftIO $ XBool <$> WI.orPred sym e1 e2
  (CE.And, _, _) -> unexpectedValues "and operation"
  (CE.Or, _, _) -> unexpectedValues "or operation"
  (CE.Add _, xe1, xe2) -> do addBVSidePred2 xe1 xe2 $ \e1 e2 _ sgn ->
                               -- The arguments should not result in
                               -- signed overflow or underflow
                               case sgn of
                                 Signed -> do
                                   (wrap, _) <- WI.addSignedOF sym e1 e2
                                   WI.notPred sym wrap
                                 Unsigned -> pure $ WI.truePred sym

                             liftIO $
                               numOp (WI.bvAdd sym)
                                     (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatAdd @_ @fi sym fpRM)
                                     xe1 xe2
  (CE.Sub _, xe1, xe2) -> do addBVSidePred2 xe1 xe2 $ \e1 e2 _ sgn ->
                               -- The arguments should not result in
                               -- signed overflow or underflow
                               case sgn of
                                 Signed -> do
                                   (wrap, _) <- WI.subSignedOF sym e1 e2
                                   WI.notPred sym wrap
                                 Unsigned -> pure $ WI.truePred sym

                             liftIO $
                               numOp (WI.bvSub sym)
                                     (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatSub @_ @fi sym fpRM)
                                     xe1 xe2
  (CE.Mul _, xe1, xe2) -> do addBVSidePred2 xe1 xe2 $ \e1 e2 _ sgn ->
                               -- The arguments should not result in
                               -- signed overflow or underflow
                               case sgn of
                                 Signed -> do
                                   (wrap, _) <- WI.mulSignedOF sym e1 e2
                                   WI.notPred sym wrap
                                 Unsigned -> pure $ WI.truePred sym

                             liftIO $
                               numOp (WI.bvMul sym)
                                     (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatMul @_ @fi sym fpRM)
                                     xe1 xe2
  (CE.Mod _, xe1, xe2) -> do -- The second argument should not be zero
                             addBVSidePred1 xe2 $ \e2 _ _ -> WI.bvIsNonzero sym e2
                             liftIO $ bvOp (WI.bvSrem sym) (WI.bvUrem sym) xe1 xe2
  (CE.Div _, xe1, xe2) -> do -- The second argument should not be zero
                             addBVSidePred1 xe2 $ \e2 _ _ -> WI.bvIsNonzero sym e2
                             liftIO $ bvOp (WI.bvSdiv sym) (WI.bvUdiv sym) xe1 xe2

  -- We do not track any side conditions for floating-point operations
  -- (see Note [Side conditions for floating-point operations]), but we will
  -- make a note of which operations have partial inputs.

  -- The second argument should not be zero
  (CE.Fdiv _, xe1, xe2) -> liftIO $ fpOp (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatDiv @_ @fi sym fpRM)
                                         xe1 xe2
  -- None of the following should happen:
  --
  -- * The first argument is negative, and the second argument is a finite noninteger
  --
  -- * The first argument is zero, and the second argument is negative
  --
  -- * The arguments cause the result to overflow
  --
  -- * The arguments cause the result to underflow
  (CE.Pow _, xe1, xe2) -> liftIO $ fpSpecialOp WSF.Pow xe1 xe2
  -- The second argument should not be negative or zero
  (CE.Logb _, xe1, xe2) -> liftIO $ fpOp logbFn xe1 xe2
    where
      logbFn :: forall fi . FPOp2 sym fi
      -- Implement logb(e1,e2) as log(e2)/log(e1). This matches how copilot-c99
      -- translates Logb to C code.
      logbFn fiRepr e1 e2 = do re1 <- WFP.iFloatSpecialFunction1 sym fiRepr WSF.Log e1
                               re2 <- WFP.iFloatSpecialFunction1 sym fiRepr WSF.Log e2
                               WFP.iFloatDiv @_ @fi sym fpRM re2 re1
  (CE.Atan2 _, xe1, xe2) -> liftIO $ fpSpecialOp WSF.Arctan2 xe1 xe2
  (CE.Eq _, xe1, xe2) -> liftIO $
                         cmp (WI.eqPred sym) (WI.bvEq sym)
                             (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatEq @_ @fi sym)
                             xe1 xe2
 -- TODO, I think we can simplify this and pull the `not` outside
  (CE.Ne _, xe1, xe2) -> liftIO $ cmp neqPred bvNeq fpNeq xe1 xe2
    where
      neqPred :: BoolCmp2 sym
      neqPred e1 e2 = do e <- WI.eqPred sym e1 e2
                         WI.notPred sym e
      bvNeq :: forall w . BVCmp2 sym w
      bvNeq e1 e2 = do e <- WI.bvEq sym e1 e2
                       WI.notPred sym e
      fpNeq :: forall fi . FPCmp2 sym fi
      fpNeq _ e1 e2 = do e <- WFP.iFloatEq @_ @fi sym e1 e2
                         WI.notPred sym e
  (CE.Le _, xe1, xe2) -> liftIO $
                         numCmp (WI.bvSle sym) (WI.bvUle sym)
                                (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatLe @_ @fi sym)
                                xe1 xe2
  (CE.Ge _, xe1, xe2) -> liftIO $
                         numCmp (WI.bvSge sym) (WI.bvUge sym)
                                (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatGe @_ @fi sym)
                                xe1 xe2
  (CE.Lt _, xe1, xe2) -> liftIO $
                         numCmp (WI.bvSlt sym) (WI.bvUlt sym)
                                (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatLt @_ @fi sym)
                                xe1 xe2
  (CE.Gt _, xe1, xe2) -> liftIO $
                         numCmp (WI.bvSgt sym) (WI.bvUgt sym)
                                (\(_ :: WFP.FloatInfoRepr fi) -> WFP.iFloatGt @_ @fi sym)
                                xe1 xe2

  (CE.BwAnd _, xe1, xe2) -> liftIO $ bvOp (WI.bvAndBits sym) (WI.bvAndBits sym) xe1 xe2
  (CE.BwOr  _, xe1, xe2) -> liftIO $ bvOp (WI.bvOrBits sym)  (WI.bvOrBits sym)  xe1 xe2
  (CE.BwXor _, xe1, xe2) -> liftIO $ bvOp (WI.bvXorBits sym) (WI.bvXorBits sym) xe1 xe2

  -- Note: For both shift operators, we are interpreting the shifter as an
  -- unsigned bitvector regardless of whether it is a word or an int.
  -- TODO, does this match the intended semantics?
  (CE.BwShiftL _ _, xe1, xe2) -> do
    Just (SomeBVExpr e1 w1 sgn1 ctor1) <- return $ asBVExpr xe1
    Just (SomeBVExpr e2 w2 _    _    ) <- return $ asBVExpr xe2

    e2' <- liftIO $ case testNatCases w1 w2 of
        NatCaseLT LeqProof -> WI.bvTrunc sym w1 e2
        NatCaseEQ -> return e2
        NatCaseGT LeqProof -> WI.bvZext sym w1 e2
    res <- liftIO $ WI.bvShl sym e1 e2'

    -- The second argument should not be greater than or equal to the bit width
    wBV <- liftIO $ WI.bvLit sym w1 $ BV.width w1
    notTooLarge <- liftIO $ WI.bvUlt sym e2' wBV
    addSidePred notTooLarge

    case sgn1 of
      Unsigned -> do
        -- Non-zero bits should not be shifted out
        otherDirection <- liftIO $ WI.bvLshr sym res e2'
        noWrap <- liftIO $ WI.bvEq sym e1 otherDirection
        addSidePred noWrap
      Signed -> do
        -- Bits that disagree with the sign bit should not be shifted out
        otherDirection <- liftIO $ WI.bvAshr sym res e2'
        noWrap <- liftIO $ WI.bvEq sym e1 otherDirection
        addSidePred noWrap

    return $ ctor1 res
  (CE.BwShiftR _ _, xe1, xe2) -> do
    Just (SomeBVExpr e1 w1 sgn1 ctor1) <- return $ asBVExpr xe1
    Just (SomeBVExpr e2 w2 _    _    ) <- return $ asBVExpr xe2

    e2' <- liftIO $ case testNatCases w1 w2 of
      NatCaseLT LeqProof -> WI.bvTrunc sym w1 e2
      NatCaseEQ -> return e2
      NatCaseGT LeqProof -> WI.bvZext sym w1 e2

    -- The second argument should not be greater than or equal to the bit width
    wBV <- liftIO $ WI.bvLit sym w1 $ BV.width w1
    notTooLarge <- liftIO $ WI.bvUlt sym e2' wBV
    addSidePred notTooLarge

    liftIO $ fmap ctor1 $ case sgn1 of
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
      (XArray xes, XWord32 ix) -> do
        -- The second argument should not be out of bounds (i.e., greater than
        -- or equal to the length of the array)
        xesLenBV <- liftIO $ WI.bvLit sym knownNat $ BV.mkBV knownNat
                           $ toInteger $ V.lengthInt xes
        inRange <- liftIO $ WI.bvUlt sym ix xesLenBV
        addSidePred inRange

        liftIO $ buildIndexExpr sym ix xes
      _ -> unexpectedValues "index operation"

  where
    numOp :: (forall w . BVOp2 sym w)
          -> (forall fi . FPOp2 sym fi)
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
      (XFloat e1, XFloat e2)-> XFloat <$> fpOp WFP.SingleFloatRepr e1 e2
      (XDouble e1, XDouble e2)-> XDouble <$> fpOp WFP.DoubleFloatRepr e1 e2
      _ -> unexpectedValues "numOp"

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

    fpSpecialOp :: WSF.SpecialFunction (EmptyCtx ::> WSF.R ::> WSF.R)
                -> XExpr sym -> XExpr sym -> IO (XExpr sym)
    fpSpecialOp fn = fpOp (\fiRepr -> WFP.iFloatSpecialFunction2 sym fiRepr fn)

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
      (XInt32 e1, XInt32 e2)-> XBool <$> bvOp e1 e2
      (XInt64 e1, XInt64 e2)-> XBool <$> bvOp e1 e2
      (XWord8 e1, XWord8 e2)-> XBool <$> bvOp e1 e2
      (XWord16 e1, XWord16 e2)-> XBool <$> bvOp e1 e2
      (XWord32 e1, XWord32 e2)-> XBool <$> bvOp e1 e2
      (XWord64 e1, XWord64 e2)-> XBool <$> bvOp e1 e2
      (XFloat e1, XFloat e2)-> XBool <$> fpOp WFP.SingleFloatRepr e1 e2
      (XDouble e1, XDouble e2)-> XBool <$> fpOp WFP.DoubleFloatRepr e1 e2
      _ -> unexpectedValues "cmp"

    numCmp :: (forall w . BVCmp2 sym w)
           -> (forall w . BVCmp2 sym w)
           -> (forall fi . FPCmp2 sym fi)
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
      (XFloat e1, XFloat e2)-> XBool <$> fpOp WFP.SingleFloatRepr e1 e2
      (XDouble e1, XDouble e2)-> XBool <$> fpOp WFP.DoubleFloatRepr e1 e2
      _ -> unexpectedValues "numCmp"

    unexpectedValues :: forall m x. (Panic.HasCallStack, MonadIO m) => String -> m x
    unexpectedValues op =
      panic [ "Unexpected values in " ++ op ++ ": " ++ show (CP.ppExpr origExpr)
            , show xe1, show xe2 ]

translateOp3 :: forall sym a b c d .
  WFP.IsInterpretedFloatExprBuilder sym =>
  CE.Expr d {- ^ Original value we are translating -} ->
  sym ->
  CE.Op3 a b c d ->
  XExpr sym ->
  XExpr sym ->
  XExpr sym ->
  TransM sym (XExpr sym)
translateOp3 origExpr sym op xe1 xe2 xe3 = case (op, xe1, xe2, xe3) of
  (CE.Mux _, XBool te, xe1, xe2) -> liftIO $ mkIte sym te xe1 xe2
  (CE.Mux _, _, _, _) -> unexpectedValues "mux operation"

  where
    unexpectedValues :: forall m x. (Panic.HasCallStack, MonadIO m) => String -> m x
    unexpectedValues op =
      panic [ "Unexpected values in " ++ op ++ ":"
            , show (CP.ppExpr origExpr), show xe1, show xe2, show xe3
            ]

{-
Note [Side conditions for floating-point operations]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We do not currently track side conditions for floating-point operations for two
reasons, as they are unlikely to matter. A typical client of copilot-theorem
will likely treat floating-point operations as uninterpreted functions, and
side conditions involving uninterpreted functions are very unlikely to be
helpful except in very specific circumstances. In case we revisit this decision
later, we make a note of which floating-point operations could potentially
track side conditions as comments (but without implementing them).
-}

-- | Build a mux tree for array indexing.
--   TODO, add special case for concrete index value.
buildIndexExpr :: forall sym n.
  (1 <= n, WFP.IsInterpretedFloatExprBuilder sym) =>
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
  WFP.IsInterpretedFloatExprBuilder sym =>
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
      (XFloat e1, XFloat e2) -> XFloat <$> WFP.iFloatIte @_ @WFP.SingleFloat sym pred e1 e2
      (XDouble e1, XDouble e2) -> XDouble <$> WFP.iFloatIte @_ @WFP.DoubleFloat sym pred e1 e2
      (XStruct xes1, XStruct xes2) ->
        XStruct <$> zipWithM (mkIte sym pred) xes1 xes2
      (XEmptyArray, XEmptyArray) -> return XEmptyArray
      (XArray xes1, XArray xes2) ->
        case V.length xes1 `testEquality` V.length xes2 of
          Just Refl -> XArray <$> V.zipWithM (mkIte sym pred) xes1 xes2
          Nothing -> panic ["Array length mismatch in ite", show (V.length xes1), show (V.length xes2)]
      _ -> panic ["Unexpected values in ite", show xe1, show xe2]

castOp ::
  WFP.IsInterpretedFloatExprBuilder sym =>
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
   (XInt64 e, CT.Float)   -> XFloat  <$> WFP.iSBVToFloat sym WFP.SingleFloatRepr fpRM e
   (XInt32 e, CT.Float)   -> XFloat  <$> WFP.iSBVToFloat sym WFP.SingleFloatRepr fpRM e
   (XInt16 e, CT.Float)   -> XFloat  <$> WFP.iSBVToFloat sym WFP.SingleFloatRepr fpRM e
   (XInt8 e, CT.Float)    -> XFloat  <$> WFP.iSBVToFloat sym WFP.SingleFloatRepr fpRM e

   -- unsigned integer to float
   (XWord64 e, CT.Float)  -> XFloat  <$> WFP.iBVToFloat sym WFP.SingleFloatRepr fpRM e
   (XWord32 e, CT.Float)  -> XFloat  <$> WFP.iBVToFloat sym WFP.SingleFloatRepr fpRM e
   (XWord16 e, CT.Float)  -> XFloat  <$> WFP.iBVToFloat sym WFP.SingleFloatRepr fpRM e
   (XWord8 e, CT.Float)   -> XFloat  <$> WFP.iBVToFloat sym WFP.SingleFloatRepr fpRM e

   -- signed integer to double
   (XInt64 e, CT.Double)  -> XDouble <$> WFP.iSBVToFloat sym WFP.DoubleFloatRepr fpRM e
   (XInt32 e, CT.Double)  -> XDouble <$> WFP.iSBVToFloat sym WFP.DoubleFloatRepr fpRM e
   (XInt16 e, CT.Double)  -> XDouble <$> WFP.iSBVToFloat sym WFP.DoubleFloatRepr fpRM e
   (XInt8 e, CT.Double)   -> XDouble <$> WFP.iSBVToFloat sym WFP.DoubleFloatRepr fpRM e

   -- unsigned integer to double
   (XWord64 e, CT.Double) -> XDouble <$> WFP.iBVToFloat sym WFP.DoubleFloatRepr fpRM e
   (XWord32 e, CT.Double) -> XDouble <$> WFP.iBVToFloat sym WFP.DoubleFloatRepr fpRM e
   (XWord16 e, CT.Double) -> XDouble <$> WFP.iBVToFloat sym WFP.DoubleFloatRepr fpRM e
   (XWord8 e, CT.Double)  -> XDouble <$> WFP.iBVToFloat sym WFP.DoubleFloatRepr fpRM e

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
