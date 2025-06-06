{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
-- | Test copilot-core:Copilot.Core.Type.
module Test.Copilot.Core.Type where

-- External imports
import Data.Int                             (Int16, Int32, Int64, Int8)
import Data.Maybe                           (isJust)
import Data.Proxy                           (Proxy (..))
import Data.Type.Equality                   (TestEquality (..), testEquality,
                                             (:~:) (..))
import Data.Word                            (Word16, Word32, Word64, Word8)
import GHC.TypeLits                         (sameSymbol)
import Prelude                              as P
import Test.Framework                       (Test, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck                      (Gen, Property, arbitrary, elements,
                                             expectFailure, forAll, forAllBlind,
                                             property, shuffle, (==>))

-- Internal imports: library modules being tested
import Copilot.Core.Type       (Field (..), SimpleType (..), Struct (..),
                                Type (..), Typed, UType (..), Value (..),
                                accessorName, fieldName, simpleType, typeLength,
                                typeOf, typeSize)
import Copilot.Core.Type.Array (Array)

-- | All unit tests for copilot-core:Copilot.Core.Type.
tests :: Test.Framework.Test
tests =
  testGroup "Copilot.Core.Type"
    [ testProperty "simpleType preserves inequality"
        testSimpleTypesInequality
    ,  testProperty "reflexivity of equality of simple types"
        testSimpleTypesEqualityReflexive
    , testProperty "symmetry of equality of simple types"
        testSimpleTypesEqualitySymmetric
    , testProperty "transitivity of equality of simple types"
        testSimpleTypesEqualityTransitive
    , testProperty "uniqueness of equality of simple types"
        testSimpleTypesEqualityUniqueness
    , testProperty "typeLength matches array size for 1-dimensional arrays"
        testTypeLength1
    , testProperty "typeLength matches array size for 2-dimensional arrays"
        testTypeLength2
    , testProperty "typeSize matches full array size for 1-dimensional arrays"
        testTypeSize1
    , testProperty "typeSize matches full array size for 2-dimensional arrays"
        testTypeSize2
    , testProperty "equality of types"
        testUTypesEqualitySymmetric
    , testProperty "equality of utype"
        testUTypesEq
    , testProperty "inequality of utype"
        testUTypesInequality
    , testProperty "inequality of utype via typeOf"
        testUTypesTypeOfInequality
    , testProperty "inequality of different types"
        testTypesInequality
    , testProperty "fieldName matches field name (positive)"
        testFieldNameOk
    , testProperty "fieldName matches field name (negative)"
        testFieldNameFail
    , testProperty "Show field name"
        testShowField
    , testProperty "Show struct"
        testShowStruct
    , testProperty "Update struct"
        testUpdateStruct
    , testProperty "Update struct"
        testUpdateStructFail
    , testProperty "accessorName matches field name (positive)"
        testAccessorNameOk
    , testProperty "accessorName matches field name (negative)"
        testAccessorNameFail
    , testProperty "typeName matches struct type name (positive)"
        testTypeNameOk
    , testProperty "typeName matches struct type name (negative)"
        testTypeNameFail
    ]

-- | Test that the function simpleTypes preserves inequality, that is, it
-- returns different values for different types. This test is limited; we do
-- not test structs or arrays.
testSimpleTypesInequality :: Property
testSimpleTypesInequality = forAllBlind twoDiffTypes $ \(t1, t2) ->
    t1 /= t2
  where
    twoDiffTypes :: Gen (SimpleType, SimpleType)
    twoDiffTypes = do
      shuffled <- shuffle diffTypes
      case shuffled of
        (t1:t2:_) -> return (t1, t2)
        _         -> return (SBool, SBool)

    -- | A list of types that should all be different.
    diffTypes :: [SimpleType]
    diffTypes = [ simpleType Bool
                , simpleType Int8
                , simpleType Int16
                , simpleType Int32
                , simpleType Int64
                , simpleType Word8
                , simpleType Word16
                , simpleType Word32
                , simpleType Word64
                , simpleType Float
                , simpleType Double
                , simpleType (Array Int8 :: Type (Array 3 Int8))
                , simpleType (Struct (S (Field 0) (Field 0)))
                ]

-- | Test that the equality relation for simple types is reflexive.
testSimpleTypesEqualityReflexive :: Property
testSimpleTypesEqualityReflexive =
  forAllBlind (elements simpleTypes) $ \t ->
    t == t

-- | Test that the equality relation for simple types is symmetric.
testSimpleTypesEqualitySymmetric :: Property
testSimpleTypesEqualitySymmetric =
  forAllBlind (elements simpleTypes) $ \t1 ->
  forAllBlind (elements simpleTypes) $ \t2 ->
    t1 == t2 ==> t2 == t1

-- | Test that the equality relation for simple types is transitive.
testSimpleTypesEqualityTransitive :: Property
testSimpleTypesEqualityTransitive =
  forAllBlind (elements simpleTypes) $ \t1 ->
  forAllBlind (elements simpleTypes) $ \t2 ->
  forAllBlind (elements simpleTypes) $ \t3 ->
    (t1 == t2 && t2 == t3) ==> (t1 == t3)

-- | Test that each type is only equal to itself.
testSimpleTypesEqualityUniqueness :: Property
testSimpleTypesEqualityUniqueness =
  forAllBlind (shuffle simpleTypes) $ \(t:ts) ->
    notElem t ts

-- | Simple types tested.
simpleTypes :: [SimpleType]
simpleTypes =
  [ SBool
  , SInt8
  , SInt16
  , SInt32
  , SInt64
  , SWord8
  , SWord16
  , SWord32
  , SWord64
  , SFloat
  , SDouble
  , SStruct
  , SArray Int8
  , SArray Int16
  ]

-- | Test that the length of an array is as expected.
testTypeLength1 :: Property
testTypeLength1 = property $ typeLength a == 3
  where
    a :: Type (Array 3 Int8)
    a = Array Int8

-- | Test that the length of an multi-dimensional array is as expected.
testTypeLength2 :: Property
testTypeLength2 = property $ typeLength a == 3
  where
    a :: Type (Array 3 (Array 12 Int8))
    a = Array (Array Int8)

-- | Test that the size of an array is as expected.
testTypeSize1 :: Property
testTypeSize1 = property $ typeLength a == 3
  where
    a :: Type (Array 3 Int8)
    a = Array Int8

-- | Test that the size of a multi-dimensional array is as expected (flattens
-- the array).
testTypeSize2 :: Property
testTypeSize2 = property $ typeSize a == 36
  where
    a :: Type (Array 3 (Array 12 Int8))
    a = Array (Array Int8)

-- | Test that equality is symmetric for UTypes via testEquality.
testUTypesEqualitySymmetric :: Property
testUTypesEqualitySymmetric =
  forAllBlind (elements utypes) $ \(UType t1) -> testEquality t1 t1 == Just Refl

-- | Test that testEquality implies equality for UTypes.
testUTypesEq :: Property
testUTypesEq =
  forAllBlind (elements utypes) $ \t@(UType t1) -> (testEquality t1 t1 == Just Refl) ==> t == t

-- | Test that any two different UTypes are not equal.
--
-- This function pre-selects two UTypes from a list of different UTypes, which
-- guarantees that they will be different.
testUTypesInequality :: Property
testUTypesInequality = forAllBlind twoDiffTypes $ \(t1, t2) ->
    t1 /= t2
  where
    twoDiffTypes :: Gen (UType, UType)
    twoDiffTypes = do
      shuffled <- shuffle utypes
      case shuffled of
        (t1:t2:_) -> return (t1, t2)
        _         -> return (UType Bool, UType Bool)

-- | Test that any two different Types are not equal.
--
-- This function pre-selects two Types from a list of different UTypes, which
-- guarantees that they will be different.
testTypesInequality :: Property
testTypesInequality = forAllBlind twoDiffTypes $ \(UType t1, UType t2) ->
    testEquality t1 t2 == Nothing
  where
    twoDiffTypes :: Gen (UType, UType)
    twoDiffTypes = do
      shuffled <- shuffle utypes
      case shuffled of
        (t1:t2:_) -> return (t1, t2)
        _         -> return (UType Bool, UType Bool)

-- | Different UTypes.
utypes :: [UType]
utypes =
    [ UType Bool
    , UType Int8
    , UType Int16
    , UType Int32
    , UType Int64
    , UType Word8
    , UType Word16
    , UType Word32
    , UType Word64
    , UType Float
    , UType Double
    , UType a1
    , UType a2
    , UType a3
    , UType a4
    , UType b1
    , UType b2
    , UType b3
    , UType b4
    , UType c
    ]
  where
    a1 :: Type (Array 3 Int8)
    a1 = Array Int8

    a2 :: Type (Array 4 Int8)
    a2 = Array Int8

    a3 :: Type (Array 5 Int8)
    a3 = Array Int8

    a4 :: Type (Array 6 Int8)
    a4 = Array Int8

    b1 :: Type (Array 3 Int16)
    b1 = Array Int16

    b2 :: Type (Array 4 Int16)
    b2 = Array Int16

    b3 :: Type (Array 5 Int16)
    b3 = Array Int16

    b4 :: Type (Array 6 Int16)
    b4 = Array Int16

    c :: Type S
    c = Struct (S (Field 0) (Field 0))

-- | Test that any two different UTypes are not equal.
--
-- This function pre-selects two UTypes from a list of different UTypes built
-- via the function typeOf, which guarantees that they will be different.
testUTypesTypeOfInequality :: Property
testUTypesTypeOfInequality = forAllBlind twoDiffTypes $ \(t1@(UType t1'), t2@(UType t2')) ->
    -- The seqs are important: otherwise, the coverage goes down drastically
    -- because the typeOf function is not really executed.
    t1' `seq` t2' `seq` t1 /= t2
  where
    twoDiffTypes :: Gen (UType, UType)
    twoDiffTypes = do
      shuffled <- shuffle uTypesTypeOf
      case shuffled of
        (t1:t2:_) -> t1 `seq` t2 `seq` return (t1, t2)
        _         -> return (UType Bool, UType Bool)

-- | Different UTypes, produced by using the function typeOf.
uTypesTypeOf :: [UType]
uTypesTypeOf =
    [ UType (typeOf :: Type Bool)
    , UType (typeOf :: Type Int8)
    , UType (typeOf :: Type Int16)
    , UType (typeOf :: Type Int32)
    , UType (typeOf :: Type Int64)
    , UType (typeOf :: Type Word8)
    , UType (typeOf :: Type Word16)
    , UType (typeOf :: Type Word32)
    , UType (typeOf :: Type Word64)
    , UType (typeOf :: Type Float)
    , UType (typeOf :: Type Double)
    , UType (typeOf :: Type (Array 3 Int8))
    , UType (typeOf :: Type (Array 3 Int16))
    , UType (typeOf :: Type (Array 3 Int32))
    , UType (typeOf :: Type (Array 3 Int64))
    , UType (typeOf :: Type (Array 3 Word8))
    , UType (typeOf :: Type (Array 3 Word16))
    , UType (typeOf :: Type (Array 3 Word32))
    , UType (typeOf :: Type (Array 3 Word64))
    , UType (typeOf :: Type (Array 3 Double))
    , UType (typeOf :: Type (Array 3 Float))
    , UType (typeOf :: Type S)
    ]

-- | Test the fieldName function (should succeed).
testFieldNameOk :: Property
testFieldNameOk = forAll arbitrary $ \k1 ->
                  forAll arbitrary $ \k2 ->
    fieldName (s1 (S (Field k1) (Field k2))) == s1FieldName
  where
    s1FieldName = "field1"

-- | Test the fieldName function (should fail).
testFieldNameFail :: Property
testFieldNameFail = expectFailure $ property $
    fieldName (s1 sampleS) == s1FieldName
  where
    sampleS     = S (Field 0) (Field 0)
    s1FieldName = "Field"

-- | Test showing a field of a struct.
testShowField :: Property
testShowField = forAll arbitrary $ \k ->
  show (s1 (S (Field k) (Field 0))) == ("field1:" ++ show k)

-- | Test showing a struct.
testShowStruct :: Property
testShowStruct = forAll arbitrary $ \k1 ->
                 forAll arbitrary $ \k2 ->
  show (S (Field k1) (Field k2)) == "<field1:" ++ show k1 ++ ",field2:" ++ show k2 ++ ">"

-- | Test showing a struct.
testUpdateStruct :: Property
testUpdateStruct =
   forAll arbitrary $ \k1 ->
   forAll arbitrary $ \k2 ->
     let f :: Field "field1" Int8
         f = Field k2
         v :: Value Int8
         v = Value Int8 f
     in unField (s1 (updateField (S (Field k1) (Field 0)) v)) == k2

 where
   unField (Field x) = x

-- | Test showing a struct.
testUpdateStructFail :: Property
testUpdateStructFail = expectFailure $
   forAll arbitrary $ \k1 ->
   forAll arbitrary $ \k3 ->
     let f :: Field "field" Int8
         f = Field k3
         v :: Value Int8
         v = Value Int8 f
     in unField (s3 (updateField (S3 (Field k1)) v)) == k3

 where
   unField (Field x) = x

-- | Test the accessorName of a field of a struct (should succeed).
testAccessorNameOk :: Property
testAccessorNameOk = property $
    accessorName s1 == s1FieldName
  where
    s1FieldName = "field1"

-- | Test the accessorName of a field of a struct (should fail).
testAccessorNameFail :: Property
testAccessorNameFail = expectFailure $ property $
    accessorName s1 == s1FieldName
  where
    s1FieldName = "Field1"

-- | Test the typeName of a struct (should succeed).
testTypeNameOk :: Property
testTypeNameOk = property $
     typeName sampleS == s1TypeName

  where

    sampleS :: S
    sampleS = S (Field 0) (Field 0)

    s1TypeName :: String
    s1TypeName = "S"

-- | Test the typeName of a struct (should fail).
testTypeNameFail :: Property
testTypeNameFail = expectFailure $ property $
     typeName sampleS == s1TypeName

  where

    sampleS :: S
    sampleS = S (Field 0) (Field 0)

    s1TypeName :: String
    s1TypeName = "s"

-- | Auxiliary struct defined for testing purposes.
data S = S { s1 :: Field "field1" Int8, s2 :: Field "field2" Word8 }

instance Struct S where
  typeName _ = "S"

  toValues s = [ Value Int8 (s1 s), Value Word8 (s2 s) ]

  updateField s (Value fieldTy (field :: Field fieldName a))
    | Just Refl <- sameSymbol (Proxy @"field1") (Proxy @fieldName)
    , Just Refl <- testEquality Int8 fieldTy
    = s { s1 = field }
    | Just Refl <- sameSymbol (Proxy @"field2") (Proxy @fieldName)
    , Just Refl <- testEquality Word8 fieldTy
    = s { s2 = field }
    | otherwise
    = error $ "Unexpected field: " P.++ show field

instance Typed S where
  typeOf = Struct (S (Field 0) (Field 0))

-- | Auxiliary struct defined for testing purposes.
data S3 = S3 { s3 :: Field "field" Int8 }

instance Struct S3 where
  typeName _ = "S3"

  toValues s = [ Value Int8 (s3 s) ]

instance Typed S3 where
  typeOf = Struct (S3 (Field 0))
