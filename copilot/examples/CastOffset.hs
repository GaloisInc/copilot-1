{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
module Main (main) where

import Copilot.Compile.C99
import qualified Copilot.Core.Operators as Core
import qualified Copilot.Language.Stream as Stream
import Foreign.Storable
import GHC.Generics
import Language.Copilot

data Ethhdr = Ethhdr
  { ethhdrDest :: Field "dest" (Array 6 Word8)
  , ethhdrSrc :: Field "src" (Array 6 Word8)
  , ethhdrType :: Field "type" Word16
  , ethhdrHDest :: Field "h_dest" (Array 6 Word8)
  , ethhdrHSource :: Field "h_source" (Array 6 Word8)
  , ethhdrHProto :: Field "h_proto" Word16
  } deriving Generic

-- Boilerplate code, could be automated
instance Storable Ethhdr where
  sizeOf _ = 6 * sizeOf (undefined :: Word8) -- dest
           + 6 * sizeOf (undefined :: Word8) -- src
           + sizeOf (undefined :: Word16) -- type
           + 6 * sizeOf (undefined :: Word8) -- h_dest
           + 6 * sizeOf (undefined :: Word8) -- h_source
           + sizeOf (undefined :: Word16) -- h_proto

instance Struct Ethhdr where
  typeName = typeNameDefault
  toValues = toValuesDefault
  updateField = updateFieldDefault

instance Typed Ethhdr where
  typeOf = typeOfDefault

data Iphdr = Iphdr
  { iphdrProtocol :: Field "protocol" Word32
  -- Other fields go here...
  } deriving Generic

-- Boilerplate code, could be automated
instance Storable Iphdr where
  sizeOf _ = sizeOf (undefined :: Word32) -- protocol

instance Struct Iphdr where
  typeName = typeNameDefault
  toValues = toValuesDefault
  updateField = updateFieldDefault

instance Typed Iphdr where
  typeOf = typeOfDefault

data Icmphdr = Icmphdr
  { icmphdrCode :: Field "type" Word8
  -- Other fields go here...
  } deriving Generic

-- Boilerplate code, could be automated
instance Storable Icmphdr where
  sizeOf _ = sizeOf (undefined :: Word8) -- code

instance Struct Icmphdr where
  typeName = typeNameDefault
  toValues = toValuesDefault
  updateField = updateFieldDefault

instance Typed Icmphdr where
  typeOf = typeOfDefault

bufferToIphdr :: Stream (Array 5000 Word8) -> Stream Iphdr
bufferToIphdr = arbitraryCast (fromIntegral (sizeOf (undefined :: Ethhdr)))

bufferToIcmphdr :: Stream (Array 5000 Word8) -> Stream Icmphdr
bufferToIcmphdr = arbitraryCast (fromIntegral (sizeOf (undefined :: Ethhdr) + sizeOf (undefined :: Iphdr)))

arbitraryCast :: (Typed a, Typed b) => Word64 -> Stream a -> Stream b
arbitraryCast offset = Stream.Op1 (Core.Cast (Just offset) undefined typeOf typeOf)

buffers :: Stream (Array 5000 Word8)
buffers = extern "buffers" Nothing

iphdrs :: Stream Iphdr
iphdrs = bufferToIphdr buffers

icmphdrs :: Stream Icmphdr
icmphdrs = bufferToIcmphdr buffers

go :: Stream Icmphdr
go =
  if iphdrs # iphdrProtocol == 0
    then icmphdrs ## icmphdrCode =: 42
    else icmphdrs

hackyExtern1 :: Stream Iphdr
hackyExtern1 = extern "hacky_extern1" Nothing

hackyExtern2 :: Stream Icmphdr
hackyExtern2 = extern "hacky_extern2" Nothing

spec :: Spec
spec = trigger "update_header" true [arg go, arg hackyExtern1, arg hackyExtern2]

main :: IO ()
main = do
  spec' <- reify spec
  compile "casts" spec'
