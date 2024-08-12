-- Copyright © 2019 National Institute of Aerospace / Galois, Inc.

-- | This is a simple example for arrays. As a program, it does not make much
-- sense, however it shows of the features of arrays nicely.

-- | Enable compiler extension for type-level data, necesary for the array
-- length.

{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RebindableSyntax       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}

module Main where

import Copilot.Compile.C99
import Copilot.Core.Operators
import Copilot.Core.Type
import Copilot.Language.Stream ( Stream (..) )
import GHC.Exts                ( Constraint )
import GHC.TypeLits
import Language.Copilot

-- -- Lets define an array of length 2.
-- -- Make the buffer of the streams 3 elements long.
-- arr :: Stream (Array 2 (Array 2 (Array 2 Bool)))
-- arr = [ array [array [array [True, False], array [False, False]], array [array [True, False], array [False, False]]]
--       , array [array [array [True, False], array [True, False]], array [array [True, False], array [True, False]]]
--       , array [array [array [False, True], array [True, False]], array [array [False, True], array [True, False]]]
--       ] ++ arr

-- Lets define an array of length 2.
-- Make the buffer of the streams 3 elements long.
arr :: Stream (Array 2 (Array 3 Bool))
arr = [ array [array [True, False, True], array [True, False, True]]
      , array [array [False, False, True], array [False, False, True]]
      ] ++ arr

spec :: Spec
spec = do
  -- A trigger that fires 'func' when the first element of 'arr' is True.
  -- It passes the current value of arr as an argument.
  -- The prototype of 'func' would be:
  -- void func (int8_t arg[3]);
  -- let a' = arr !! 0 =: (constant $ array [ array [False, False], array [False, False]])
  -- let a' = arr !! 1 =: (constant $ array [False, True])
  let a' = arr !! 0 =$ \a -> a !! 1 =$ ([True, True] ++)
  -- let a' = arr !! 0 =$ \a -> a !! 0 =$ \b -> b !! 0 =$ not
  trigger "func" true [arg a']

-- Compile the spec
main :: IO ()
main = do
  f' <- reify spec
  compile "array" f'
