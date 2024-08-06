{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies           #-}
module Copilot.Language.Operators.Projection
  ( Projectable (..)
  ) where

import Copilot.Language.Stream (Stream)

infixl 8 =:
infixl 8 =$

class Projectable d s t | d s -> t where

  data Projection d s t

  (=:) :: Projection d s t -> Stream t -> Stream d

  (=$) :: Projection d s t -> (Stream t -> Stream t) -> Stream d
