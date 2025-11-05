{-# LANGUAGE NoImplicitPrelude #-}
module Main (main) where

import qualified Copilot.Compile.Bluespec as Bluespec
import Language.Copilot

nans :: Stream Float
nans = [read "NaN"] ++ nans

infinities :: Stream Float
infinities = [inf, -inf] ++ infinities
  where
    inf :: Float
    inf = read "Infinity"

zeroes :: Stream Float
zeroes = [0, -0] ++ zeroes

spec :: Spec
spec =
  trigger "rtf" true [arg nans, arg infinities, arg zeroes]

main :: IO ()
main = do
  interpret 2 spec
  spec' <- reify spec
  Bluespec.compile "Floats" spec'
