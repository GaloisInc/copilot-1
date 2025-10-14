{-# LANGUAGE Safe #-}

-- |
-- Copyright: (c) 2011 National Institute of Aerospace / Galois, Inc.
--
-- Custom functions to report error messages to users.
module Copilot.Compile.C99.Error
    ( impossible
    , zeroLengthArray
    )
  where

-- | Report an error due to a bug in Copilot.
impossible :: String -- ^ Name of the function in which the error was detected.
           -> String -- ^ Name of the package in which the function is located.
           -> a
impossible function package =
  error $ "Impossible error in function "
    ++ function ++ ", in package " ++ package
    ++ ". Please file an issue at "
    ++ "https://github.com/Copilot-Language/copilot/issues"
    ++ " or email the maintainers at <ivan.perezdominguez@nasa.gov>"

-- | Report an error when attempting to compile a zero-length array to C99.
--
-- C99 does not support zero-length arrays, so Copilot cannot compile
-- specifications that use them.
zeroLengthArray :: a
zeroLengthArray =
  error $ "copilot-c99: Cannot compile zero-length arrays to C99.\n"
       ++ "C99 does not support arrays of length 0.\n"
       ++ "Please ensure all arrays in your Copilot specification have length >= 1."
