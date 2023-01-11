# The design of `copilot-bluespec`

This document provides an overview of how the `copilot-bluespec` library
compiles a Copilot specification to a Bluespec program. We assume that you
already have some familiarity with core Copilot concepts such as streams,
triggers, externs, etc.

## Bluespec overview

Bluespec is a high-level hardware design language (HDL). Bluespec comes with a
compiler, `bsc`, as well as its own simulator, which allows users to run
Bluespec programs easily. Bluespec also supports compiling to Verilog.

There are two different syntaxes for the Bluespec language: Bluespec Haskell
(BH) and Bluespec SystemVerilog (BSV). Bluespec Haskell (also known as Bluespec
Classic), the older of the two syntaxes, is a more functional, high-level
syntax that is heavily inspired by the Haskell programming language. Bluespec
SystemVerilog, which was created later, more closely SystemVerilog and targets
hardware design engineers who are more familiar with SystemVerilog's syntax.
Both syntaxes are merely front-ends for the same language, and programs written
in one syntax can be converted to the other.

The `copilot-bluespec` library compiles to Bluespec Haskell rather than
Bluespec SystemVerilog. This is primarily because BH's Haskell-like syntax is a
closer fit to how Copilot is structured, which makes the design of the compiler
simpler.

## A small example

To get a sense for how `copilot-bluespec` works, let us compile a simple
Copilot specification down to Bluespec. Our specification will declare a stream
containing the Fibonacci numbers, along with some triggers that will fire if a
Fibonacci number is even or odd:

```hs
module Main (main) where

import qualified Prelude as P ()

import Language.Copilot
import Copilot.Compile.Bluespec

fibs :: Stream Word32
fibs = [1, 1] ++ (fibs + drop 1 fibs)

evenStream :: Stream Word32 -> Stream Bool
evenStream n = (n `mod` constant 2) == constant 0

oddStream :: Stream Word32 -> Stream Bool
oddStream n = not (evenStream n)

spec :: Spec
spec = do
  trigger "even" (evenStream fibs) [arg fibs]
  trigger "odd"  (oddStream fibs) [arg fibs]

main :: IO ()
main = do
  spec' <- reify spec
  compile "Fibs" spec'
```

Note that the only parts of this program that are `copilot-bluespec` specific
are:

1. The `import Copilot.Compile.Bluespec` statement, and
2. The call to `compile "Fibs" spec'` in `main`. This will compile the Copilot
   specification to a Bluespec program named `Fibs.bs`.

Running this program will generate `Fibs.bs`, whose contents will look roughly
like the following:

TODO RGS: Update the code below once the codegen is finalized

```bluespec
package Fibs where

import Vector

interface FibsIfc =
  even :: UInt 32 -> Action
  odd :: UInt 32 -> Action

mkFibs :: Module FibsIfc -> Module Empty
mkFibs ifcMod = do
  ifc <- ifcMod
  module
    s0_0 :: Reg (UInt 32) <- mkReg 1
    s0_1 :: Reg (UInt 32) <- mkReg 1
    let s0 :: Vector 2 (Reg (UInt 32))
        s0 = update (update newVector 0 s0_0) 1 s0_1
    s0_idx :: Reg (Bit 64) <- mkReg 0

    let s0_get :: Bit 64 -> UInt 32
        s0_get x = (select s0 ((s0_idx + x) % 2))._read;

        s0_gen :: UInt 32
        s0_gen = s0_get 0 + s0_get 1

        even_guard :: Bool
        even_guard =
          (s0_get 0 % 2) == 0

        odd_guard :: Bool
        odd_guard =
          not (s0_get 0 % 2 == 0)

    rules
      "even": when even_guard ==>
        ifc.even (s0_get 0)

      "odd:": when odd_guard ==>
        ifc.odd (s0_get 0)

      "step": when True ==> do
        select s0 s0_idx := s0_gen
        s0_idx := (s0_idx + 1) % 2
```

(Note that the actual code is machine-generated and somewhat more difficult to
read. We have cleaned up the code slightly to make it easier to understand.)

The `mkFibs` function orchestrates everything in the spec. It returns a module,
which can be thought of as a generator of hardware objects. It also accepts
another module as an argument, which is parameterized by the `FibsIfc`
interface. An interface defines _methods_, which control how the environment
interacts with the module. There are two interfaces in use in `mkFibs`:

* `Empty`, a standard interface with no methods. `Empty` is typically used
  in top-level modules.
* `FibsIfc`, a generated interface whose methods correspond to the names of
  the triggers in the Copilot spec.

In a larger application, a Copilot user would instantiate `mkFibs` with a
`FibsIfc` module that describes what should happen when the `even` and `odd`
triggers fire. `FibsIfc` contains everything that the user must supply;
everything else is handled within the module that `mkFibs` returns.

Here is an example of a larger application might look like:

TODO RGS: Update the code below once the codegen is finalized

```bluespec
package Top where

import Fibs

fibsIfc :: Module FibsIfc
fibsIfc =
  module
    interface
      even x =
        $display "Even Fibonacci number: %0d" x

      odd x =
        $display "Odd  Fibonacci number: %0d" x

mkTop :: Module Empty
mkTop = mkFibs fibsIfc
```

`mkTop` is the top-level module that we will use as a program entrypoint. The
only interesting thing that it does is instantiate `mkFibs` with a custom
`FibsIfc`, where `even` and `odd` are defined to display a custom message
whenever an even or odd Fibonacci number is encountered, respectively.

We can run `mkTop` by using Bluespec's simulator like so:

```
$ bsc -sim -g mkTop -u Top.bs
checking package dependencies
compiling Top.bs
code generation for mkTop starts
Elaborated module file created: mkTop.ba
All packages are up to date.

$ bsc -sim -e mkTop -o mkTop.exe
Bluesim object created: mkTop.{h,o}
Bluesim object created: model_mkTop.{h,o}
Simulation shared library created: mkTop.exe.so
Simulation executable created: mkTop.exe

$ ./mkTop.exe -m 10
Odd  Fibonacci number: 1
Odd  Fibonacci number: 1
Even Fibonacci number: 2
Odd  Fibonacci number: 3
Odd  Fibonacci number: 5
Even Fibonacci number: 8
Odd  Fibonacci number: 13
Odd  Fibonacci number: 21
Even Fibonacci number: 34
```

We pass `-m 10` to instruct Bluespec's simulator to only run for 10 clock
cycles. Note that the first clock cycle does not fire any rules, which is why
only 9 messages are printed.

## Streams

Much like in `copilot-c99`, `copilot-bluespec` translates each stream
declaration into a ring buffer. More concretely, it translates a Stream into a
`Vector n (Reg t)`, where `n` is the minimum number of elements needed to later
values in the stream and `t` is the stream's element type. `Reg` is a register,
which stores a value that can be read from and written to. As time advances, we
will update the `Reg`s in the ring buffer with later values in the stream.

The `Fibs.bs` example above contains exactly one stream, which is created at
the top of the `mkFibs` function:

```bluespec
    s0_0 :: Reg (UInt 32) <- mkReg 1
    s0_1 :: Reg (UInt 32) <- mkReg 1
    let s0 :: Vector 2 (Reg (UInt 32))
        s0 = update (update newVector 0 s0_0) 1 s0_1
    s0_idx :: Reg (Bit 64) <- mkReg 0
```

Here, `s0_idx`, tracks the index of the next stream element to be updated.
`mkFibs` then defines several functions in terms of `s0` and `s0_idx`, which
are then used in the rules.

(Commentary: a ring buffer is not the only way we could translate a stream to
Bluespec. Bluespec also has a `MIMO` (many-in, many-out) queue that is _almost_
suitable for our needs, but it comes with an unusual restriction that it must
have a minimum size of 2 elements. There exist Copilot streams that only
require one element of storage, so we would have to special-case these streams
if we wanted to use a `MIMO`.)

## Triggers

TODO RGS

## Rules

The rules govern what actions are performed during each cycle. There
are three actions in the `Fibs.hs` example:

```bluespec
    rules
      "even": when even_guard ==>
        ifc.even (s0_get 0)

      "odd:": when odd_guard ==>
        ifc.odd (s0_get 0)

      "step": when True ==> do
        select s0 s0_idx := s0_gen
        s0_idx := (s0_idx + 1) % 2
```

# Notes

## Structs

TODO RGS: We have to do some name mangling here to give struct names capital
letters. Is there a better way?

## Floating-point numbers

TODO RGS: Hoo boy
