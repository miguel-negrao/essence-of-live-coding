* Test with initial state, for one step or many steps
* Test bisimulation with initial state, for many steps (is this really bisimulation?) Allows for stateful property-based testing
* Test with arbitrary state (using boltzmann-samplers)

TODO: insert figure for ghci, insert debugging after cells
\begin{comment}
\begin{code}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}

module LiveCoding.QuickCheck where

-- base
import Control.Arrow
import Control.Monad (foldM)

-- QuickCheck
import Test.QuickCheck
import Test.QuickCheck.Monadic

-- boltzmann-samples
import Boltzmann.Data

-- essenceoflivecoding
import LiveCoding.Cell
\end{code}
\end{comment}

\subsection{Testing with \texttt{QuickCheck}}

Often, a live program, or some of its components,
should satisfy certain correctness properties.
It is good practice in Haskell to build up a program from functions,
and ensure their correctness with property-based testing.
\texttt{QuickCheck} \fxerror{Cite}
is the primeval framework for this.
It generates, type-driven, arbitrary input for a function,
and checks whether given assertions are valid.

In our livecoding approach, programs are not composed of mere functions, but of cells,
and of course we wish to test them in a similar way.
\fxwarning{Say that it's really good to know that your cells do what you expect before you just reload into them. We could need some tooling to call quickcheck before reloading.}

As a simple example,
we wish to assure that \mintinline{haskell}{sumC} will never output negative numbers if only positive numbers are fed into it.
Our test cell is thus defined as:
\begin{code}
testCell :: Cell IO (Positive Int) Bool
testCell
  =   arr getPositive
  >>> sumC
  >>> arr (>= 0)
\end{code}
(The \mintinline{haskell}{IO} monad only occurs here for monomorphization.
But let it be remarked that we will be able to test cells with actual side effects in the same way as pure ones.)

Given a faulty cell, it is impossible to predict how often it must be stepped until it returns an invalid value.
The number of successive inputs has to be variable in a test.
We therefore begin by running a cell repeatedly against a list of inputs, collecting its outputs:
\begin{code}
embed
  :: Monad m
  =>        [a]
  -> Cell  m a b
  ->       m  [b]
embed [] _ = return []
embed (a : as) cell = do
  (b, cell') <- step cell a
  bs <- embed as cell'
  return $ b : bs
\end{code}
If the input type \mintinline{haskell}{a} can be generated arbitrarily,
then so can a list of \mintinline{haskell}{a}s.
Once we have run the cell with the given inputs,
we form the conjunction of the properties tested at each step,
with \texttt{QuickCheck}'s \mintinline{haskell}{conjoin}.
Effects in \mintinline{haskell}{IO} can be embedded in \texttt{QuickCheck}
\fxerror{Cite "Testing Monadic Code with QuickCheck", http://www.cse.chalmers.se/~rjmh/Papers/QuickCheckST.ps} with the monad morphism \mintinline{haskell}{run},
and executed with \mintinline{haskell}{monadicIO}.
Cobbling all those pieces together makes cells testable:
\begin{code}
instance (Arbitrary a, Show a, Testable prop)
  => Testable (Cell IO a prop) where
  property cell = property
    $ \as -> monadicIO $ fmap conjoin
    $ embed as $ hoistCell run cell
\end{code}
Let us execute our test:
\begin{verbatim}
 > quickCheck testCell
+++ OK, passed 100 tests.
\end{verbatim}
Any property that can be expressed as a cell can tested.
This includes a large class of properties.
If we want to ensure that the output of some complex cell \mintinline{haskell}{cell1} satisfies a property depending on the current input and internal state,
we can remodel the relevant portions of its state in a simplified cell and check the property:
\begin{code}
agreesWith
  :: (Arbitrary a, Show a, Testable prop)
  => Cell IO  a  b
  -> Cell IO (a, b) prop
  -> Property
cell1 `agreesWith` cell2 = property $ proc a -> do
  b <- cell1 -<  a
  cell2      -< (a, b)
\end{code}
Along these lines, one can set up stateful property-based testing \cite{ProperTesting} for the livecoding environment.
Similarly, we can check the output of one cell against a reference implementation:
\begin{code}
bisimulates
  :: (Arbitrary a, Show a, Eq b, Show b)
  => Cell IO a b
  -> Cell IO a b
  -> Property
cell1 `bisimulates` cell2 = property $ proc a -> do
  b1 <- cell1 -< a
  b2 <- cell2 -< a
  returnA -< b1 === b2
\end{code}
One shortcoming of the testing methods presented so far is that the cells will always be initialised at the same state.
This can restrict the search space for the cell state greatly,
as it will only reach those states reachable from the initial state after a number of steps,
depending on the size of the .
\begin{code}
reinitialise :: Cell m a b -> Gen (Cell m a b)
reinitialise Cell { .. } = do
  cellState <- generator' 1000
  return Cell { .. }
\end{code}
\fxwarning{Could use quickcheck `counterexamples` on `gshow cellState` somehow}
\fxwarning{How to test freshly migrated state?}
\fxwarning{LTL}
