module Monad where

-- transformers
import Control.Monad.Trans.State.Strict
-- essence-of-live-coding

import Data.Functor.Identity (Identity)
import LiveCoding
import LiveCoding.Cell.Monad.Trans
-- test-framework-quickcheck2
import Test.Framework.Providers.QuickCheck2
import Util

test =
  testProperty
    "State effect"
    CellMigrationSimulation
      { cell1 = flip runStateC (0 :: Int) $ constM (modify (+ 1)),
        cell2 = flip runStateC 23 $ constM (modify (+ 2)),
        input1 = [(), (), ()],
        input2 = [(), (), ()],
        output1 = [((), 1), ((), 2), ((), 3)],
        output2 = [((), 5), ((), 7), ((), 9)]
      }
