{-# LANGUAGE Arrows #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

-- This code is adapted from code in
-- https://github.com/ivanperez-keera/Yampa/tree/develop/yampa-test
-- Copyright (c) 2017, Iván Perez
-- License: https://github.com/ivanperez-keera/Yampa/blob/develop/yampa-test/LICENSE
-- Adapted by Miguel Negrão 2022
module LiveCoding.FRP.Test where

import Control.Category (id)
import Data.Functor.Identity (Identity (runIdentity))
import LiveCoding
  ( Arrow (arr, first, (&&&)),
    Cell,
    runReaderC',
    step,
    (>>^),
  )
import LiveCoding.FRP (ClockInfoT, Time)
import System.Random (Random)
import Test.QuickCheck
  ( Arbitrary (arbitrary),
    Positive (getPositive),
    Property,
    Testable,
    choose,
    forAll,
    listOf,
    vectorOf,
  )
import Prelude hiding (id)

boolStream :: ([(Time, Bool)] -> t) -> Bool -> [(Positive Time, Bool)] -> t
boolStream prop' (initialValue :: Bool) (samples :: [(Positive Time, Bool)]) =
  prop' ((0, initialValue) : (first getPositive <$> samples))

withStream :: forall a t. ([(Time, a)] -> t) -> a -> [(Positive Time, a)] -> t
withStream prop' initialValue samples =
  prop' ((0, initialValue) : (first getPositive <$> samples))

withStreamRange ::
  forall a t.
  (Show a, Testable t, Random a, Num a) =>
  (a, a) ->
  ([(a, Int)] -> t) ->
  Property
withStreamRange range prop' = forAll (listOf ((,) <$> choose range <*> arbitrary)) $
  \samples (initialValue :: Int) ->
    prop' ((0, initialValue) : samples)

withStreamRangeSized ::
  forall a t.
  (Show a, Testable t, Random a, Num a) =>
  (a, a) ->
  Int ->
  ([(a, Int)] -> t) ->
  Property
withStreamRangeSized range size prop' = forAll (vectorOf size ((,) <$> choose range <*> arbitrary)) $
  \samples (initialValue :: Int) ->
    prop' ((0, initialValue) : samples)

withStreamFixedDelta ::
  forall a prop.
  (Testable prop, Arbitrary a, Show a) =>
  Int ->
  Time ->
  ([(Time, a)] -> prop) ->
  Property
withStreamFixedDelta size delta prop' = forAll (vectorOf size arbitrary) $ \(x : xs) ->
  prop' ((0, x) : ((delta,) <$> xs))

withStreamFixedDeltaTime ::
  forall a prop.
  (Testable prop, Arbitrary a, Show a) =>
  Time ->
  Time ->
  ([(Time, a)] -> prop) ->
  Property
withStreamFixedDeltaTime time delta prop' = forAll (vectorOf (ceiling (time / delta)) arbitrary) $ \(x : xs) ->
  prop' ((0, x) : ((delta,) <$> xs))

streamFixedDeltaZeros :: (Num a, Num b) => a -> Int -> [(a, b)]
streamFixedDeltaZeros timeStep size = (0, 0) : replicate size (timeStep, 0)

prop :: (Cell (ClockInfoT Identity) a b, a -> b -> Bool) -> TPred a
prop (a, b) = SP ((arr snd &&& runReaderC' a) >>^ uncurry b)

propId :: TPred Bool
propId = prop (id, \_ b -> b)

prop_always_equal ::
  Eq a1 =>
  Cell (ClockInfoT Identity) a2 a1 ->
  Cell (ClockInfoT Identity) a2 a1 ->
  TPred a2
prop_always_equal a b = Always $ prop (a &&& b, const (uncurry (==)))

prop_always_similar ::
  (Ord a1, Num a1) =>
  a1 ->
  Cell (ClockInfoT Identity) a2 a1 ->
  Cell (ClockInfoT Identity) a2 a1 ->
  TPred a2
prop_always_similar margin cell1 cell2 =
  Always $ prop (cell1 &&& cell2, const similar)
  where
    similar (x, y) = abs (x - y) <= margin

type ClockCell a b = Cell Identity (Time, a) b

type ClockCell' a b = Cell (ClockInfoT Identity) a b

-- | Type representing future-time linear temporal logic predicates with until
-- and next.
data TPred a where
  SP :: ClockCell a Bool -> TPred a
  And :: TPred a -> TPred a -> TPred a
  Or :: TPred a -> TPred a -> TPred a
  Not :: TPred a -> TPred a
  Implies :: TPred a -> TPred a -> TPred a
  Always :: TPred a -> TPred a
  Eventually :: TPred a -> TPred a
  Next :: TPred a -> TPred a
  Until :: TPred a -> TPred a -> TPred a

-- | A stream of samples, with their sampling times.
type SignalSampleStream a = [(Time, a)]

-- | Evaluates a temporal predicate at time t=0 with a concrete sample stream.
--
-- Returns 'True' if the temporal proposition is currently true (at time = 0).
evalT :: TPred a -> SignalSampleStream a -> Bool
evalT (SP sf) = \stream -> firstSample sf stream
evalT (And t1 t2) = \stream -> evalT t1 stream && evalT t2 stream
evalT (Or t1 t2) = \stream -> evalT t1 stream || evalT t2 stream
evalT (Not t1) = \stream -> not (evalT t1 stream)
evalT (Implies t1 t2) = \stream -> not (evalT t1 stream) || evalT t2 stream
evalT (Always t1) = \stream -> case stream of
  [] -> True
  xs -> evalT t1 xs && evalT (Next (Always t1)) xs
evalT (Eventually t1) = \stream -> case stream of
  [] -> False -- False because this is the final value in the recursion of Eventually
  (dt, a) : as -> evalT t1 stream || evalT (tauApp (Eventually t1) a dt) as
evalT (Until t1 t2) = \stream ->
  (evalT t1 stream && evalT (Next (Until t1 t2)) stream)
    || evalT t2 stream
evalT (Next t1) = \stream -> case stream of
  [] -> True -- This is important. It determines how
  -- always and next behave at the
  -- end of the stream, which affects that is and isn't
  -- a tautology. It should be reviewed very carefully.
  (dt, a) : as -> evalT (tauApp t1 a dt) as

-- | Tau-application (transportation to the future)
tauApp :: TPred a -> a -> Time -> TPred a
tauApp pred sample dtime = tPredMap (\sf -> nextCell sf sample dtime) pred

-- | Apply a transformation to the leaves (to the SFs)
tPredMap :: (ClockCell a Bool -> ClockCell a Bool) -> TPred a -> TPred a
tPredMap f (SP sf) = SP (f sf)
tPredMap f (And t1 t2) = And (tPredMap f t1) (tPredMap f t2)
tPredMap f (Or t1 t2) = Or (tPredMap f t1) (tPredMap f t2)
tPredMap f (Not t1) = Not (tPredMap f t1)
tPredMap f (Implies t1 t2) = Implies (tPredMap f t1) (tPredMap f t2)
tPredMap f (Always t1) = Always (tPredMap f t1)
tPredMap f (Eventually t1) = Eventually (tPredMap f t1)
tPredMap f (Next t1) = Next (tPredMap f t1)
tPredMap f (Until t1 t2) = Until (tPredMap f t1) (tPredMap f t2)

firstSample ::
  ClockCell a Bool ->
  SignalSampleStream a ->
  Bool
firstSample cell (sample : _) = fst $ runIdentity $ step cell sample
firstSample _ [] = error "firstSample needs a list of samples"

nextCell ::
  ClockCell a b ->
  a ->
  Time ->
  ClockCell a b
nextCell cell sample dtime = snd $ runIdentity $ step cell (dtime, sample)
