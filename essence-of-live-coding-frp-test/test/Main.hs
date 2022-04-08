{-# LANGUAGE Arrows #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

-- Some of this code is adapted from code in
-- https://github.com/ivanperez-keera/Yampa/tree/develop/yampa-test
-- Copyright (c) 2017, Iván Perez
-- License: https://github.com/ivanperez-keera/Yampa/blob/develop/yampa-test/LICENSE

module Main where

import Control.Applicative (Applicative (liftA2))
import Control.Arrow (Arrow (arr), (>>>))
import Control.Arrow.Utils (constantly)
import Control.Category (id)
import Control.Monad.Trans.Reader (ask)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Maybe (isNothing)
import LiveCoding hiding (edge)
import LiveCoding.FRP
import LiveCoding.FRP.Test
import System.Random (Random)
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck
import Prelude hiding (id)

main :: IO ()
main = defaultMain tests

tests :: [Test]
tests =
  [ -- https://link.springer.com/content/pdf/bbm%3A978-3-540-68635-4%2F1.pdf
    testGroup
      "Linear temporal logic"
      [ testProperty "A -> A" $ boolStream $ evalT (Implies propId propId),
        testProperty "not next A -> next not A" $ \(a0 :: Bool) (a1 :: Bool) (samples :: [(Positive Time, Bool)]) ->
          evalT (Implies (Next $ Not propId) (Not $ Next propId)) ((0, a0) : (0.1, a1) : (first getPositive <$> samples)),
        testProperty "not always A -> eventually not A" $ boolStream $ evalT (Implies (Not $ Always propId) (Eventually $ Not propId)),
        testProperty "always A -> next A" $ \(a0 :: Bool) (a1 :: Bool) (samples :: [(Positive Time, Bool)]) ->
          evalT (Implies (Always propId) (Next propId)) ((0, a0) : (0.1, a1) : (first getPositive <$> samples)),
        testProperty "next A -> eventually A" $ \(a0 :: Bool) (a1 :: Bool) (samples :: [(Positive Time, Bool)]) ->
          evalT (Implies (Next propId) (Eventually propId)) ((0, a0) : (0.1, a1) : (first getPositive <$> samples)),
        testProperty "always A -> eventually A" $ \(a0 :: Bool) (a1 :: Bool) (samples :: [(Positive Time, Bool)]) ->
          evalT (Implies (Always propId) (Eventually propId)) ((0, a0) : (0.1, a1) : (first getPositive <$> samples)),
        testProperty "eventually always A -> always eventually A" $ boolStream $ evalT (Implies (Eventually $ Always propId) (Always $ Eventually propId)),
        testProperty "always always A -> always A" $ boolStream $ evalT (Implies (Always $ Always propId) (Always propId)),
        testProperty "eventually eventually A -> eventually A" $ boolStream $ evalT (Implies (Eventually $ Eventually propId) (Eventually propId))
      ],
    testGroup
      "Initialization"
      [ testProperty "initially" prop_initially,
        testProperty "-->" prop_initialization,
        testProperty ">--" prop_input_initialization,
        testProperty ">=-" prop_f_initialization
      ],
    testGroup
      "Event Related"
      [ testProperty "never" prop_never,
        testProperty "now" prop_now,
        testProperty "after" prop_after,
        testProperty "notYet" prop_not_yet,
        testProperty "dropEvents" prop_drop_events,
        testProperty "takeEvents" prop_take_events
      ],
    testGroup
      "Time related"
      [ testProperty "time always increases" prop_basic_time_increasing,
        testProperty "derivative sin" prop_derivative_1,
        testProperty "derivative polynomial" prop_derivative_2,
        testProperty "integral polynomial" prop_integral_1,
        testProperty "integral sin" prop_integral_2,
        testProperty "integral sin var times" prop_integral_2_var
        -- doesn't pass these tests.
        --testProperty "falling ball x >= floor height and <= initial height delta = 0.001" prop_ball_fixed
        --testProperty "falling ball x >= floor height and <= initial height var" prop_ball_var
      ],
    testGroup
      "Switch"
      [ testProperty "switch happens imediatelly" prop_switch_1,
        testProperty "dSwitch happens on next tick" prop_switch_2,
        testProperty "cascading switchs happen imediatelly" prop_switch_3
      ]
  ]

prop_initially :: Int -> Int -> [(Positive Time, Int)] -> Bool
prop_initially initialValue =
  withStream $
    evalT $
      And
        (prop (cell, const (== initialValue)))
        (Next (Always (prop (cell &&& id, const (uncurry (==))))))
  where
    cell = initially (initialValue :: Int)

prop_initialization :: Int -> Int -> Int -> [(Positive Time, Int)] -> Bool
prop_initialization initialValue laterValue =
  withStream $
    evalT $
      And
        (prop (cell, const (== (initialValue :: Int))))
        (Next (Always (prop (cell, const (== (laterValue :: Int))))))
  where
    cell = initialValue --> constC laterValue

prop_input_initialization :: Int -> Int -> Int -> [(Positive Time, Int)] -> Bool
prop_input_initialization initialValue laterValue =
  withStream $
    evalT $
      And
        (prop (cell, const (== (initialValue + 10))))
        (Next $ Always $ prop (cell &&& arr (+ 10), const (uncurry (==))))
  where
    cell = initialValue >-- arr (+ 10)

prop_f_initialization :: Fun Int Int -> Int -> [(Positive Time, Int)] -> Bool
prop_f_initialization (Fn f) =
  withStream $
    evalT $
      And
        (prop (cell &&& id, const (\(a, b) -> a == f b)))
        (Next $ Always $ prop (cell &&& id, const (uncurry (==))))
  where
    cell = f >=- id

prop_never :: Int -> [(Positive Time, Int)] -> Bool
prop_never = withStream $ evalT $ Always $ prop (never, const (== (Nothing :: Maybe ())))

prop_now :: Int -> [(Positive Time, Int)] -> Bool
prop_now =
  withStream $
    evalT
      ( And
          (prop (cell, const (== Just value)))
          (Next $ Always $ prop (cell, const (== Nothing)))
      )
  where
    value :: Int
    value = 99
    cell = now value

prop_after :: Property
prop_after = forAll (choose (0.1, 1)) $ \t ->
  withStreamFixedDeltaTime @() (2 * t) 0.01 $
    evalT $
      Eventually $ prop (time &&& after t (99 :: Int), const $ \(t', v) -> t' >= t && v == Just 99)

prop_not_yet :: Int -> [(Positive Time, Int)] -> Bool
prop_not_yet =
  withStream $
    evalT $
      And
        (prop (cell, const (== (Nothing :: Maybe Int))))
        (Next $ Always $ prop (cell &&& arr Just, const $ uncurry (==)))
  where
    cell = arr Just >>> notYet

prop_take_events :: Int -> Maybe () -> [(Positive Time, Maybe ())] -> Bool
prop_take_events numEventsToTake =
  withStream $
    evalT $
      And
      (Always $
        Implies
          (prop (sum, const (>= numEventsToTake)))
          (prop (cell, const (== Nothing))))
      ( Always $
            Implies
              (prop (sum, const (< numEventsToTake)))
              (prop (cell &&& id, const (uncurry (==))))
        )
  where
    cell :: Cell (ClockInfoT Identity) (Maybe ()) (Maybe ())
    cell = takeEvents numEventsToTake
    sum = arr (const (+ 1) <$>) >>> daccumHold (0 :: Int)

prop_drop_events :: Int -> Maybe () -> [(Positive Time, Maybe ())] -> Bool
prop_drop_events numEventsToDrop =
  withStream $
    evalT $
      And
        ( Always $
            Implies
              (prop (sum, const (<= numEventsToDrop)))
              (prop (cell, const (== Nothing)))
        )
        ( Always $
            Implies
              (prop (sum, const (> numEventsToDrop)))
              (prop (cell &&& id, const (uncurry (==))))
        )
  where
    cell :: Cell (ClockInfoT Identity) (Maybe ()) (Maybe ())
    cell = dropEvents numEventsToDrop
    sum = arr (const (+ 1) <$>) >>> accumHold (0 :: Int)

prop_basic_time_increasing :: Int -> [(Positive Time, Int)] -> Bool
prop_basic_time_increasing = withStream $ evalT $ Always $ prop (cell, const (uncurry (>)))
  where
    cell :: ClockCell' a (Time, Time)
    cell = proc _ -> do
      t <- time -< ()
      tPrev <- delay (-1) -< t
      returnA -< (t, tPrev)

prop_derivative_1 :: Bool
prop_derivative_1 =
  evalT
    (Next $ prop_always_similar 0.05 sfDer sfDerByHand) --doesn't hold on first sample
    (streamFixedDeltaZeros timeStep (ceiling (2 / timeStep)))
  where
    sfDer = time >>> arr (\t -> sin (2 * pi * t)) >>> derivative
    sfDerByHand = time >>> arr (\t -> 2 * pi * cos (2 * pi * t))

prop_derivative_2 :: Bool
prop_derivative_2 =
  evalT
    (Next $ prop_always_similar 0.05 sfDer sfDerByHand) --doesn't hold on first sample
    (streamFixedDeltaZeros timeStep (ceiling (2 / timeStep)))
  where
    sfDer = time >>> arr (\t -> 1 + t + t ** 2 + t ** 3 + t ** 4) >>> derivative
    sfDerByHand = time >>> arr (\t -> 1 + 2 * t + 3 * (t ** 2) + 4 * (t ** 3))

prop_integral_1 :: Bool
prop_integral_1 =
  evalT
    (prop_always_similar 0.05 cellInt cellIntByHand)
    (streamFixedDeltaZeros timeStep (ceiling (10 / timeStep)))
  where
    cellInt = time >>> arr (\t -> 1 + t + t ** 2 + t ** 3 + t ** 4) >>> integral
    cellIntByHand = time >>> arr (\t -> t + (t ** 2) / 2 + (t ** 3) / 3 + (t ** 4) / 4 + (t ** 5) / 5)

prop_integral_2 :: Bool
prop_integral_2 =
  evalT
    (prop_always_similar 0.05 cellInt cellIntByHand)
    (streamFixedDeltaZeros timeStep (ceiling (2 / timeStep))) -- run at least 2 sin cycles
  where
    cellInt = time >>> arr (\t -> sin (2 * pi * t)) >>> integral
    cellIntByHand = time >>> arr (\t -> (sin (pi * t) ** 2) / pi)

prop_integral_2_var :: Property
prop_integral_2_var =
  withStreamRangeSized (0.001, 0.005) (ceiling (2 / 0.001)) $ -- run at least 2 sin cycles
    evalT
      (prop_always_similar 0.05 cellInt cellIntByHand)
  where
    cellInt = time >>> arr (\t -> sin (2 * pi * t)) >>> integral
    cellIntByHand = time >>> arr (\t -> (sin (pi * t) ** 2) / pi)

prop_switch_1 :: Int -> [(Positive Time, Int)] -> Bool
prop_switch_1 = withStream $ \stream ->
  evalT
    (prop_always_equal cell id)
    ((0, 0) : stream) -- make sure first value is not 99
  where
    cell = switch (constC (99, Just ())) f
    f () = id

prop_switch_2 :: Int -> [(Positive Time, Int)] -> Bool
prop_switch_2 = withStream $ \stream ->
  evalT
    ( And
        (prop (cell, const (== 99)))
        (Next $ prop_always_equal cell id)
    )
    ((0, 0) : stream) -- make sure first value is not 99
  where
    cell = dSwitch (constC (99, Just ())) f
    f () = id

prop_switch_3 :: Int -> [(Positive Time, Int)] -> Bool
prop_switch_3 = withStream $ \stream ->
  evalT
    (prop_always_equal cell id)
    ((0, 0) : stream) -- make sure first value is not 98 or 99
  where
    cell = switch (constC (98, Just ())) f
    f () = switch (constC (99, Just ())) g
    g () = id

-- This is only true with small enough sample list. After a while it becomes false.
prop_ball_fixed :: Bool
prop_ball_fixed =
  evalT (Always $ prop (bouncingBall, const (\x -> x >= 0 && x <= 2))) ((0, 0) : replicate 10000 (timeStep, 0))

prop_ball_var :: Property
prop_ball_var =
  withStreamRangeSized (0.001, 0.01) 5000 $
    evalT (Always $ prop (bouncingBall, const (>= 0)))

bouncingBall :: Monad m => Cell (ClockInfoT m) a Double
bouncingBall = foreverE (2, 0) $ proc _ -> do
  (p0, v0) <- constM ask -< ()
  (p, v) <- liftCell $ liftCell fallingBall -< (p0, v0)
  bounce <- edge -< (p <= 0 && v < 0)
  liftCell throwEC -< (p, - v) <$ bounce
  returnA -< p

fallingBall ::
  Monad m =>
  Cell
    (ClockInfoT m)
    (Double, Double)
    (Double, Double)
fallingBall = proc (p0, v0) -> do
  v <- integral -< (-9.81 :: Double)
  let v' = v + v0
  p <- integral -< v'
  returnA -< (p + p0, v')

timeStep :: Double
timeStep = 0.001
