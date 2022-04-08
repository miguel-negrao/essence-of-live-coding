{-# LANGUAGE Arrows #-}

{- ORMOLU_DISABLE -}

-- base
import GHC.Float (double2Float)

-- transformers
import Control.Monad.Trans.Reader ( ask )

-- gloss
import Graphics.Gloss (Picture, color, green, thickCircle)
import qualified Graphics.Gloss as Gloss

-- essence-of-live-coding
import LiveCoding
  ( Arrow (arr),
    Cell,
    HandlingStateT,
    LiveProgram,
    arrM,
    foreverE,
    liftCell,
    liveCell,
    liveMain,
    returnA,
    (>>>),
  )

-- essence-of-live-coding-gloss
import LiveCoding.Gloss
  ( GlossSettings (stepsPerSecond),
    PictureT,
    addPicture,
    defaultSettings,
    glossWrapC,
  )

-- essence-of-live-coding-frp
import LiveCoding.FRP
  ( ClockInfoT,
    edge,
    integral,
    runClockInfoC,
    throwEC,
  )

{- ORMOLU_ENABLE -}

{--
Currently the physical simulation is not correct. It appears to have drag although that isn't present
in the equations. Possibly related with incorrect collision detection.
--}

main :: IO ()
main = liveMain liveProgram

liveProgram :: LiveProgram (HandlingStateT IO)
liveProgram = liveCell mainCell

mainCell :: Cell (HandlingStateT IO) () ()
mainCell =
  runClockInfoC bouncingBall
    >>> glossWrapC defaultSettings {stepsPerSecond = 25} glossCell
    >>> arr (const ())

ball :: Double -> Picture
ball x = Gloss.translate 0 (double2Float x * 90 - 90) $ color green $ thickCircle 10 20

glossCell :: Cell (PictureT IO) Double ()
glossCell = arr ball >>> addPicture

bouncingBall :: Monad m => Cell (ClockInfoT m) () Double
bouncingBall = foreverE (2, 0) $ proc () -> do
  (p0, v0) <- arrM (const ask) -< ()
  (p, v) <- liftCell $ liftCell fallingBall -< (p0, v0)
  bounce <- edge -< (p <= 0 && v < 0)
  liftCell throwEC -< (p, -v) <$ bounce
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
