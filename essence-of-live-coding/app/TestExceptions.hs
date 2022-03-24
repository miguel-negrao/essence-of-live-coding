{-# LANGUAGE Arrows #-}

-- base
import Control.Arrow
-- transformers
import Control.Monad.Trans.Class
-- essence-of-live-coding
import LiveCoding

liveProgram = liveCell $
  safely $ do
    try $ throwingCell
    safe $ arr (const (3 :: Integer)) >>> sumC >>> arr (const ())

throwingCell = proc _ -> do
  n <- sumC -< (1 :: Integer)
  if n > 10
    then throwC -< ()
    else returnA -< ()
  arrM $ lift . print -< n

main = do
  (debugger, observer) <- countDebugger
  launchWithDebugger liveProgram $ debugger <> statePrint
  await observer 30
