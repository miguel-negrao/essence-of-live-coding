{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RankNTypes #-}

module LiveCoding.HandlingState where

-- base
import Control.Arrow (returnA, arr, (>>>))
import Data.Data

-- transformers
import Control.Monad.Trans.Class (MonadTrans(lift))
import Control.Monad.Trans.State.Strict
import Data.Foldable (traverse_)

-- containers
import Data.IntMap hiding (singleton)
import qualified Data.IntMap as IntMap hiding (singleton)

-- mmorph
import Control.Monad.Morph

-- operational
import Control.Monad.Operational

-- essence-of-live-coding
import LiveCoding.Cell
import LiveCoding.Cell.Monad
import LiveCoding.Cell.Monad.Trans
import LiveCoding.LiveProgram
import LiveCoding.LiveProgram.Monad.Trans
import Data.Function ((&))

data Handling h where
  Handling
    :: { key    :: Key
       , handle :: h
       }
    -> Handling h
  Uninitialized :: Handling h

data HandlingStateInstruction m a where
  Register :: m () -> HandlingStateInstruction m Key
  Reregister :: m () -> Key -> HandlingStateInstruction m ()
  UnregisterAll :: HandlingStateInstruction m ()
  DestroyUnregistered :: HandlingStateInstruction m ()

instance MFunctor HandlingStateInstruction where
  hoist morphism (Register action) = Register $ morphism action
  hoist morphism (Reregister action key) = Reregister (morphism action) key
  hoist morphism UnregisterAll = UnregisterAll
  hoist morphism DestroyUnregistered = DestroyUnregistered

-- | In this monad, handles can be registered,
--   and their destructors automatically executed.
--   It is basically a monad in which handles are automatically garbage collected.
type HandlingStateT m = ProgramT (HandlingStateInstruction m) m

hoistHandlingStateT :: (Monad m, Monad n) => (forall x . m x -> n x) -> HandlingStateT m a -> HandlingStateT n a
hoistHandlingStateT morphism = mapInstr (hoist morphism) . hoistProgramT morphism

type Destructors m = IntMap (Destructor m)

-- | Hold a map of registered handle keys and destructors
data HandlingState m = HandlingState
  { nHandles    :: Key
  , destructors :: Destructors m
  }
  deriving Data

type HandlingStateCarrierT m = StateT (HandlingState m) m

initHandlingState :: HandlingState m
initHandlingState = HandlingState
  { nHandles = 0
  , destructors = IntMap.empty
  }

-- | Handle the 'HandlingStateT' effect _without_ garbage collection.
--   Apply this to your main loop after calling 'foreground'.
--   Since there is no garbage collection, don't use this function for live coding.
runHandlingStateT
  :: Monad m
  => HandlingStateT m a
  -> m a
runHandlingStateT = runHandlingStateCarrierT . interpretHandlingState

runHandlingStateCarrierT
  :: Monad m
  => HandlingStateCarrierT m a
  -> m a
runHandlingStateCarrierT = flip evalStateT initHandlingState

{- | Apply this to your main live cell before passing it to the runtime.

On the first tick, it initialises the 'HandlingState' at "no handles".

On every step, it does:

1. Unregister all handles
2. Register currently present handles
3. Destroy all still unregistered handles
   (i.e. those that were removed in the last tick)
-}
runHandlingStateC
  :: forall m a b .
     (Monad m, Typeable m)
  => Cell (HandlingStateT m) a b
  -> Cell                 m  a b
runHandlingStateC cell = flip runStateC_ initHandlingState
  $ hoistCell (interpretHandlingState . garbageCollected) cell

-- | Like 'runHandlingStateC', but for whole live programs.
runHandlingState
  :: (Monad m, Typeable m)
  => LiveProgram (HandlingStateT m)
  -> LiveProgram                 m
runHandlingState LiveProgram { .. } = flip runStateL initHandlingState $ hoistLiveProgram interpretHandlingState LiveProgram
  { liveStep = garbageCollected . liveStep
  , ..
  }

garbageCollected
  :: Monad m
  => HandlingStateT m a
  -> HandlingStateT m a
garbageCollected action = unregisterAll >> action <* destroyUnregistered

data Destructor m = Destructor
  { isRegistered :: Bool
  , action       :: m ()
  }


register
  :: Monad m
  => m () -- ^ Destructor
  -> HandlingStateT m Key
register = singleton . Register

reregister
  :: Monad m
  => m ()
  -> Key
  -> HandlingStateT m ()
reregister action key = singleton $ Reregister action key

unregisterAll
  :: Monad m
  => HandlingStateT m ()
unregisterAll = singleton UnregisterAll

destroyUnregistered
  :: Monad m
  => HandlingStateT m ()
destroyUnregistered = singleton DestroyUnregistered

insertDestructor
  :: m ()
  -> Key
  -> Destructors m
  -> Destructors m
insertDestructor action key destructors =
  let destructor = Destructor { isRegistered = True, .. }
  in  insert key destructor destructors

interpretHandlingState :: Monad m => HandlingStateT m a -> HandlingStateCarrierT m a
interpretHandlingState action = do
  firstAction <- lift $ viewT action
  case firstAction of
    Return a -> return a
    instruction :>>= continuation -> interpretHandlingStateInstruction instruction >>= (interpretHandlingState . continuation)
  -- interpretWithMonadT interpretHandlingStateInstruction

interpretHandlingStateInstruction :: Monad m => HandlingStateInstruction m a -> HandlingStateCarrierT m a

interpretHandlingStateInstruction (Register destructor) = do
  HandlingState { .. } <- get
  let key = nHandles + 1
  put HandlingState
    { nHandles = key
    , destructors = insertDestructor destructor key destructors
    }
  return key

interpretHandlingStateInstruction (Reregister action key) = do
  HandlingState { .. } <- get
  put HandlingState { destructors = insertDestructor action key destructors, .. }

interpretHandlingStateInstruction UnregisterAll = do
  HandlingState { .. } <- get
  let newDestructors = IntMap.map (\destructor -> destructor { isRegistered = False }) destructors
  put HandlingState { destructors = newDestructors, .. }

interpretHandlingStateInstruction DestroyUnregistered = do
  HandlingState { .. } <- get
  let
      (registered, unregistered) = partition isRegistered destructors
  traverse_ (lift . action) unregistered
  put HandlingState { destructors = registered, .. }

-- * Things that belong to the operational package

interpretWithMonadT :: Monad m => (forall x . instr x -> m x) -> ProgramT instr m a -> m a
interpretWithMonadT interpreter = go
  where
    go program = do
      firstInstruction <- viewT program
      case firstInstruction of
        Return a -> return a
        instruction :>>= continuation -> interpreter instruction >>= (go . continuation)

unviewT :: Monad m => ProgramViewT instr m a -> ProgramT instr m a
unviewT (Return a) = return a
unviewT (instruction :>>= continuation) = singleton instruction >>= continuation

-- Ideally, this was implemented as instance MMorph from the mmorph package, but it lacks the Monad n context
hoistProgramT :: (Monad m, Monad n) => (forall x . m x -> n x) -> ProgramT instr m a -> ProgramT instr n a
hoistProgramT morphism action = (action
  & viewT
  & morphism
  & fmap (hoistViewT morphism)
  & lift)
  >>= unviewT

hoistViewT :: (Monad m, Monad n) => (forall x . m x -> n x) -> ProgramViewT instr m a -> ProgramViewT instr n a
hoistViewT morphism (Return a) = Return a
hoistViewT morphism (instruction :>>= continuation) = instruction :>>= (hoistProgramT morphism . continuation)

-- TODO Refactor with unviewT
mapInstr :: Monad m => (forall x . instr1 x -> instr2 x) -> ProgramT instr1 m a -> ProgramT instr2 m a
mapInstr f = go
  where
    go action = do
      leftInstruction <- lift $ viewT action
      case leftInstruction of
        Return a -> return a
        instruction :>>= continuation -> singleton (f instruction) >>= (go . continuation)

-- * 'Data' instances

dataTypeHandling :: DataType
dataTypeHandling = mkDataType "Handling" [handlingConstr, uninitializedConstr]

handlingConstr :: Constr
handlingConstr = mkConstr dataTypeHandling "Handling" [] Prefix

uninitializedConstr :: Constr
uninitializedConstr = mkConstr dataTypeHandling "Uninitialized" [] Prefix

instance (Typeable h) => Data (Handling h) where
  dataTypeOf _ = dataTypeHandling
  toConstr Handling { .. } = handlingConstr
  toConstr Uninitialized = uninitializedConstr
  gunfold _cons nil constructor = nil Uninitialized

dataTypeDestructor :: DataType
dataTypeDestructor = mkDataType "Destructor" [ destructorConstr ]

destructorConstr :: Constr
destructorConstr = mkConstr dataTypeDestructor "Destructor" [] Prefix

instance Typeable m => Data (Destructor m) where
  dataTypeOf _ = dataTypeDestructor
  toConstr Destructor { .. } = destructorConstr
  gunfold _ _ = error "Destructor.gunfold"
