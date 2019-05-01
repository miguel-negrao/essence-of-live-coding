\begin{comment}
\begin{code}
module LiveCoding.CellExcept.Applicative where

-- transformers
import Control.Monad.Trans.Except

-- essenceoflivecoding
import LiveCoding.Cell
\end{code}
\end{comment}

At this point, we unfortunately have to give up the efficient \mintinline{haskell}{newtype}.
The spoilsport is, again the type class \mintinline{haskell}{Data},
to which the exception type \mintinline{haskell}{e1} is subjected
(since the exception must be stored during the execution of the second cell).
But the issue is minor,
it is fixed by defining the \emph{free functor},
or \emph{Co-Yoneda construction}:
\fxwarning{Maybe cite http://comonad.com/reader/2016/adjoint-triples/ or search something else}
\fxwarning{Possible other names: Mode}
\begin{code}
data CellExcept m a b e = forall e' .
  Data e' => CellExcept
  { fmapExcept :: e' -> e
  , cellExcept :: Cell (ExceptT e' m) a b
  }
\end{code}
While ensuring that we only store cells with exceptions that can be \emph{bound},
we allow do not restrict the parameter type \mintinline{haskell}{e}.

It is known that this construction gives rise to a \mintinline{haskell}{Functor} instance for free:
\begin{code}
instance Functor (CellExcept m a b) where
  fmap f CellExcept { .. } = CellExcept
    { fmapExcept = f . fmapExcept
    , ..
    }
\end{code}

The \mintinline{haskell}{Applicative} instance arises from the work we have done so far.
\mintinline{haskell}{pure} is implemented by throwing a unit and transforming it to the required exception,
while sequential application is a bookkeeping exercise around the previously defined function \mintinline{haskell}{andThen}:
\begin{code}
instance Monad m
  => Applicative (CellExcept m a b) where
  pure e = CellExcept
    { fmapExcept = const e
    , cellExcept = constM $ throwE ()
    }

  CellExcept fmap1 cell1 <*>
    CellExcept fmap2 cell2 = CellExcept { .. }
    where
      fmapExcept (e1, e2) = fmap1 e1
        $ fmap2 e2
      cellExcept = cell1 `andThen` cell2
\end{code}
\end{comment}

We can enter the \mintinline{haskell}{CellExcept} context from an exception-throwing cell,
trying to execute it until the exception occurs:
\begin{spec}
try
  :: Data          e
  => Cell (ExceptT e m) a b
  -> CellExcept      m  a b e
\end{spec}
\begin{comment}
\begin{code}
-- try :: (Data e, Commutable e) => Cell (ExceptT e m) a b -> CellExcept m a b e
try :: Data e => Cell (ExceptT e m) a b -> CellExcept m a b e
\end{code}
\end{comment}
\begin{code}
try = CellExcept id
\end{code}
And we can leave it safely once we have proven that there are no exceptions left to throw,
i.e. the exception type is empty:
\begin{code}
safely
  :: Monad      m
  => CellExcept m a b Void
  -> Cell       m a b
safely = hoistCell discardVoid . runCellExcept

discardVoid
  :: Functor      m
  => ExceptT Void m a
  ->              m a
discardVoid
  = fmap (fromRight
      (error "safely: Received Left")
    ) . runExceptT
\end{code}
