{-# LANGUAGE FlexibleContexts, FunctionalDependencies, GeneralizedNewtypeDeriving #-}
module LazySlice.Syntax where

import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader, ask, local)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont (ContT, resetT)
import Control.Monad.Trans.Except (ExceptT(..))
import Control.Monad.Trans.Reader (Reader)

-- | http://www.cse.chalmers.se/~abela/msfp08.pdf is a good guide.
--  http://www.davidchristiansen.dk/tutorials/nbe/ presents similar code in Racket.

data Term
    = App Term Term
    | Break Term Term
    | Cont Int -- ^ Continuations use a separate De Bruijn index from the variables, counted inside-out by the effect handlers.
    | Lam Term Term
    | Pi Term Term
    | Raise String
    | Sigma Term Term
    | Try Term
    | Universe
    | Var Int -- ^ A variable is a De Bruijn index (which counts from the inside-out).

type ContTy a = (Reader Int) (Either String a)

newtype Eval a = Eval
    { eval :: ContT (Either String Whnf) (Reader Int) (Either String a) }

instance Functor Eval where
    fmap f (Eval e) = Eval $ fmap (fmap f) e

instance Applicative Eval where
    pure a = Eval (pure $ pure a)
    (Eval f) <*> (Eval a) = Eval $ (<*>) <$> f <*> a

instance Monad Eval where
    (Eval a) >>= f = Eval $ a >>= go
        where
            go (Left e) = pure (Left e)
            go (Right a) = eval $ f a

instance MonadReader Int Eval where
    ask = Eval $ fmap Right ask
    local f (Eval e) = Eval (local f e)

-- | A spine of function applications.
data Neutral
    = NApp Neutral Val
    | NVar Int

-- | Weak head normal forms.
data Whnf
    = WCont (Either String Whnf -> ContTy Whnf)
    | WNeu Neutral
    | WLam Val Abs
    | WPi Val Abs
    | WSigma Val Abs
    | WUniverse

-- | The environment of values.
type Env = [Binding]

-- | The environment of continuations.
type Conts = [Either String Whnf -> ContTy Whnf]

data Binding
    = Val Val
    | Free Int -- ^ A free variable is not a De Bruijn index, and it counts from the outside in.

-- | A handler catches an effect.
type Handler = String -> Maybe Term

data Val = Clos Env Conts Handler Term

data Abs = Abs Env Term
