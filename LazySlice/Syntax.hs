{-# LANGUAGE DeriveFunctor, GADTs, KindSignatures #-}
module LazySlice.Syntax where

-- | http://www.cse.chalmers.se/~abela/msfp08.pdf is a good guide.

-- | The uninhabited type.
data Void :: * where

-- | Terms are parameterized by v, the type of their variables.
--   Whenever a new scope is entered, v is increased by one
--   inhabitant.
data Term v
    = App (Term v) (Term v)
    | Lam (Term v) (Term (Maybe v))
    | Pi (Term v) (Term (Maybe v))
    | Sigma (Term v) (Term (Maybe v))
    | Universe
    | Var v
    deriving Functor

-- | A spine of function applications.
data Neutral v
    = NApp (Neutral v) (Val v)
    | NVar v

-- | Weak head normal forms.
data Whnf v
    = WNeu (Neutral v)
    | WLam (Env v) (Val v) (Term (Maybe v))
    | WLet (Val v) (Whnf (Maybe v))
    | WPi (Val v) (Val (Maybe v))
    | WSigma (Val v) (Val (Maybe v))
    | WUniverse

-- | An environment is a map from variables to their values. It is not to be confused
--   with a typing context, which is a map from variables to their types.
data Env :: * -> * where
    Empty :: Env Void
    Binding :: Env v -> Val (Maybe v) -> Env (Maybe v)

data Val v
    = Clos (Env v) (Term v) -- ^ A closure is a term in an environment.
    | Free v
