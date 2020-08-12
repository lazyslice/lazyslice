{-# LANGUAGE GADTs, KindSignatures #-}
module LazySlice.Syntax where

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

data Neutral v
    = NApp (Neutral v) (Val v)
    | NVar v

-- | Weak head normal forms.
data Whnf v
    = WNeu (Neutral v)
    | WLam (Val v) (Term v)
    | WPi (Val v) (Val (Maybe v))
    | WSigma (Val v) (Val (Maybe v))
    | WUniverse

data Env :: * -> * where
    Empty :: Env Void
    Binding :: Env v -> Val v -> Env (Maybe v)

data Val v = Clos (Env v) (Term v)
