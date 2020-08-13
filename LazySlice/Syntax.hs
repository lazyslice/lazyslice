module LazySlice.Syntax where

-- | http://www.cse.chalmers.se/~abela/msfp08.pdf is a good guide.
--  http://www.davidchristiansen.dk/tutorials/nbe/ presents similar code in Racket.

data Term
    = App Term Term
    | Lam Term Term
    | Pi Term Term
    | Sigma Term Term
    | Universe
    | Var Int

-- | A spine of function applications.
data Neutral
    = NApp Neutral Val
    | NVar Int

-- | Weak head normal forms.
data Whnf
    = WNeu Neutral
    | WLam Val Val
    | WPi Val Val
    | WSigma Val Val
    | WUniverse

type Env = [Val]

data Val = Clos Env Term
