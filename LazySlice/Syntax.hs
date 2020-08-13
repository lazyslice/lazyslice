module LazySlice.Syntax where

-- | http://www.cse.chalmers.se/~abela/msfp08.pdf is a good guide.
--  http://www.davidchristiansen.dk/tutorials/nbe/ presents similar code in Racket.

data Term
    = App Term Term
    | Lam Term Term
    | Pi Term Term
    | Sigma Term Term
    | Universe
    | Var Int -- ^ A variable is a De Bruijn index (which counts from the inside-out).

-- | A spine of function applications.
data Neutral
    = NApp Neutral Val
    | NVar Int

-- | Weak head normal forms.
data Whnf
    = WNeu Neutral
    | WLam Val Abs
    | WPi Val Abs
    | WSigma Val Abs
    | WUniverse

type Env = [Binding]

data Binding
    = Val Val
    | Free Int -- ^ A free variable is not a De Bruijn index, and it counts from the outside in.

data Val = Clos Env Term

-- | And Abs and a Val share the same representation, but
--   they have differens semantics. An Abs's term has one
--   bound variable.
data Abs = Abs Env Term
