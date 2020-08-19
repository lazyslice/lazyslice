module LazySlice.Syntax where

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

-- | A spine of function applications.
data Neutral m
    = NApp (Neutral m) (Val m)
    | NVar Int

-- | Weak head normal forms.
data Whnf m
    = WCont (Whnf m -> m (Whnf m))
    | WNeu (Neutral m)
    | WLam (Val m) (Abs m)
    | WPi (Val m) (Abs m)
    | WSigma (Val m) (Abs m)
    | WUniverse

-- | The environment of values.
type Env m = [Binding m]

-- | The environment of continuations.
type Conts m = [Whnf m -> m (Whnf m)]

data Binding m
    = Val (Val m)
    | Free Int -- ^ A free variable is not a De Bruijn index, and it counts from the outside in.

-- | A handler catches an effect.
type Handler = String -> Maybe Term

data Val m = Clos (Env m) (Conts m) Handler Term

data Abs m = Abs (Env m) Term
