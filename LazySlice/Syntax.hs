{-# LANGUAGE FlexibleContexts, FunctionalDependencies, GeneralizedNewtypeDeriving #-}
module LazySlice.Syntax where

import Control.Monad.Trans.Reader (Reader)
import Data.Map (Map)

-- | http://www.cse.chalmers.se/~abela/msfp08.pdf is a good guide.
--  http://www.davidchristiansen.dk/tutorials/nbe/ presents similar code in Racket.

data Module = Module
    { decls :: [Decl] }
    deriving Show

data Decl
    = Declare String Term
    | Define String Term
    deriving Show

data Term
    = App Term Term
    | Cont Int -- ^ Continuations use a separate De Bruijn index from the variables, counted inside-out by the effect handlers.
    | Def String -- ^ A global definition.
    | Lam (Maybe Term) Term
    | Pair Term Term
    | Pi Term Term
    | Raise String
    | Sigma Term Term
    | Triv
    | Try Term
    | Unit
    | Universe
    | Var Int -- ^ A variable is a De Bruijn index (which counts from the inside-out).
    deriving Show

type Table = Map String (Whnf, Maybe Term)

type ContTy = (Reader (Table, Int)) (Either String Whnf)

-- | A spine of function applications.
data Neutral
    = NApp Neutral Val
    | NVar Int

-- | Weak head normal forms.
data Whnf
    = WCont (Either String Whnf -> ContTy)
    | WNeu Neutral
    | WLam (Maybe Val) Abs
    | WPair Val Val
    | WPi Val Abs
    | WSigma Val Abs
    | WTriv
    | WUnit
    | WUniverse

-- | The environment of values.
type Env = [Binding]

-- | The environment of continuations.
type Conts = [Either String Whnf -> ContTy]

data Binding
    = Val Val
    | Free Int -- ^ A free variable is not a De Bruijn index, and it counts from the outside in.

-- | A handler catches an effect.
type Handler = String -> Maybe Term

data Val = Clos Env Conts Handler Term

data Abs = Abs Env Term
