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
    = Data String [(String, Term)]
    | Declare String Term
    | Define String Term
    | Defun String [([Pattern], Term)]
    deriving Show

data Pattern
    = ConPat String [Pattern]
    | VarPat MatchVar
    | WildPat
    deriving Show

-- | A match variable is a concrete variable used when pattern matching, and
--   always maps to a term.
newtype MatchVar = MV Int
    deriving (Eq, Ord, Show)

nextMV (MV i) = MV (i + 1)

-- | A pattern variable is a symbolic term used when typechecking dependent
--   pattern matching.
newtype PatternVar = PV Int
    deriving (Eq, Ord, Show)

nextPV (PV i) = PV (i + 1)

-- | https://jesper.sikanda.be/files/elaborating-dependent-copattern-matching.pdf
data CaseTree
    = Leaf Term
    | Intro PatternVar CaseTree -- ^ Introduce next parameter
    | Split PatternVar [(String, [PatternVar], CaseTree)]
    -- var, ^ (C, var1..varN, rhs)

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
    | MatchVar MatchVar
    | Var Int -- ^ A variable is a De Bruijn index (which counts from the inside-out).
    deriving Show

data Def
    = Term Term
    | Head Head
    | Undef

data Table = Table
    { datacons :: Map String (String, Whnf) -- ^ (Telescope, Typecon, Type arguments)
    , datatypes :: Map String [(String, Whnf)]
    , defs :: Map String (Whnf, Def) }

data EvalState = EvalState
    { table :: Table
    , index :: Int }

type ContTy = (Reader EvalState) (Either String Whnf)

data Head
    = DataCon String
    | FreeVar Int
    | PatVar PatternVar
    | MatVar MatchVar
    | TypeCon String
    | Fun String CaseTree

instance Eq Head where
    DataCon s1 == DataCon s2 = s1 == s2
    FreeVar i1 == FreeVar i2 = i1 == i2
    PatVar v1 == PatVar v2 = v1 == v2
    MatVar v1 == MatVar v2 = v1 == v2
    TypeCon s1 == TypeCon s2 = s1 == s2
    Fun s1 _ == Fun s2 _ = s1 == s2
    _ == _ = False

instance Show Head where
    show (DataCon s) = s
    show (FreeVar i) = "fv" ++ show i
    show (PatVar v) = show v
    show (MatVar v) = show v
    show (TypeCon s) = s
    show (Fun s _) = s

-- | Weak head normal forms.
data Whnf
    = WCont (Either String Whnf -> ContTy)
    | WNeu Head [Val] -- head, spine
    | WLam (Maybe Val) Abs
    | WPair Val Val
    | WPi Val Abs
    | WSigma Val Abs
    | WTriv
    | WUnit
    | WUniverse

instance Show Whnf where
    show (WCont _) = "<cont>"
    show (WNeu hd spine) =
        "(" ++ show hd ++ " " ++ show spine ++ ")"
    show (WLam m a) =
        "(lam " ++ show m ++ " " ++ show a ++ ")"
    show (WPair a b) =
        "(tuple " ++ show a ++ " " ++ show b ++ ")"
    show (WPi a b) =
        "(pi " ++ show a ++ " " ++ show b ++ ")"
    show (WSigma a b) =
        "(sigma " ++ show a ++ " " ++ show b ++ ")"
    show WTriv = "trivial"
    show WUnit = "unit"
    show WUniverse = "type"

-- | The environment of values.
type Env = [Binding]

-- | The environment of continuations.
type Conts = [Either String Whnf -> ContTy]

data Binding
    = Val Val
    | Free Int -- ^ A free variable is not a De Bruijn index, and it counts from the outside in.
    | Pat PatternVar
    deriving Show

-- | A handler catches an effect.
type Handler = String -> Maybe Term

-- | A match environment maps match variables to terms and is essentially the
--   "solution" to a pattern match.
type MatchEnv = Map MatchVar Val

-- | A pattern environment maps pattern variables to terms and is
--   used when refining the types of dependent pattern match
--   clauses.
type PatEnv = Map PatternVar Whnf

data Val = Clos PatEnv MatchEnv Env Conts Handler Term | Whnf Whnf

instance Show Val where
    show (Clos _ _ env _ _ term) =
        "(clos " ++ show env ++ " " ++ show term ++ ")"

data Abs = Abs PatEnv MatchEnv Env Term

instance Show Abs where
    show (Abs _ _ env term) =
        "(abstr " ++ show env ++ " " ++ show term ++ ")"
