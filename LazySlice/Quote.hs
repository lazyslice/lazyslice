module LazySlice.Quote where

import LazySlice.AST as AST
import LazySlice.Syntax as Syn
import Control.Monad (replicateM)

quoteTerm :: [Binding] -> SymbolStack -> Syn.Term -> AST.Expr
quoteTerm i vs (Syn.App t u) =
    AST.App (quoteTerm i vs t) (quoteTerm i vs u)
quoteTerm _ _ (Syn.Def name) = AST.Var name
quoteTerm i vs (Syn.Lam _ t) =
        AST.Lam (getPartial vs' 0) (quoteTerm i vs' t)
    where vs' = push vs
quoteTerm i vs (Syn.Pair t u) =
    AST.Pair (quoteTerm i vs t) (quoteTerm i vs u)
quoteTerm i vs (Syn.Pi t u) =
        AST.Pi (getPartial vs' 0) (quoteTerm i vs t)
            (quoteTerm i vs' u)
    where vs' = push vs
quoteTerm i vs (Syn.Sigma t u) =
        AST.Sigma (getPartial vs' 0) (quoteTerm i vs t)
            (quoteTerm i vs' u)
    where vs' = push vs
quoteTerm _ _ Syn.Triv = AST.Triv
quoteTerm _ _ Syn.Unit = AST.Unit
quoteTerm _ _ Syn.Universe = AST.Univ
quoteTerm i vs (Syn.Var v) = case get vs v of
    Right v -> AST.Var v
    Left off -> case i !! off of
        Val v -> quoteVal v
        Free fv -> AST.Var $ "fv" ++ show fv
        Pat pv -> AST.Var $ show pv

quoteVal :: Syn.Val -> AST.Expr
quoteVal (Clos _ _ env _ _ t) = quoteTerm env empty t
quoteVal (Whnf whnf) = quoteWhnf whnf

quoteAbs :: Syn.Abs -> AST.Expr
quoteAbs (Abs _ _ env t) = quoteTerm env vs t
    where vs = push empty

quoteWhnf :: Syn.Whnf -> AST.Expr
quoteWhnf (Syn.WNeu hd spine) = go spine
    where
        go [] = case hd of
            DataCon s -> AST.Var s
            FreeVar fv -> AST.Var $ "fv" ++ show fv
            PatVar pv -> AST.Var $ show pv
            MatVar mv -> AST.Var $ show mv
            TypeCon s -> AST.Var s
            Fun s _ -> AST.Var s
        go (x:xs) = AST.App (go xs) (quoteVal x)
quoteWhnf (Syn.WLam ty (Syn.Abs _ _ env a)) =
        AST.Lam "a" (quoteTerm env vs a)
    where vs = push empty
quoteWhnf (Syn.WPair a b) =
    AST.Pair (quoteVal a) (quoteVal b)
quoteWhnf (Syn.WPi a (Syn.Abs _ _ env b)) =
        AST.Pi "a" (quoteVal a) (quoteTerm env vs b)
    where vs = push empty
quoteWhnf (Syn.WSigma a (Syn.Abs _ _ env b)) =
        AST.Sigma "a" (quoteVal a) (quoteTerm env vs b)
    where vs = push empty
quoteWhnf Syn.WTriv = AST.Triv
quoteWhnf Syn.WUnit = AST.Unit
quoteWhnf Syn.WUniverse = AST.Univ

vars :: [String]
vars = do
    times <- [1..]
    replicateM times ['a'..'z']

data SymbolStack = SymbolStack Int [String]

empty = SymbolStack 0 []

push (SymbolStack depth vs) =
    SymbolStack (depth + 1) $ (vars !! depth):vs

get (SymbolStack _ vs) v = go v vs
    where
        go i [] = Left i
        go 0 (v:_) = Right v
        go i (_:vs) = go (i - 1) vs

getPartial stk v = case get stk v of
    Right x -> x
