{-# LANGUAGE FlexibleContexts #-}
module LazySlice.Normalize where

import LazySlice.Syntax
import Control.Monad.Except (MonadError, throwError)

class Monad m => MonadEval m where
    inScope :: (Int -> m a) -> m a

-- | Evaluate to WHNF.
whnf :: MonadError String m => Env -> Term -> m Whnf
whnf rho (App t u) = do
    t <- whnf rho t
    case t of
        WLam a (Abs rho t) -> whnf (Val v : rho) t
        WNeu neu -> return $ WNeu (NApp neu v)
        _ -> throwError "Not a function"
    where v = Clos rho u
whnf rho (Lam a t) =
    return $ WLam (Clos rho a) (Abs rho t)
whnf rho (Pi a b) =
    return $ WPi (Clos rho a) (Abs rho b)
whnf rho (Sigma a b) =
    return $ WSigma (Clos rho a) (Abs rho b)
whnf _ Universe = return WUniverse
whnf rho (Var v) =
    case rho !! v of
        Val (Clos rho' t) -> whnf rho' t
        Free v -> return $ WNeu (NVar v)

unifyWhnf :: (MonadEval m, MonadError String m) => Whnf -> Whnf -> m ()
unifyWhnf (WNeu neul) (WNeu neur) = unifyNeu neul neur
unifyWhnf (WLam a t) (WLam b u) = unifyAbs t u
unifyWhnf (WPi a b) (WPi c d) = do
    unifyVal a c
    unifyAbs b d
unifyWhnf (WSigma a b) (WSigma c d) = do
    unifyVal a c
    unifyAbs b d
unifyWhnf WUniverse WUniverse = return ()
unifyWhnf _ _ = throwError "Unify fail"

unifyNeu :: (MonadEval m, MonadError String m) => Neutral -> Neutral -> m ()
unifyNeu (NVar i) (NVar j)
    | i == j = return ()
    | otherwise = throwError "Unify fail"
unifyNeu (NApp nl vl) (NApp nr vr) = do
    unifyNeu nl nr
    unifyVal vl vr
unifyNeu _ _ = throwError "Unify fail"

unifyVal :: (MonadEval m, MonadError String m) => Val -> Val -> m ()
unifyVal (Clos rho t) (Clos rho' u) = do
    t <- whnf rho t
    u <- whnf rho' u
    unifyWhnf t u

unifyAbs :: (MonadEval m, MonadError String m) => Abs -> Abs -> m ()
unifyAbs (Abs rho t) (Abs rho' u) =
    inScope $ \i -> do
        t <- whnf (Free i : rho) t
        u <- whnf (Free i : rho') u
        unifyWhnf t u
