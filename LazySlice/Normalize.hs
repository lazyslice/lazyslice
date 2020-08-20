{-# LANGUAGE FlexibleContexts, FunctionalDependencies, GeneralizedNewtypeDeriving #-}
module LazySlice.Normalize where

import LazySlice.Syntax
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader, ask, local)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont (ContT, resetT, shiftT)
import Control.Monad.Trans.Except (ExceptT(..))
import Control.Monad.Trans.Reader (ReaderT)

inScope :: (Int -> Eval a) -> Eval a
inScope f = do
    idx <- ask
    local (+1) (f $ idx + 1)

prompt :: Eval Whnf -> Eval Whnf
prompt (Eval m) = Eval $ resetT m

control :: ((Either String Whnf -> ContTy Whnf) -> Eval Whnf) -> Eval Whnf
control f = Eval $ shiftT (eval . f)

typeError :: String -> Eval a
typeError = Eval . pure . Left

handler _ = Nothing

-- | Evaluate to WHNF.
whnf :: Env -> Conts -> Term -> Handler -> Eval Whnf
whnf rho kappa (App t u) h = do
    t <- whnf rho kappa t h
    case t of
        WLam a (Abs rho t) -> whnf (Val v : rho) kappa t h
        WNeu neu -> return $ WNeu (NApp neu v)
        _ -> typeError "Not a function"
    where v = Clos rho kappa h u
whnf rho kappa (Break t u) h = do
    t <- whnf rho kappa t h
    case t of
        WCont k -> do
            u <- whnf rho kappa u h
            Eval $ lift $ (k (Right u))
        _ -> typeError "Not a continuation"
whnf _ kappa (Cont k) _ = return $ WCont (kappa !! k)
whnf rho kappa (Lam a t) h =
    return $ WLam (Clos rho kappa h a) (Abs rho t)
whnf rho kappa (Raise eff) h =
    control $ \k ->
        case h eff of
            Nothing -> typeError $ "Uncaught exception: " ++ eff
            Just t -> whnf rho (k : kappa) t handler
whnf rho kappa (Pi a b) h = return $ WPi (Clos rho kappa h a) (Abs rho b)
whnf rho kappa (Sigma a b) h = return $ WSigma (Clos rho kappa h a) (Abs rho b)
whnf rho kappa (Try t) h = prompt (whnf rho kappa t h)
whnf _ _ Universe _ = return WUniverse
whnf rho _ (Var v) _ =
    case rho !! v of
        Val (Clos rho' kappa' h t) -> whnf rho' kappa' t h
        Free v -> return $ WNeu (NVar v)

unifyWhnf :: Whnf -> Whnf -> Eval ()
unifyWhnf (WNeu neul) (WNeu neur) = unifyNeu neul neur
unifyWhnf (WLam a t) (WLam b u) = unifyAbs t u
unifyWhnf (WPi a b) (WPi c d) = do
    unifyVal a c
    unifyAbs b d
unifyWhnf (WSigma a b) (WSigma c d) = do
    unifyVal a c
    unifyAbs b d
unifyWhnf WUniverse WUniverse = return ()
unifyWhnf _ _ = typeError "Unify fail"

unifyNeu :: Neutral -> Neutral -> Eval ()
unifyNeu (NVar i) (NVar j)
    | i == j = return ()
    | otherwise = typeError "Unify fail"
unifyNeu (NApp nl vl) (NApp nr vr) = do
    unifyNeu nl nr
    unifyVal vl vr
unifyNeu _ _ = typeError "Unify fail"

unifyVal :: Val -> Val -> Eval ()
unifyVal (Clos rho kappa h t) (Clos rho' kappa' h' u) = do
    t <- whnf rho kappa t h
    u <- whnf rho' kappa' u h'
    unifyWhnf t u

unifyAbs :: Abs -> Abs -> Eval ()
unifyAbs (Abs rho t) (Abs rho' u) =
    inScope $ \i -> do
        t <- whnf (Free i : rho) [] t handler
        u <- whnf (Free i : rho') [] u handler
        unifyWhnf t u
