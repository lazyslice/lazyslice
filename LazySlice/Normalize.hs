{-# LANGUAGE FlexibleContexts #-}
module LazySlice.Normalize where

import LazySlice.Syntax
import Control.Monad.Except (MonadError, throwError)

-- | Evaluate to WHNF.
whnf :: MonadError String m => Env -> Term -> m Whnf
whnf rho (App t u) = do
    t <- whnf rho t
    case t of
        WLam a (Clos rho t) -> whnf (v : rho) t
        WNeu neu -> return $ WNeu (NApp neu v)
        _ -> throwError "Not a function"
    where v = Clos rho u
whnf rho (Lam a t) = return $ WLam (Clos rho a) (Clos rho t)
whnf rho (Pi a b) = return $ WPi (Clos rho a) (Clos rho b)
whnf rho (Sigma a b) = return $ WSigma (Clos rho a) (Clos rho b)
whnf _ Universe = return WUniverse
whnf rho (Var v) = whnf rho' t
    where Clos rho' t = rho !! v
