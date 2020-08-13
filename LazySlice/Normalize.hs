{-# LANGUAGE TypeFamilies #-}
module LazySlice.Normalize where

import LazySlice.Syntax

shift :: Val v -> Val (Maybe v)
shift (Free v) = Free (Just v)
shift (Clos rho t) = Clos (Binding rho (Free Nothing)) (fmap Just t)

getVar :: Env v -> v -> Val v
getVar (Binding _ val) Nothing = val
getVar (Binding rho _) (Just v) = shift $ getVar rho v

-- | Evaluate to WHNF.
whnf :: Env v -> Term v -> Whnf v
whnf rho (App t u) = app (whnf rho t) (Clos rho u)
whnf rho (Lam a t) = WLam rho (Clos rho a) t
whnf rho (Pi a b) = WPi (Clos rho a) (Clos (Binding rho (Free Nothing)) b)
whnf rho (Sigma a b) = WSigma (Clos rho a) (Clos (Binding rho (Free Nothing)) b)
whnf _ Universe = WUniverse
whnf rho (Var v) =
    case getVar rho v of
        Clos rho' t -> whnf rho' t
        Free v -> WNeu (NVar v)

app :: Whnf v -> Val v -> Whnf v
app (WLam rho a t) v = WLet v (whnf (Binding rho (shift v)) t)
app (WNeu neu) v = WNeu (NApp neu v)
