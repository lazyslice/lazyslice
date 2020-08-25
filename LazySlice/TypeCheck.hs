{-# LANGUAGE ApplicativeDo, FlexibleContexts, FlexibleInstances, FunctionalDependencies #-}
module LazySlice.TypeCheck where

import LazySlice.Syntax
import Control.Monad.Except (MonadError, throwError, catchError)
import Control.Monad.Reader (MonadReader, ask, local)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Cont (ContT, runContT, resetT, shiftT)
import Control.Monad.Trans.Except (ExceptT, runExcept)
import Control.Monad.Trans.Reader (Reader, runReader, runReaderT)
import Data.Map (Map, empty, (!?), insert)

typecheck :: Module -> Either String ()
typecheck modl = runExcept $ runReaderT (checkModule modl) $ empty

checkModule :: (MonadError String m, MonadReader Table m) => Module -> m ()
checkModule (Module decls) = go decls
    where
        go :: (MonadError String m, MonadReader Table m) => [Decl] -> m ()
        go [] = pure ()
        go (Declare name ty:decls) = do
            table <- ask
            case run (check [] ty WUniverse) table of
                Left e -> throwError e
                Right () -> case run (whnf [] [] ty handler) table of
                    Left e -> throwError e
                    Right ty -> local (insert name (ty, Nothing)) $ go decls
        go (Define name def:decls) = do
            table <- ask
            case table !? name of
                Nothing -> throwError $ "Not found: " ++ name
                Just (_, Just _) -> throwError $ "Redefined: " ++ name
                Just (ty, Nothing) -> case run (check [] def ty) table of
                    Left e -> throwError e
                    Right () ->
                        local (insert name (ty, Just def)) $ go decls

get [] n = throwError $ "Out of bounds: " ++ show n
get (x:_) 0 = pure x
get (_:xs) n = get xs (n - 1)

newtype Eval r a = Eval
    { eval :: ContT (Either String r) (Reader (Table, Int)) (Either String a) }

run :: Eval a a -> Table -> Either String a
run (Eval e) table = runReader (runContT e pure) (table, 0)

instance Functor (Eval r) where
    fmap f (Eval e) = Eval $ fmap (fmap f) e

instance Applicative (Eval r) where
    pure a = Eval $ pure $ Right a
    (Eval f) <*> (Eval a) = Eval $ (<*>) <$> f <*> a

instance Monad (Eval r) where
    (Eval a) >>= f = Eval $ a >>= go
        where
            go (Left e) = pure $ Left e
            go (Right a) = eval $ f a

instance MonadReader (Table, Int) (Eval r) where
    ask = Eval $ fmap Right ask
    local f (Eval e) = Eval $ local f e

instance MonadError [Char] (Eval r) where
    throwError err = Eval $ pure $ Left err
    catchError (Eval e) handle = Eval $ do
        either <- e
        case either of
            Right a -> pure $ Right a
            Left e -> eval $ handle e

inScope :: (Int -> Eval r a) -> Eval r a
inScope f =
    local (\(table, idx) -> (table, idx + 1))
        (ask >>= \(_, idx) -> f idx)

prompt :: Eval Whnf Whnf -> Eval r Whnf
prompt (Eval m) = Eval $ resetT m

control :: ((Either String Whnf -> ContTy) -> Eval Whnf Whnf) -> Eval Whnf Whnf
control f = Eval $ shiftT (eval . f)

handler _ = Nothing

-- | Evaluate to WHNF.
whnf :: Env -> Conts -> Term -> Handler -> Eval Whnf Whnf
whnf rho kappa (App t u) h = do
    t <- whnf rho kappa t h
    case t of
        WCont k -> do
            u <- whnf rho kappa u h
            Eval $ lift $ (k (Right u))
        WLam _ (Abs rho t) -> whnf (Val v : rho) kappa t h
        WNeu neu -> pure $ WNeu (NApp neu v)
        _ -> throwError "Not a function"
    where v = Clos rho kappa h u
whnf _ kappa (Cont k) _ = pure $ WCont (kappa !! k)
whnf rho kappa (Def global) h = do
    (table, _) <- ask
    case table !? global of
        Just (_, Just def) -> whnf rho kappa def h
        Just (_, Nothing) -> throwError $ "Undefined global " ++ global
        Nothing -> throwError $ "Unbound global " ++ global
whnf rho kappa (Lam a t) h =
    pure $ WLam (fmap (Clos rho kappa h) a) (Abs rho t)
whnf rho kappa (Pair t u) h =
    pure $ WPair (Clos rho kappa h t) (Clos rho kappa h u)
whnf rho kappa (Raise eff) h =
    control $ \k ->
        case h eff of
            Nothing -> throwError $ "Uncaught exception: " ++ eff
            Just t -> whnf rho (k : kappa) t handler
whnf rho kappa (Pi a b) h = pure $ WPi (Clos rho kappa h a) (Abs rho b)
whnf rho kappa (Sigma a b) h = pure $ WSigma (Clos rho kappa h a) (Abs rho b)
whnf _ _ Triv _ = pure WTriv
whnf rho kappa (Try t) h = prompt (whnf rho kappa t h)
whnf _ _ Unit _ = pure WUnit
whnf _ _ Universe _ = pure WUniverse
whnf rho _ (Var v) _ = do
    r <- get rho v
    case r of
        Val val -> whnfVal val
        Free v -> pure $ WNeu (NVar v)

whnfVal :: Val -> Eval Whnf Whnf
whnfVal (Clos rho kappa h t) = whnf rho kappa t h

whnfAbs :: Conts -> Handler -> Abs -> Binding -> Eval Whnf Whnf
whnfAbs kappa h (Abs env t) v = whnf (v:env) kappa t h

unifyWhnf :: Whnf -> Whnf -> Eval r ()
unifyWhnf (WNeu neul) (WNeu neur) = unifyNeu neul neur
unifyWhnf (WLam a t) (WLam b u) = unifyAbs t u
unifyWhnf (WPair a b) (WPair c d) = do
    unifyVal a c
    unifyVal b d
unifyWhnf (WPi a b) (WPi c d) = do
    unifyVal a c
    unifyAbs b d
unifyWhnf (WSigma a b) (WSigma c d) = do
    unifyVal a c
    unifyAbs b d
unifyWhnf WTriv WTriv = pure ()
unifyWhnf WUnit WUnit = pure ()
unifyWhnf WUniverse WUniverse = pure ()
unifyWhnf a b =
    throwError $ "Unify fail: " ++ show a ++ " " ++ show b

unifyNeu :: Neutral -> Neutral -> Eval r ()
unifyNeu (NVar i) (NVar j)
    | i == j = return ()
    | otherwise = throwError "Unify fail"
unifyNeu (NApp nl vl) (NApp nr vr) = do
    unifyNeu nl nr
    unifyVal vl vr
unifyNeu _ _ = throwError "Unify fail"

unifyVal :: Val -> Val -> Eval r ()
unifyVal (Clos rho kappa h t) (Clos rho' kappa' h' u) = do
    t <- prompt $ whnf rho kappa t h
    u <- prompt $ whnf rho' kappa' u h'
    unifyWhnf t u

unifyAbs :: Abs -> Abs -> Eval r ()
unifyAbs (Abs rho t) (Abs rho' u) =
    inScope $ \i -> do
        t <- prompt $ whnf (Free i : rho) [] t handler
        u <- prompt $ whnf (Free i : rho') [] u handler
        unifyWhnf t u

envFromCtx :: [Whnf] -> Env
envFromCtx ls = go (length ls) ls
    where
        go n [] = []
        go n (_:xs) = Free (n - 1) : go (n - 1) xs

infer :: [Whnf] -> Term -> Eval r Whnf
infer gamma (App t u) = do
    fTy <- infer gamma t
    case fTy of
        WPi a b -> do
            a <- prompt $ whnfVal a
            check gamma u a
            prompt $ whnfAbs [] handler b (Val $ Clos (envFromCtx gamma) [] handler u)
        _ -> throwError "Not a pi type"
infer _ (Def global) = do
    (table, _) <- ask
    case table !? global of
        Nothing -> throwError $ "Unbound global " ++ global
        Just (ty, _) -> pure ty
infer gamma (Lam (Just t) u) = do
    check gamma t WUniverse
    t <- prompt $ whnf (envFromCtx gamma) [] t handler
    infer (t:gamma) u
infer _ (Lam Nothing _) =
    throwError "Cannot infer lambda without annotation."
infer _ (Pair _ _) = throwError "Cannot infer pair."
infer gamma (Sigma t u) = do
    check gamma t WUniverse
    t <- prompt $ whnf (envFromCtx gamma) [] t handler
    check (t:gamma) u WUniverse
    pure WUniverse
infer gamma (Pi t u) = do
    check gamma t WUniverse
    t <- prompt $ whnf (envFromCtx gamma) [] t handler
    check (t:gamma) u WUniverse
    pure WUniverse
infer _ Triv = pure WUnit
infer _ Unit = pure WUniverse
infer _ Universe = pure WUniverse
infer gamma (Var n) = get gamma n

check :: [Whnf] -> Term -> Whnf -> Eval r ()
check gamma (Lam Nothing t) (WPi a b) = do
    a <- prompt $ whnfVal a
    inScope $ \i -> do
        b <- prompt $ whnfAbs [] handler b (Free i)
        check (a:gamma) t b
check gamma (Pair t u) (WSigma a b) = do
    a <- prompt $ whnfVal a
    check gamma t a
    b <- prompt $ whnfAbs [] handler b (Val $ Clos (envFromCtx gamma) [] handler t)
    check (a:gamma) u b
check gamma term ty = do
    ty' <- infer gamma term
    unifyWhnf ty ty'
