{-# LANGUAGE ApplicativeDo, FlexibleContexts, FlexibleInstances, FunctionalDependencies #-}
module LazySlice.TypeCheck where

import LazySlice.Syntax
import Control.Monad.Except (MonadError, throwError, catchError, liftEither)
import Control.Monad.Reader (MonadReader, ask, local)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Cont (ContT, runContT, resetT, shiftT)
import Control.Monad.Trans.Except (ExceptT, runExcept)
import Control.Monad.Trans.Reader (Reader, runReader, runReaderT)
import Data.Map (Map, empty, (!?), insert)

typecheck :: Module -> Either String ()
typecheck modl = runExcept $ runReaderT (checkModule modl) $ Table empty empty empty

define :: String -> Whnf -> Def -> Table -> Table
define name ty def table = table { defs = insert name (ty, def) $ defs table }

defineDataCon :: String -> Whnf -> ([Val], String, [Val]) -> Table -> Table
defineDataCon name ty datacon table =
    let table' = table { datacons = insert name datacon $ datacons table } in
    define name ty (Head $ DataCon name) table'

getDef :: Table -> String -> Maybe (Whnf, Def)
getDef table name = defs table !? name

getDatatype :: Table -> String -> Maybe [(String, [Val], [Val])]
getDatatype table name = datatypes table !? name

checkModule :: (MonadError String m, MonadReader Table m) => Module -> m ()
checkModule (Module decls) = go decls
    where
        go :: (MonadError String m, MonadReader Table m) => [Decl] -> m ()
        go [] = pure ()
        go (Data name datacons:decls) = do
            table <- ask
            case getDef table name of
                Nothing -> throwError $ "Not found: " ++ name
                Just (ty, Undef) ->
                    defineDatatype name ty datacons $ go decls
                Just (_, _) -> throwError $ "Redefined: " ++ name
        go (Declare name ty:decls) = do
            table <- ask
            liftEither $ run (check [] ty WUniverse) table
            ty <- liftEither $ run (whnf [] [] ty handler) table
            local (define name ty Undef) $ go decls
        go (Define name def:decls) = do
            table <- ask
            case getDef table name of
                Nothing -> throwError $ "Not found: " ++ name
                Just (ty, Undef) -> do
                    liftEither $ run (check [] def ty) table
                    local (define name ty (Term def)) $ go decls
                Just (_, _) -> throwError $ "Redefined: " ++ name

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

defineDatatype
    :: (MonadError String m, MonadReader Table m)
    => String -> Whnf -> [(String, Term)] -> m a -> m a
defineDatatype typename ty datacons m =
        local (define typename ty (Head $ TypeCon typename))
            $ go [] datacons
    where
        go acc [] =
            local (\table ->
                    table
                        { datatypes =
                            insert typename (reverse acc) $ datatypes table }
                ) m
        go acc ((name, ty):datacons) = do
            table <- ask
            case getDef table name of
                Just _ -> throwError $ "Redefined: " ++ name
                Nothing -> do
                    liftEither $ run (check [] ty WUniverse) table
                    ty <- liftEither $ run (prompt $ whnf [] [] ty handler) table
                    datacon@(tele, _, tyargs) <- getTele typename ty
                    local (defineDataCon name ty datacon)
                        $ go ((name, tele, tyargs):acc) datacons

getTele
    :: (MonadError String m, MonadReader Table m)
    => String -> Whnf -> m ([Val], String, [Val])
getTele name = go 0
    where
        go i (WPi a b) = do
                table <- ask
                b <- liftEither $ run (prompt $ whnfAbs [] handler b (Free i)) table
                (tele, typecon, typeargs) <- go (i + 1) b
                pure (a:tele, typecon, typeargs)
        go i (WNeu (TypeCon name') spine)
            | name' == name = pure ([], name, spine)
            | otherwise =
                throwError $ "Invalid constructor type: " ++ name' ++ " not " ++ name
        go i ty =
            throwError $ "Invalid constructor type: " ++ show ty

-- | Evaluate to WHNF.
whnf :: Env -> Conts -> Term -> Handler -> Eval Whnf Whnf
whnf rho kappa (App t u) h = do
    t <- whnf rho kappa t h
    case t of
        WCont k -> do
            u <- whnf rho kappa u h
            Eval $ lift $ (k (Right u))
        WLam _ (Abs rho t) -> whnf (Val v : rho) kappa t h
        WNeu hd spine -> pure $ WNeu hd $ v:spine
        _ -> throwError "Not a function"
    where v = Clos rho kappa h u
whnf _ kappa (Cont k) _ = pure $ WCont (kappa !! k)
whnf rho kappa (Def global) h = do
    (table, _) <- ask
    case getDef table global of
        Just (_, Head hd) -> pure $ WNeu hd []
        Just (_, Term def) -> whnf rho kappa def h
        Just (_, Undef) -> throwError $ "Undefined global " ++ global
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
        Free v -> pure $ WNeu (FreeVar v) []

whnfVal :: Val -> Eval Whnf Whnf
whnfVal (Clos rho kappa h t) = whnf rho kappa t h

whnfAbs :: Conts -> Handler -> Abs -> Binding -> Eval Whnf Whnf
whnfAbs kappa h (Abs env t) v = whnf (v:env) kappa t h

unifyWhnf :: Whnf -> Whnf -> Eval r ()
unifyWhnf (WNeu hdl spinel) (WNeu hdr spiner)
    | hdl == hdr = mapM_ (uncurry unifyVal) $ zip spinel spiner
    | otherwise =
        throwError
            $ "Unify fail: " ++ show hdl ++ " " ++ show hdr
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
    case getDef table global of
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

-- TODO: Implement dependent pattern matching

type PatConstraint = [(Int, Whnf, Pattern)]
data Clause = C Int PatConstraint [Pattern] Term

elabPats :: [Clause] -> Whnf -> Eval r CaseTree
elabPats [] _ = throwError "Incomplete pattern match"
elabPats (clauses@(C _ e [] term:_)) ty = case findRefut e of
        Nothing -> do
            check [] term ty
            pure $ Leaf term
        Just (v, ty) -> do
            datacons <- case ty of
                WNeu (TypeCon name) spine -> do
                    (table, _) <- ask
                    case datatypes table !? name of
                        Nothing ->
                            throwError $ "Undefined: " ++ name
                        Just datacons -> pure datacons
                ty -> throwError $ "Not a datatype: " ++ show ty
            cases <- split datacons v clauses
            pure $ Split v cases
    where
        -- Find a constraint in the form (x / c v...) and
        -- return the variable x and its type
        findRefut :: PatConstraint -> Maybe (Int, Whnf)
        findRefut [] = Nothing
        findRefut ((v, ty, ConPat _ _):e) = Just (v, ty)
        findRefut ((_, _, VarPat _):e) = findRefut e

        -- Split var on a datatype.
        split [] var clauses = pure []
        split ((name, innerTys, _):datacons) var clauses = do
            clauses <- refine name innerTys var clauses
            branch <- elabPats clauses ty
            xs <- split datacons var clauses
            pure $ (name, undefined, branch):xs

        -- Remove impossible constraints from the clauses.
        refine name innerTys var [] = pure []
        refine name innerTys var (C varGen e pats rhs:clauses) = do
            maybe <- filterE varGen [] name innerTys var e
            next <- refine name innerTys var clauses
            case maybe of
                Nothing -> pure next
                Just (varGen, vars, e) ->
                    pure $ C varGen e pats rhs : next

        -- Remove constraints that fail the refinement.
        filterE varGen acc name innerTys var [] = pure Nothing
        filterE varGen acc name innerTys var ((c@(var', _, pat)):e)
            | var == var' = case pat of
                ConPat name' pats
                    | name == name' -> do
                        (varGen', e') <- fresh varGen innerTys pats
                        pure
                            $ Just
                            $ ( varGen'
                              , Just $ fmap (\(v, _, _) -> v) e'
                              , acc ++ e' ++ e )
                    | otherwise -> pure Nothing
                VarPat s ->
                    pure $ Just (varGen, Nothing, acc ++ c:e)
            | otherwise =
                filterE varGen (c:acc) name innerTys var e

        fresh varGen [] [] = pure (varGen, [])
        fresh varGen (ty:tys) (pat:pats) = do
            ty <- prompt $ whnfVal ty
            (varGen', e) <- fresh (varGen + 1) tys pats
            pure (varGen', (varGen, ty, pat):e)
elabPats (C varGen e (pat:pats) rhs:clauses) (WPi a b) = do
        a <- prompt $ whnfVal a
        b <- prompt $ whnfAbs [] handler b (Free varGen)
        clauses <- liftEither $ intro a clauses
        Intro varGen
            <$> elabPats
                (C (varGen + 1) e (pat:pats) rhs : clauses) b
    where
        intro :: Whnf -> [Clause] -> Either String [Clause]
        intro _ [] = Right []
        intro a (C varGen e (pat:pats) rhs:clauses) = do
            rest <- intro a clauses
            Right
                $ (C (varGen + 1) ((varGen, a, pat):e) pats rhs):rest
        intro _ (C _ _ [] _ : _) = Left "Missing patterns"
elabPats _ _ = throwError "Nothing to do?"
