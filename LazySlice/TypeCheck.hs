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
            ty <- liftEither $ run (whnf empty [] [] ty handler) table
            local (define name ty Undef) $ go decls
        go (Define name def:decls) = do
            table <- ask
            case getDef table name of
                Nothing -> throwError $ "Not found: " ++ name
                Just (ty, Undef) -> do
                    liftEither $ run (check [] def ty) table
                    local (define name ty (Term def)) $ go decls
                Just (_, _) -> throwError $ "Redefined: " ++ name
        go (Defun name clauses:decls) = do
            table <- ask
            case getDef table name of
                Nothing -> throwError $ "Not found: " ++ name
                Just (ty, Undef) -> do
                    go decls
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
                    ty <- liftEither $ run (prompt $ whnf empty [] [] ty handler) table
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
whnf :: MatchEnv -> Env -> Conts -> Term -> Handler -> Eval Whnf Whnf
whnf menv rho kappa (App t u) h = do
    t <- whnf menv rho kappa t h
    case t of
        WCont k -> do
            u <- whnf menv rho kappa u h
            Eval $ lift $ (k (Right u))
        WLam _ (Abs menv rho t) -> whnf menv (Val v : rho) kappa t h
        WNeu hd spine -> pure $ WNeu hd $ v:spine
        _ -> throwError "Not a function"
    where v = Clos menv rho kappa h u
whnf _ _ kappa (Cont k) _ = pure $ WCont (kappa !! k)
whnf menv rho kappa (Def global) h = do
    (table, _) <- ask
    case getDef table global of
        Just (_, Head hd) -> pure $ WNeu hd []
        Just (_, Term def) -> whnf menv rho kappa def h
        Just (_, Undef) -> throwError $ "Undefined global " ++ global
        Nothing -> throwError $ "Unbound global " ++ global
whnf menv rho kappa (Lam a t) h =
    pure $ WLam (fmap (Clos menv rho kappa h) a) (Abs menv rho t)
whnf menv rho kappa (Pair t u) h =
    pure $ WPair (Clos menv rho kappa h t) (Clos menv rho kappa h u)
whnf menv rho kappa (Raise eff) h =
    control $ \k ->
        case h eff of
            Nothing -> throwError $ "Uncaught exception: " ++ eff
            Just t -> whnf menv rho (k : kappa) t handler
whnf menv rho kappa (Pi a b) h =
    pure $ WPi (Clos menv rho kappa h a) (Abs menv rho b)
whnf menv rho kappa (Sigma a b) h =
    pure $ WSigma (Clos menv rho kappa h a) (Abs menv rho b)
whnf _ _ _ Triv _ = pure WTriv
whnf menv rho kappa (Try t) h = prompt (whnf menv rho kappa t h)
whnf _ _ _ Unit _ = pure WUnit
whnf _ _ _ Universe _ = pure WUniverse
whnf menv _ _ (MatchVar v) _ = case menv !? v of
    Just val -> whnfVal val
    Nothing -> throwError $ "Match variable not found: " ++ show v
whnf _ rho _ (Var v) _ = do
    r <- get rho v
    case r of
        Val val -> whnfVal val
        Free v -> pure $ WNeu (FreeVar v) []
        Pat v -> pure $ WNeu (PatVar v) []

whnfVal :: Val -> Eval Whnf Whnf
whnfVal (Clos menv rho kappa h t) = whnf menv rho kappa t h
whnfVal (Whnf whnf) = pure whnf

whnfAbs :: Conts -> Handler -> Abs -> Binding -> Eval Whnf Whnf
whnfAbs kappa h (Abs menv env t) v = whnf menv (v:env) kappa t h

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
unifyVal t u = do
    t <- prompt $ whnfVal t
    u <- prompt $ whnfVal u
    unifyWhnf t u

unifyAbs :: Abs -> Abs -> Eval r ()
unifyAbs (Abs menv rho t) (Abs menv' rho' u) =
    inScope $ \i -> do
        t <- prompt $ whnf menv (Free i : rho) [] t handler
        u <- prompt $ whnf menv' (Free i : rho') [] u handler
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
            prompt $ whnfAbs [] handler b (Val $ Clos empty (envFromCtx gamma) [] handler u)
        _ -> throwError "Not a pi type"
infer _ (Def global) = do
    (table, _) <- ask
    case getDef table global of
        Nothing -> throwError $ "Unbound global " ++ global
        Just (ty, _) -> pure ty
infer gamma (Lam (Just t) u) = do
    check gamma t WUniverse
    t <- prompt $ whnf empty (envFromCtx gamma) [] t handler
    infer (t:gamma) u
infer _ (Lam Nothing _) =
    throwError "Cannot infer lambda without annotation."
infer _ (Pair _ _) = throwError "Cannot infer pair."
infer gamma (Sigma t u) = do
    check gamma t WUniverse
    t <- prompt $ whnf empty (envFromCtx gamma) [] t handler
    check (t:gamma) u WUniverse
    pure WUniverse
infer gamma (Pi t u) = do
    check gamma t WUniverse
    t <- prompt $ whnf empty (envFromCtx gamma) [] t handler
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
    b <- prompt $ whnfAbs [] handler b (Val $ Clos empty (envFromCtx gamma) [] handler t)
    check (a:gamma) u b
check gamma term ty = do
    ty' <- infer gamma term
    unifyWhnf ty ty'

-- TODO: Implement dependent pattern matching

type PatConstraint = [(PatternVar, Whnf, Pattern)]
data Clause = C PatternVar PatConstraint [Pattern] Term
data Refutability = Refut PatternVar Whnf | Irrefut [(MatchVar, PatternVar)]

elabPats
    :: (MonadError String m, MonadReader Table m)
    => [Clause] -> Whnf -> m CaseTree
elabPats [] _ = throwError "Incomplete pattern match"
elabPats (clauses@(C _ e [] term:_)) ty = case refut e of
        Irrefut _ -> do
            table <- ask
            liftEither $ run (check [] term ty) table
            pure $ Leaf term
        Refut v ty -> do
            datacons <- case ty of
                WNeu (TypeCon name) spine -> do
                    table <- ask
                    case datatypes table !? name of
                        Nothing ->
                            throwError $ "Undefined: " ++ name
                        Just datacons -> pure datacons
                ty -> throwError $ "Not a datatype: " ++ show ty
            cases <- split datacons v clauses
            pure $ Split v cases
    where
        -- Find a constraint in the form (x / c v...)
        refut :: PatConstraint -> Refutability
        refut [] = Irrefut []
        refut ((v, ty, ConPat _ _):e) = Refut v ty
        refut ((v, _, VarPat v'):e) = case refut e of
            Irrefut ls -> Irrefut ((v', v):ls)
            Refut v ty -> Refut v ty

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
            maybe <- filt varGen [] name innerTys var e
            next <- refine name innerTys var clauses
            case maybe of
                Nothing -> pure next
                Just (varGen, vars, e) ->
                    pure $ C varGen e pats rhs : next

        -- Remove constraints that fail the refinement.
        filt varGen acc name innerTys var [] = pure Nothing
        filt varGen acc name innerTys var ((c@(var', _, pat)):e)
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
                filt varGen (c:acc) name innerTys var e

        fresh varGen [] [] = pure (varGen, [])
        fresh _ [] (_:_) = throwError "Too many patterns!"
        fresh _ (_:_) [] = throwError "Not enough patterns!"
        fresh varGen (ty:tys) (pat:pats) = do
            table <- ask
            ty <- liftEither $ run (prompt $ whnfVal ty) table
            (varGen', e) <- fresh (nextPV varGen) tys pats
            pure (varGen', (varGen, ty, pat):e)
elabPats clauses@(C varGen _ _ _:_) (WPi a b) = do
        table <- ask
        a <- liftEither $ run (prompt $ whnfVal a) table
        b <- liftEither
            $ run (prompt $ whnfAbs [] handler b $ Pat varGen) table
        clauses <- liftEither $ intro a clauses
        Intro varGen <$> elabPats clauses b
    where
        intro :: Whnf -> [Clause] -> Either String [Clause]
        intro _ [] = Right []
        intro a (C varGen e (pat:pats) rhs:clauses) = do
            rest <- intro a clauses
            Right
                $ C (nextPV varGen) ((varGen, a, pat):e) pats rhs : rest
        intro _ (C _ _ [] _ : _) = Left "Missing patterns"
elabPats _ _ = throwError "Nothing to do?"
