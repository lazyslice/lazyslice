{-# LANGUAGE ApplicativeDo, FlexibleContexts, FlexibleInstances, FunctionalDependencies #-}
module LazySlice.TypeCheck where

import qualified LazySlice.Sexp as Sexp
import LazySlice.Syntax
import qualified LazySlice.Quote as Quote
import Control.Monad.Except (MonadError, throwError, catchError, liftEither)
import Control.Monad.Reader (MonadReader, ask, local)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Cont (ContT, runContT, resetT, shiftT)
import Control.Monad.Trans.Except (ExceptT, runExcept)
import Control.Monad.Trans.Reader (Reader, runReader, runReaderT)
import Data.Map (Map, empty, singleton, (!?), insert, union, fromList)

quote = Sexp.quoteSexp . Sexp.quoteExpr . Quote.quoteWhnf

typecheck :: Module -> Either String ()
typecheck modl = runExcept $ runReaderT (checkModule modl) $ Table empty empty empty

define :: String -> Whnf -> Def -> Table -> Table
define name ty def table = table { defs = insert name (ty, def) $ defs table }

defineDataCon :: String -> String -> Whnf -> Table -> Table
defineDataCon typename name ty table =
    let table' = table
            { datacons = insert name (typename, ty) $ datacons table } 
    in
    define name ty (Head $ DataCon name) table'

getDef :: Table -> String -> Maybe (Whnf, Def)
getDef table name = defs table !? name

getDatatype :: Table -> String -> Maybe [(String, Whnf)]
getDatatype table name = datatypes table !? name

topCheck def ty = do
    table <- ask
    case run (check empty [] def ty) table of
        Right r -> pure r
        Left e ->
            throwError
                $ "Expected type: " ++ quote ty ++ "\n" ++ e

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
            topCheck ty WUniverse
            ty <-
                liftEither
                    $ run (whnf empty empty [] [] ty handler) table
            local (define name ty Undef) $ go decls
        go (Define name def:decls) = do
            table <- ask
            case getDef table name of
                Nothing -> throwError $ "Not found: " ++ name
                Just (ty, Undef) -> do
                    topCheck def ty
                    local (define name ty (Term def)) $ go decls
                Just (_, _) -> throwError $ "Redefined: " ++ name
        go (Defun name clauses:decls) = do
            table <- ask
            case getDef table name of
                Nothing -> throwError $ "Not found: " ++ name
                Just (ty, Undef) -> do
                    tree <- elabPats (PV 0) (fmap toClause clauses) ty
                    local (define name ty $ Head $ Fun name tree)
                        $ go decls
                Just (_, _) -> throwError $ "Redefined: " ++ name

        toClause (pats, term) = C empty [] pats term

get [] n = throwError $ "Out of bounds: " ++ show n
get (x:_) 0 = pure x
get (_:xs) n = get xs (n - 1)

newtype Eval r a = Eval
    { eval :: ContT (Either String r) (Reader EvalState) (Either String a) }

run :: Eval a a -> Table -> Either String a
run (Eval e) table =
    runReader (runContT e pure) $ EvalState table 0

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

instance MonadReader EvalState (Eval r) where
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
inScope f = do
    idx <- fmap index ask
    local (\s -> s { index = index s + 1 })
        (f idx)

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
                    liftEither $ run (check empty [] ty WUniverse) table
                    ty <- liftEither $ run (prompt $ whnf empty empty [] [] ty handler) table
                    getTele typename ty
                    local (defineDataCon typename name ty)
                        $ go ((name, ty):acc) datacons

getTele
    :: (MonadError String m, MonadReader Table m)
    => String -> Whnf -> m ([Val], String, [Val])
getTele name = go 0
    where
        go i (WPi a b) = do
                table <- ask
                b <-
                    liftEither $ run (prompt $ whnfAbs [] handler b (Free i)) table
                (tele, typecon, typeargs) <- go (i + 1) b
                pure (a:tele, typecon, typeargs)
        go i (WNeu (TypeCon name') spine)
            | name' == name = pure ([], name, spine)
            | otherwise =
                throwError $ "Invalid constructor type: " ++ name' ++ " not " ++ name
        go i ty =
            throwError
                $ "Invalid constructor type: " ++ quote ty

-- | Evaluate to WHNF.
whnf
    :: PatEnv
    -> MatchEnv
    -> Env
    -> Conts
    -> Term
    -> Handler
    -> Eval Whnf Whnf
whnf metavars menv rho kappa (App t u) h = do
    t <- whnf metavars menv rho kappa t h
    case t of
        WCont k -> do
            u <- whnf metavars menv rho kappa u h
            Eval $ lift $ (k (Right u))
        WLam _ (Abs metavars menv rho t) ->
            whnf metavars menv (Val v : rho) kappa t h
        WNeu hd spine -> pure $ WNeu hd $ v:spine
        _ -> throwError "Not a function"
    where v = Clos metavars menv rho kappa h u
whnf _ _ _ kappa (Cont k) _ = pure $ WCont (kappa !! k)
whnf metavars menv rho kappa (Def global) h = do
    table <- table <$> ask
    case getDef table global of
        Just (_, Head hd) -> pure $ WNeu hd []
        Just (_, Term def) ->
            whnf metavars menv rho kappa def h
        Just (_, Undef) ->
            throwError $ "Undefined global " ++ global
        Nothing -> throwError $ "Unbound global " ++ global
whnf metavars menv rho kappa (Lam a t) h =
    pure $ WLam (fmap (Clos metavars menv rho kappa h) a)
            (Abs metavars menv rho t)
whnf metavars menv rho kappa (Pair t u) h =
    pure $ WPair (Clos metavars menv rho kappa h t)
                (Clos metavars menv rho kappa h u)
whnf metavars menv rho kappa (Raise eff) h =
    control $ \k ->
        case h eff of
            Nothing -> throwError $ "Uncaught exception: " ++ eff
            Just t -> whnf metavars menv rho (k : kappa) t handler
whnf metavars menv rho kappa (Pi a b) h =
    pure $ WPi (Clos metavars menv rho kappa h a)
                (Abs metavars menv rho b)
whnf metavars menv rho kappa (Sigma a b) h =
    pure $ WSigma (Clos metavars menv rho kappa h a)
                    (Abs metavars menv rho b)
whnf _ _ _ _ Triv _ = pure WTriv
whnf metavars menv rho kappa (Try t) h =
    prompt (whnf metavars menv rho kappa t h)
whnf _ _ _ _ Unit _ = pure WUnit
whnf _ _ _ _ Universe _ = pure WUniverse
whnf metavars menv _ _ (MatchVar v) _ = case menv !? v of
    Just val -> whnfVal val
    Nothing -> pure $ WNeu (MatVar v) []
whnf metavars _ rho _ (Var v) _ = do
    r <- get rho v
    case r of
        Val val -> whnfVal val
        Free v -> pure $ WNeu (FreeVar v) []
        Pat v -> case metavars !? v of
            Just whnf -> pure whnf
            Nothing -> pure $ WNeu (PatVar v) []

whnfVal :: Val -> Eval Whnf Whnf
whnfVal (Clos metavars menv rho kappa h t) =
    whnf metavars menv rho kappa t h
whnfVal (Whnf whnf) = pure whnf

whnfAbs :: Conts -> Handler -> Abs -> Binding -> Eval Whnf Whnf
whnfAbs kappa h (Abs metavars menv env t) v =
    whnf metavars menv (v:env) kappa t h

applySubstVal :: Val -> PatEnv -> Eval r Val
applySubstVal (Clos metavars menv rho kappa h t) subst =
    pure (Clos (union metavars subst) menv rho kappa h t)
applySubstVal (Whnf whnf) subst = do
    whnf <- applySubstWhnf whnf subst
    pure $ Whnf whnf

applySubstAbs :: Abs -> PatEnv -> Abs
applySubstAbs (Abs metavars menv env t) subst =
    Abs (union metavars subst) menv env t

applySubstWhnf (WNeu (PatVar pv) []) subst =
    case subst !? pv of
        Nothing -> pure $ WNeu (PatVar pv) []
        Just def -> pure $ def
applySubstWhnf (WNeu (PatVar pv) spine) subst =
    case subst !? pv of
        Nothing -> do
            spine <- mapM (flip applySubstVal subst) spine
            pure $ WNeu (PatVar pv) spine
        Just (WNeu hd spine') ->
            pure $ WNeu hd (spine ++ spine')
        Just (WLam _ t) -> undefined
applySubstWhnf (WNeu hd spine) subst = do
    spine <- mapM (flip applySubstVal subst) spine
    pure $ WNeu hd spine
applySubstWhnf (WLam a t) subst = do
    a <- mapM (flip applySubstVal subst) a
    pure $ WLam a (applySubstAbs t subst)
applySubstWhnf (WSigma a b) subst = do
    a <- applySubstVal a subst
    pure $ WSigma a (applySubstAbs b subst)
applySubstWhnf (WPi a b) subst = do
    a <- applySubstVal a subst
    pure $ WPi a (applySubstAbs b subst)
applySubstWhnf (WPair a b) subst = do
    a <- applySubstVal a subst
    b <- applySubstVal b subst
    pure $ WPair a b
applySubstWhnf WTriv _ = pure WTriv
applySubstWhnf WUnit _ = pure WUnit
applySubstWhnf WUniverse _ = pure WUniverse

unifyWhnf :: Whnf -> Whnf -> Eval r PatEnv
unifyWhnf (WNeu hdl spinel) (WNeu hdr spiner) =
    unifyNeu hdl spinel hdr spiner
unifyWhnf (WLam a t) (WLam b u) = unifyAbs t u
unifyWhnf (WPair a b) (WPair c d) = do
    subst <- unifyVal a c
    b <- applySubstVal b subst
    d <- applySubstVal d subst
    subst' <- unifyVal b d
    pure $ union subst subst'
unifyWhnf (WPi a b) (WPi c d) = do
    subst <- unifyVal a c
    subst' <-
        unifyAbs (applySubstAbs b subst) (applySubstAbs d subst)
    pure $ union subst subst'
unifyWhnf (WSigma a b) (WSigma c d) = do
    subst <- unifyVal a c
    subst' <-
        unifyAbs (applySubstAbs b subst) (applySubstAbs d subst)
    pure $ union subst subst'
unifyWhnf WTriv WTriv = pure empty
unifyWhnf WUnit WUnit = pure empty
unifyWhnf WUniverse WUniverse = pure empty
unifyWhnf (WNeu (PatVar pv) []) b =
    pure $ singleton pv b
unifyWhnf a (WNeu (PatVar pv) []) =
    pure $ singleton pv a
unifyWhnf a b =
    throwError $ "Unify fail: " ++ quote a ++ " " ++ quote b

unifyNeu :: Head -> [Val] -> Head -> [Val] -> Eval r PatEnv
unifyNeu hdl (l:ls) hdr (r:rs) = do
    subst <- unifyVal l r
    ls <- mapM (flip applySubstVal subst) ls
    rs <- mapM (flip applySubstVal subst) rs
    subst' <- unifyNeu hdl ls hdr rs
    pure $ union subst subst'
unifyNeu (PatVar pv) [] hdr rs
    -- TODO: Substitute
    | hdr == PatVar pv = pure empty
    | otherwise = pure (singleton pv (WNeu hdr rs))
unifyNeu hdl ls (PatVar pv) []
    -- TODO: Substitute
    | hdl == PatVar pv = pure empty
    | otherwise = pure (singleton pv (WNeu hdl ls))
unifyNeu hdl [] hdr []
    | hdl == hdr = pure empty
    | otherwise =
        throwError $ "Unify fail: " ++ quote (WNeu hdl []) ++ " " ++ quote (WNeu hdr [])
unifyNeu hdl [] hdr rs =
    throwError
        $ "Unify fail: " ++ quote (WNeu hdl []) ++ " " ++ quote (WNeu hdr rs)
unifyNeu hdl ls hdr [] =
    throwError
        $ "Unify fail: " ++ quote (WNeu hdl ls) ++ " " ++ quote (WNeu hdr [])

unifyVal :: Val -> Val -> Eval r PatEnv
unifyVal t u = do
    t <- prompt $ whnfVal t
    u <- prompt $ whnfVal u
    unifyWhnf t u

unifyAbs :: Abs -> Abs -> Eval r PatEnv
unifyAbs (Abs metavars menv rho t) (Abs metavars' menv' rho' u) =
    inScope $ \i -> do
        t <- prompt
            $ whnf metavars menv (Free i : rho) [] t handler
        u <- prompt
            $ whnf metavars' menv' (Free i : rho') [] u handler
        unifyWhnf t u

envFromCtx :: [Whnf] -> Env
envFromCtx ls = go (length ls) ls
    where
        go n [] = []
        go n (_:xs) = Free (n - 1) : go (n - 1) xs

infer :: PatCtx -> [Whnf] -> Term -> Eval r (PatEnv, Whnf)
infer pgamma gamma (App t u) = do
    (subst, fTy) <- infer pgamma gamma t
    case fTy of
        WPi a b -> do
            a <- applySubstVal a subst
            a <- prompt $ whnfVal a
            subst' <- check pgamma gamma u a
            let subst'' = union subst subst'
            let b' = applySubstAbs b subst''
            res <- prompt
                    $ whnfAbs [] handler b'
                        (Val $ Clos subst'' empty (envFromCtx gamma) [] handler u)
            pure (subst'', res)
        _ -> throwError "Not a pi type"
infer _ _ (Def global) = do
    table <- table <$> ask
    case getDef table global of
        Nothing -> throwError $ "Unbound global " ++ global
        Just (ty, _) -> pure (empty, ty)
infer pgamma gamma (Lam (Just t) u) = do
    subst <- check pgamma gamma t WUniverse
    t <- prompt $ whnf subst empty (envFromCtx gamma) [] t handler
    (subst', ty) <- infer pgamma (t:gamma) u
    pure (union subst subst', ty)
infer _ _ (Lam Nothing _) =
    throwError "Cannot infer lambda without annotation."
infer _ _ (Pair _ _) = throwError "Cannot infer pair."
infer pgamma gamma (Sigma t u) = do
    subst <- check pgamma gamma t WUniverse
    t <- prompt $ whnf subst empty (envFromCtx gamma) [] t handler
    subst' <- check pgamma (t:gamma) u WUniverse
    pure (union subst subst', WUniverse)
infer pgamma gamma (Pi t u) = do
    subst <- check pgamma gamma t WUniverse
    t <- prompt $ whnf subst empty (envFromCtx gamma) [] t handler
    subst' <- check pgamma (t:gamma) u WUniverse
    pure (union subst subst', WUniverse)
infer _ _ Triv = pure (empty, WUnit)
infer _ _ Unit = pure (empty, WUniverse)
infer _ _ Universe = do
    pure (empty, WUniverse)
infer pgamma _ (MatchVar name) = case pgamma !? name of
    Nothing -> throwError $ "Not found: " ++ show name
    Just ty -> pure (empty, ty)
infer _ gamma (Var n) = do
    ty <- get gamma n
    pure (empty, ty)

check :: PatCtx -> [Whnf] -> Term -> Whnf -> Eval r PatEnv
check pgamma gamma (Lam Nothing t) (WPi a b) = do
    a <- prompt $ whnfVal a
    inScope $ \i -> do
        b <- prompt $ whnfAbs [] handler b (Free i)
        check pgamma (a:gamma) t b
check pgamma gamma (Pair t u) (WSigma a b) = do
    a <- prompt $ whnfVal a
    subst <- check pgamma gamma t a
    b <- prompt
        $ whnfAbs [] handler (applySubstAbs b subst)
        (Val $ Clos empty empty (envFromCtx gamma) [] handler t)
    subst' <- check pgamma (a:gamma) u b
    pure $ union subst subst'
check pgamma gamma term ty = do
    (subst, ty') <- infer pgamma gamma term
    ty <- applySubstWhnf ty subst
    subst' <- unifyWhnf ty ty'
    pure $ union subst subst'

-- TODO: Implement dependent pattern matching

type PatConstraint = [(PatternVar, Whnf, Pattern)]
type PatCtx = Map MatchVar Whnf
data Clause = C PatCtx PatConstraint [Pattern] Term
data Refutability
    = Refut PatternVar Whnf
    | Irrefut [(MatchVar, PatternVar, Whnf)]

elabPats
    :: (MonadError String m, MonadReader Table m)
    => PatternVar -> [Clause] -> Whnf -> m CaseTree
elabPats _ [] _ = throwError "Incomplete pattern match"
elabPats varGen (clauses@(C pctx e [] term:_)) ty =
    case refut e of
        Irrefut vars -> do
            let pctx' = union pctx
                    $ fromList
                    $ fmap (\(mv, pv, ty) -> (mv, ty)) vars
            table <- ask
            liftEither $ run (check pctx' [] term ty) table
            pure $ Leaf term
        Refut v ty -> do
            datacons <- case ty of
                WNeu (TypeCon name) spine -> do
                    table <- ask
                    case datatypes table !? name of
                        Nothing ->
                            throwError $ "Undefined: " ++ name
                        Just datacons -> pure datacons
                ty -> throwError $ "Not a datatype: " ++ quote ty
            cases <- split datacons v ty clauses
            pure $ Split v cases
    where
        -- Find a constraint in the form (x / c v...).
        refut :: PatConstraint -> Refutability
        refut [] = Irrefut []
        refut ((v, ty, ConPat _ _):e) = Refut v ty
        refut ((v, ty, VarPat v'):e) = case refut e of
            Irrefut ls -> Irrefut ((v', v, ty):ls)
            Refut v ty -> Refut v ty
        refut ((v, ty, WildPat):e) = refut e

        -- Split var on a datatype.
        split [] var varTy clauses = pure []
        split ((name, conTy):datacons) var varTy clauses = do
            xs <- split datacons var varTy clauses
            (varGen, vts, outTy) <- inst varGen conTy
            table <- ask
            case run (unifyWhnf outTy varTy) table of
                Right subst -> do
                    vts <-
                        liftEither
                            $ run (mapM (mapM (flip applySubstWhnf subst)) vts) table
                    ty <- liftEither $ run (applySubstWhnf ty subst) table
                    clauses' <- refine name var vts subst clauses
                    table <- ask
                    branch <- elabPats varGen clauses' ty
                    pure $ (name, fmap fst vts, branch):xs
                -- Type error means impossible case
                Left e -> pure xs

        -- Instantiate the datacon's telescope type
        inst varGen (WPi a b) = do
            table <- ask
            a <- liftEither $ run (whnfVal a) table
            b <- liftEither $ run (prompt $ whnfAbs [] handler b (Val $ Whnf $ WNeu (PatVar varGen) [])) table
            (varGen', rest, outTy) <- inst (nextPV varGen) b
            pure (varGen', (varGen, a):rest, outTy)
        inst varGen ty@(WNeu _ _) = pure (varGen, [], ty)

        -- Remove clauses with impossible constraints.
        refine name var vts subst [] = pure []
        refine name var vts subst (C pctx e pats rhs:clauses) = do
            table <- ask
            e <- liftEither $ run (mapM (\(var, ty, pat) -> do
                        ty <- applySubstWhnf ty subst
                        pure (var, ty, pat)
                    ) e) table
            maybe <- filt [] name var vts e
            next <- refine name var vts subst clauses
            case maybe of
                Nothing -> pure next
                Just (Nothing, e) ->
                    pure $ C pctx e pats rhs : next
                Just (Just (v, ty), e) ->
                    pure $ C (insert v ty pctx) e pats rhs : next

        -- Remove constraints that fail the refinement.
        filt acc name var vts [] = pure Nothing
        filt acc name var vts ((c@(var', ty, pat)):e)
            | var == var' = case pat of
                ConPat name' pats
                    | name == name' -> do
                        e' <- tie vts pats
                        pure $ Just (Nothing, acc ++ e' ++ e)
                    | otherwise -> pure Nothing
                VarPat s -> pure $ Just (Just (s, ty), acc ++ c:e)
            | otherwise = filt (c:acc) name var vts e

        tie [] [] = pure []
        tie [] (_:_) = throwError "Too many patterns!"
        tie (_:_) [] = throwError "Not enough patterns!"
        tie ((v, ty):vts) (pat:pats) = do
            rest <- tie vts pats
            pure $ (v, ty, pat):rest

elabPats varGen clauses (WPi a b) = do
        table <- ask
        a <- liftEither $ run (prompt $ whnfVal a) table
        b <- liftEither
            $ run (prompt $ whnfAbs [] handler b $ Pat varGen) table
        clauses <- liftEither $ intro a clauses
        Intro varGen <$> elabPats (nextPV varGen) clauses b
    where
        intro :: Whnf -> [Clause] -> Either String [Clause]
        intro _ [] = Right []
        intro a (C pctx e (pat:pats) rhs:clauses) = do
            rest <- intro a clauses
            Right $ C pctx ((varGen, a, pat):e) pats rhs : rest
        intro _ (C _ _ [] _ : _) = Left "Missing patterns"
elabPats _ _ _ =
    throwError "Pattern present, but type isn't a pi type"
