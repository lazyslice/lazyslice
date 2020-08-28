{-# LANGUAGE FlexibleContexts #-}
module LazySlice.Resolve where

import LazySlice.AST as AST
import LazySlice.Syntax as Syn
import Control.Monad.Except (MonadError, throwError, liftEither)
import Control.Monad.Reader (MonadReader, ask, local)
import Control.Monad.Trans.Reader (runReaderT)
import Control.Monad.Trans.Except (runExcept)
import Data.Map (Map, (!?), empty, insert, union)

data Name = Local Int | Global String | PatV Syn.MatchVar

data Symtable = Symtable
    { vars :: Map String Name }

resolve :: AST.Module -> Either String Syn.Module
resolve modl = runExcept $ runReaderT (resolveModule modl) $ Symtable empty

resolveModule :: (MonadError String m, MonadReader Symtable m) => AST.Module -> m Syn.Module
resolveModule (AST.Module decls) = do
        defs <- go decls
        pure $ Syn.Module defs
    where
        go :: (MonadError String m, MonadReader Symtable m)
           => [AST.Decl] -> m [Syn.Decl]
        go [] = pure []
        go (AST.Data name def:decls) = global name $ do
            resolveDatatype def $ \def -> do
                rest <- go decls
                pure $ Syn.Data name def:rest
        go (AST.Declare name ty:decls) = do
            ty <- resolveExpr ty
            rest <- global name $ go decls
            pure $ Syn.Declare name ty:rest
        go (AST.Define name expr:decls) = do
            expr <- resolveExpr expr
            rest <- go decls
            pure $ Syn.Define name expr:rest
        go (AST.Defun name clauses:decls) = do
            clauses <- resolveFun clauses
            rest <- go decls
            pure $ Syn.Defun name clauses:rest

global :: (MonadReader Symtable m) => String -> m a -> m a
global name =
    local $ \symtable ->
        Symtable { vars = insert name (Global name) $ vars symtable }

intro :: MonadReader Symtable m => String -> m Syn.Term -> m Syn.Term
intro name = local $ \symtable ->
        let vs = vars symtable in
        symtable { vars = insert name (Local 0) $ fmap up vs }
    where
        up (Local v) = Local $ v + 1
        up other = other

resolveDatatype
    :: (MonadError String m, MonadReader Symtable m)
    => [(String, AST.Expr)] -> ([(String, Syn.Term)] -> m a) -> m a
resolveDatatype [] k = k []
resolveDatatype ((name, expr):xs) k = do
    expr <- resolveExpr expr
    global name $ resolveDatatype xs $ \rest -> k $ (name, expr):rest

resolveFun
    :: (MonadError String m, MonadReader Symtable m)
    => [([AST.Pattern], AST.Expr)]
    -> m [([Syn.Pattern], Syn.Term)]
resolveFun = mapM (uncurry resolveClause)

resolveClause
    :: (MonadError String m, MonadReader Symtable m)
    => [AST.Pattern] -> AST.Expr -> m ([Syn.Pattern], Syn.Term)
resolveClause lhs rhs = do
        (lhs, tbl) <- liftEither $ resolveLHS lhs
        rhs <- local (modify tbl) $ resolveExpr rhs
        pure (lhs, rhs)
    where
        modify mvs symtable =
            let mvs' = fmap PatV mvs in
            symtable
                { vars = union mvs' $ vars symtable }

resolveLHS
    :: [AST.Pattern]
    -> Either String ([Syn.Pattern], Map String MatchVar)
resolveLHS pats =
    runExcept
        (runReaderT (resolvePatterns pats $ \pats -> do
            (_, tbl) <- ask
            pure (pats, tbl)) (Syn.MV 0, empty))

resolveExpr
    :: (MonadError String m, MonadReader Symtable m)
    => AST.Expr -> m Syn.Term
resolveExpr (AST.App t u) = do
    t <- resolveExpr t
    u <- resolveExpr u
    pure $ Syn.App t u
resolveExpr AST.Hole = undefined
resolveExpr (AST.Lam x t) = do
    t <- intro x $ resolveExpr t
    pure $ Syn.Lam Nothing t
resolveExpr (AST.Pi x t u) = do
    t <- resolveExpr t
    u <- intro x $ resolveExpr u
    pure $ Syn.Pi t u
resolveExpr (AST.Sigma x t u) = do
    t <- resolveExpr t
    u <- intro x $ resolveExpr u
    pure $ Syn.Sigma t u
resolveExpr (AST.Pair t u) =
    Syn.Pair <$> resolveExpr t <*> resolveExpr u
resolveExpr AST.Triv = pure Syn.Triv
resolveExpr AST.Unit = pure Syn.Unit
resolveExpr AST.Univ = pure Syn.Universe
resolveExpr (AST.Var name) = do
    symtable <- ask
    case vars symtable !? name of
        Just (Local v) -> pure $ Syn.Var v
        Just (Global v) -> pure $ Syn.Def v
        Just (PatV v) -> pure $ Syn.MatchVar v
        Nothing -> throwError $ "Unbound variable " ++ name

resolvePattern
    :: (MonadError String m, MonadReader (MatchVar, Map String MatchVar) m)
    => AST.Pattern -> (Syn.Pattern -> m a) -> m a
resolvePattern AST.WildPat k = k Syn.WildPat
resolvePattern (AST.VarPat name) k = do
    (mv, tbl) <- ask
    case tbl !? name of
        Nothing ->
            local (\(mv, tbl) ->
                (Syn.nextMV mv, insert name mv tbl))
                $ k $ Syn.VarPat mv
        Just _ -> throwError $ "Redefined: " ++ name
resolvePattern (AST.ConPat name pats) k =
    resolvePatterns pats (k . Syn.ConPat name)

resolvePatterns
    :: (MonadError String m, MonadReader (MatchVar, Map String MatchVar) m)
    => [AST.Pattern] -> ([Syn.Pattern] -> m a) -> m a
resolvePatterns pats k =
    -- Accumulator is a function because of CPS
    foldr (\pat k pats ->
        resolvePattern pat $ \pat -> k $ pat:pats)
        (k . reverse) pats []
