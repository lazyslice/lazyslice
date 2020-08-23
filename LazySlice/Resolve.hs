{-# LANGUAGE FlexibleContexts #-}
module LazySlice.Resolve where

import LazySlice.AST as AST
import LazySlice.Syntax as Syn
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader, ask, local)
import Control.Monad.Trans.Reader (runReaderT)
import Control.Monad.Trans.Except (runExcept)
import Data.Map (Map, (!?), empty, insert, traverseWithKey)

data Name = Local Int | Global String

data Symtable = Symtable
    { vars :: Map String Name }

resolve :: AST.Module -> Either String Syn.Module
resolve modl = runExcept (runReaderT (resolveModule modl) $ Symtable empty)

intro :: MonadReader Symtable m => String -> m Syn.Term -> m Syn.Term
intro name = local $ \symtable ->
        let vs = vars symtable in
        Symtable
            { vars = insert name (Local 0) $ fmap up vs }
    where
        up (Local v) = Local $ v + 1
        up other = other

resolveModule :: (MonadError String m, MonadReader Symtable m) => AST.Module -> m Syn.Module
resolveModule (AST.Module decls) = do
        defs <- go empty decls
        pure $ Syn.Module defs
    where
        go :: (MonadError String m, MonadReader Symtable m)
           => Map String (Syn.Term, Maybe Syn.Term)
           -> [AST.Decl]
           -> m (Map String (Syn.Term, Syn.Term))
        go defs [] = do
            traverseWithKey (\name (ty, def) ->
                case def of
                    Just def -> pure (ty, def)
                    Nothing -> throwError $ "No definition for " ++ name)
                defs
        go defs (AST.Decl name ty:decls) = do
            ty <- resolveExpr ty
            go (insert name (ty, Nothing) defs) decls
        go defs (AST.Define name expr:decls) =
            case defs !? name of
                Just (ty, Nothing) -> do
                    expr <- resolveExpr expr
                    go (insert name (ty, Just expr) defs) decls
                Just (_, Just _) ->
                    throwError $ "Multiple definitions for " ++ name
                Nothing -> throwError $ "No type declaration for " ++ name

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
resolveExpr AST.Univ = pure Syn.Universe
resolveExpr (AST.Var name) = do
    symtable <- ask
    case vars symtable !? name of
        Just (Local v) -> pure $ Syn.Var v
        Just (Global _) -> throwError "Unimplemented"
        Nothing -> throwError $ "Unbound variable " ++ name
