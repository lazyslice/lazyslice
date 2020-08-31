{-# LANGUAGE ApplicativeDo, FlexibleContexts #-}
module LazySlice.Sexp where

import LazySlice.AST
import Control.Monad (join)
import Data.List (intersperse)
import Text.Parsec

data Sexp
    = Atom String
    | List [Sexp]

wordChar :: Stream s m Char => ParsecT s u m Char
wordChar = alphaNum <|> oneOf "-:!?_"

word :: Stream s m Char => ParsecT s u m String
word = do
    c <- wordChar
    str <- many wordChar
    pure $ c:str

list :: Stream s m Char => ParsecT s u m [Sexp]
list = do
    char '('
    spaces
    sexps <- many (sexp <* spaces)
    char ')'
    pure sexps

sexp :: Stream s m Char => ParsecT s u m Sexp
sexp = try (Atom <$> word)
    <|> try (List <$> list)

program :: Stream s m Char => ParsecT s u m [Sexp]
program = do
    spaces
    decls <- many (sexp <* spaces)
    pure decls

elabModule :: [Sexp] -> Either String Module
elabModule sexps = Module <$> mapM elabDecl sexps

elabDecl :: Sexp -> Either String Decl
elabDecl (List (Atom "data":Atom name:datacons)) = do
    datacons <- elabData datacons
    pure $ Data name datacons
elabDecl (List [Atom "define", Atom name, sexp]) = do
    expr <- elabExpr sexp
    pure $ Define name expr
elabDecl (List (Atom "defun":Atom name:clauses)) = do
    clauses <- elabClauses clauses
    pure $ Defun name clauses
elabDecl (List [Atom ":", Atom name, sexp]) = do
    expr <- elabExpr sexp
    pure $ Declare name expr
elabDecl _ = Left "Unknown declaration form."

elabData :: [Sexp] -> Either String [(String, Expr)]
elabData [] = Right []
elabData (List [Atom ":", Atom name, sexp]:datacons) = do
    expr <- elabExpr sexp
    rest <- elabData datacons
    pure $ (name, expr):rest
elabData (_:_) = Left "?"

elabClauses :: [Sexp] -> Either String [([Pattern], Expr)]
elabClauses [] = pure []
elabClauses (List [List pats, expr]:clauses) = do
    pats <- mapM elabPat pats
    expr <- elabExpr expr
    next <- elabClauses clauses
    pure $ (pats, expr):next

elabAbs f [sexp] = elabExpr sexp
elabAbs f (List [Atom name, ty]:rest) =
    f name <$> elabExpr ty <*> elabAbs f rest
elabAbs _ _ = Left "?"

elabLambda :: [Sexp] -> Sexp -> Either String Expr
elabLambda [] body = elabExpr body
elabLambda (Atom param:xs) body = Lam param <$> elabLambda xs body

elabTuple :: [Sexp] -> Either String Expr
elabTuple [] =
    Left "Cannot have empty tuple. (Maybe you meant to use trivial?)"
elabTuple [x] = elabExpr x
elabTuple (x:xs) = Pair <$> elabExpr x <*> elabTuple xs

elabExpr :: Sexp -> Either String Expr
elabExpr (Atom "type") = pure Univ
elabExpr (Atom "unit") = pure Unit
elabExpr (Atom "trivial") = pure Triv
elabExpr (Atom name) = pure $ Var name
elabExpr (List (Atom "apply":f:args)) = do
    f <- elabExpr f
    args <- mapM elabExpr args
    pure $ foldl App f args
elabExpr (List (Atom "exists":rest)) = elabAbs Sigma rest
elabExpr (List (Atom "forall":rest)) = elabAbs Pi rest
elabExpr (List [Atom "lambda", List params, body]) =
    elabLambda params body
elabExpr (List (Atom "tuple":rest)) = elabTuple rest
elabExpr (List (f:args)) = do
    f <- elabExpr f
    args <- mapM elabExpr args
    pure $ foldl App f args
elabExpr _ = Left "Unknown expression form."

elabPat :: Sexp -> Either String Pattern
elabPat (Atom "_") = pure $ WildPat
elabPat (Atom v) = pure $ VarPat v
elabPat (List (Atom name:pats)) = do
    pats <- mapM elabPat pats
    pure $ ConPat name pats

quoteExpr :: Expr -> Sexp
quoteExpr Univ = Atom "type"
quoteExpr Unit = Atom "unit"
quoteExpr Triv = Atom "trivial"
quoteExpr (Var v) = Atom v
quoteExpr (App f x) =
        let (hd, spine) = go [x] f in
        List $ Atom "apply" : quoteExpr f : fmap quoteExpr spine
    where
        go acc (App f x) = go (x:acc) f
        go acc expr = (expr, acc)
quoteExpr (Sigma name a b) =
        let (binders, end) = go b in
        List $
            Atom "exists"
                : (fmap quoteBinder ((name, a) : binders)
                    ++ [quoteExpr end])
    where
        go (Sigma name a b) =
            let (binders, end) = go b in
            ((name, a) : binders, end)
        go expr = ([], expr)
quoteExpr (Pi name a b) =
        let (binders, end) = go b in
        List $
            Atom "forall"
                : (fmap quoteBinder ((name, a) : binders)
                    ++ [quoteExpr end])
    where
        go (Pi name a b) =
            let (binders, end) = go b in
            ((name, a) : binders, end)
        go expr = ([], expr)
quoteExpr (Lam param body) =
        let (params, body) = go body in
        List
            [ Atom "lambda"
            , List $ Atom param : params
            , quoteExpr body ]
    where
        go (Lam param body) =
            let (params, body) = go body in
            (Atom param : params, body)
        go expr = ([], expr)
quoteExpr (Pair a b) =
        let ls = quoteExpr a : go b in
        List $ Atom "tuple" : ls
    where
        go (Pair a b) =
            let ls = go b in
            quoteExpr a : ls
        go expr = [quoteExpr expr]

quoteBinder :: (String, Expr) -> Sexp
quoteBinder (name, expr) = List [Atom name, quoteExpr expr]

quoteSexp :: Sexp -> String
quoteSexp (Atom s) = s
quoteSexp (List sexps) =
    "(" ++ join (intersperse " " (fmap quoteSexp sexps)) ++ ")"