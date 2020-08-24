{-# LANGUAGE ApplicativeDo, FlexibleContexts #-}
module LazySlice.Sexp where

import LazySlice.AST
import Text.Parsec

data Sexp
    = Atom String
    | List [Sexp]

wordChar :: Stream s m Char => ParsecT s u m Char
wordChar = alphaNum <|> oneOf "-:!?"

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

elabAbs f [sexp] = elabExpr sexp
elabAbs f (List [Atom name, ty]:rest) =
    f name <$> elabExpr ty <*> elabAbs f rest
elabAbs _ _ = Left "?"

elabModule :: [Sexp] -> Either String Module
elabModule sexps = Module <$> mapM elabDecl sexps

elabDecl :: Sexp -> Either String Decl
elabDecl (List [Atom "define", Atom name, sexp]) = do
    expr <- elabExpr sexp
    pure $ Define name expr
elabDecl (List [Atom ":", Atom name, sexp]) = do
    expr <- elabExpr sexp
    pure $ Declare name expr
elabDecl _ = Left "Unknown declaration form."

elabExpr :: Sexp -> Either String Expr
elabExpr (Atom "type") = pure Univ
elabExpr (Atom name) = pure $ Var name
elabExpr (List (Atom "apply":f:args)) = do
    f <- elabExpr f
    args <- mapM elabExpr args
    pure $ foldl App f args
elabExpr (List (Atom "exists":rest)) = elabAbs Sigma rest
elabExpr (List (Atom "forall":rest)) = elabAbs Pi rest
elabExpr (List (f:args)) = do
    f <- elabExpr f
    args <- mapM elabExpr args
    pure $ foldl App f args
elabExpr _ = Left "Unknown expression form."
