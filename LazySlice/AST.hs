module LazySlice.AST where

data Expr
    = App Expr Expr
    | Hole
    | Lam String Expr
    | Pair Expr Expr
    | Pi String Expr Expr
    | Sigma String Expr Expr
    | Triv
    | Unit
    | Univ
    | Var String
    deriving Show

data Pattern
    = ConPat String [Pattern]
    | VarPat String
    deriving Show

data Decl
    = Data String [(String, Expr)]
    | Declare String Expr
    | Define String Expr
    | Defun String [([Pattern], Expr)]
    deriving Show

data Module = Module [Decl]
