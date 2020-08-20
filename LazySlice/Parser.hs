module LazySlice.Parser where

data Expr
    = App Expr Expr -- expr expr
    | Expo Expr Expr -- expr -> expr
    | Pi String Expr Expr -- Π(id : expr), expr
    | Prod -- expr * expr
    | Sigma String Expr Expr -- Σ(id : expr), expr
    | Var String -- id
