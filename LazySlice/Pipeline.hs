{-# LANGUAGE ApplicativeDo, FlexibleContexts #-}
module LazySlice.Pipeline where

import LazySlice.Sexp as Sexp
import LazySlice.Syntax
import Text.Parsec

check prog = case parse Sexp.program "myfile" prog of
    Left e -> Left $ show e
    Right sexps -> mapM elabDecl sexps
