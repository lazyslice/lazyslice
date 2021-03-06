{-# LANGUAGE ApplicativeDo, FlexibleContexts #-}
module LazySlice.Pipeline where

import LazySlice.Resolve
import LazySlice.Sexp as Sexp
import LazySlice.Syntax
import LazySlice.TypeCheck
import Text.Parsec

check prog = case parse Sexp.program "myfile" prog of
    Left e -> Left $ show e
    Right sexps ->
        case elabModule sexps of
            Left e -> Left e
            Right modl -> do
                modl <- resolve modl
                typecheck modl
                pure modl
