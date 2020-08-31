module Main where

import LazySlice.Pipeline
import qualified Data.Text.Lazy.IO as T.IO
import System.Environment

main :: IO ()
main = do
    prog <- T.IO.readFile "examples/test.ls"
    case check prog of
        Left e -> do
            putStrLn "Error"
            putStrLn e
        Right sexp -> do
            putStrLn "Okay"
