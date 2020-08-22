module Main where

import LazySlice.Pipeline
import qualified Data.Text.Lazy.IO as T.IO

main :: IO ()
main = do
    putStrLn "Starting..."
    prog <- T.IO.readFile "examples/test.ls"
    putStrLn "Read."
    case check prog of
        Left e -> do
            putStrLn "Error"
            print e
        Right sexp -> do
            putStrLn "Okay"
            print sexp
    putStrLn "Done."
