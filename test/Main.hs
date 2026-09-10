module Main (main) where

import Examples.Symbolic (symbolicExamplesOk)
import System.Exit (exitFailure)

main :: IO ()
main = do
  putStrLn "symbolicExamplesOk..."
  if symbolicExamplesOk
    then putStrLn "All OK."
    else do
      putStrLn "symbolicExamplesOk failed"
      exitFailure
