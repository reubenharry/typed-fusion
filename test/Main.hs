module Main (main) where

import Examples.Symbolic (fusedHalfHalfActionMovesProp, symbolicExamplesOk)
import System.Exit (exitFailure)
import Test.QuickCheck (quickCheckResult, isSuccess)

main :: IO ()
main = do
  putStrLn "symbolicExamplesOk..."
  if symbolicExamplesOk
    then putStrLn "All OK."
    else do
      putStrLn "symbolicExamplesOk failed"
      exitFailure
  putStrLn "fusedHalfHalfActionMovesProp..."
  r <- quickCheckResult fusedHalfHalfActionMovesProp
  if isSuccess r
    then putStrLn "All OK."
    else do
      putStrLn "fusedHalfHalfActionMovesProp failed"
      exitFailure
