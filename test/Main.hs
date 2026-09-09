module Main (main) where

import Hom.Examples (symbolicExamplesOk)
import System.Exit (exitFailure)

main :: IO ()
main = do
  putStrLn "symbolicExamplesOk..."
  if symbolicExamplesOk
    then putStrLn "All OK."
    else do
      putStrLn "symbolicExamplesOk failed"
      exitFailure
