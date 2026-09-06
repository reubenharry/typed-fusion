{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

import Experiments.Symbolic.Core
import Experiments.SymbolicExamples

main :: IO ()
main = do
  putStrLn $ "composeMorTreesSelfTest = " ++ show composeMorTreesSelfTest
  putStrLn $ "checkComposeMorTrees222 = " ++ show checkComposeMorTrees222
  putStrLn $ "checkHomFusedCategory222 = " ++ show checkHomFusedCategory222
  putStrLn $ "checkComposeMorTrees111 = " ++ show checkComposeMorTrees111
  putStrLn $ "checkComposeMorTrees000 = " ++ show checkComposeMorTrees000
