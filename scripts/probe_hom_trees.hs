{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

import Experiments.Symbolic.Core
import Experiments.SymbolicExamples

main :: IO ()
main = do
  putStrLn $ "composeHomTreesSelfTest = " ++ show composeHomTreesSelfTest
  putStrLn $ "checkComposeHomTrees222 = " ++ show checkComposeHomTrees222
  putStrLn $ "checkHomFusedCategory222 = " ++ show checkHomFusedCategory222
  putStrLn $ "checkComposeHomTrees111 = " ++ show checkComposeHomTrees111
  putStrLn $ "checkComposeHomTrees000 = " ++ show checkComposeHomTrees000
