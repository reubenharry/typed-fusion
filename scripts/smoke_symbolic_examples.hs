{-# LANGUAGE DataKinds #-}
module Main where
import Examples.Symbolic

main :: IO ()
main = mapM_ (\(n,b) -> putStrLn (n ++ ": " ++ show b))
  [ ("undualDualRoundtripOk", undualDualRoundtripOk)
  , ("symbolicExamplesOk", symbolicExamplesOk)
  , ("homUnfusedU1IdIdOk", homUnfusedU1IdIdOk)
  , ("homUnfusedU1LeftUnitOk", homUnfusedU1LeftUnitOk)
  , ("composeHomTreesSelfTest", composeHomTreesSelfTest)
  , ("fmoveTreesSelfTest", fmoveTreesSelfTest)
  , ("fuseMapRightFinvSelfTest", fuseMapRightFinvSelfTest)
  ]
