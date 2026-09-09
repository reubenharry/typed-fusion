{-# LANGUAGE DataKinds #-}
module Main where
import Hom.Examples

main :: IO ()
main = mapM_ (\(n,b) -> putStrLn (n ++ ": " ++ show b))
  [ ("undualDualRoundtripOk", undualDualRoundtripOk)
  , ("symbolicExamplesOk", symbolicExamplesOk)
  , ("composeHomTreesSelfTest", composeHomTreesSelfTest)
  , ("fmoveTreesSelfTest", fmoveTreesSelfTest)
  , ("fuseMapRightFinvSelfTest", fuseMapRightFinvSelfTest)
  ]
