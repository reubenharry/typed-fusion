{-# LANGUAGE DataKinds #-}
import Test.QuickCheck (quickCheckWith, stdArgs, maxSuccess)
import TensorNetwork.DMRG.Fixed
  ( prop_gMatIsIdentity
  , prop_nMatIsIdentityAtGaugedCentre
  , prop_nMatIsIdentityAfterSolveAndMove
  )

devArgs = stdArgs { maxSuccess = 10 }

main :: IO ()
main = do
  mapM_ (\(n,p) -> quickCheckWith devArgs p >>= print . (n,)) $
    [ ("gMat", prop_gMatIsIdentity)
    , ("nMat gauged", prop_nMatIsIdentityAtGaugedCentre)
    , ("nMat solve+move", prop_nMatIsIdentityAfterSolveAndMove)
    ]
