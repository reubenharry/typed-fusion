{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

import Test.QuickCheck (quickCheckResult)

import TensorNetwork.DMRG.Fixed
  ( prop_gMatIsIdentity
  , prop_nMatIsIdentityAtGaugedCentre
  , prop_nMatIsIdentityAfterSolveAndMove
  , prop_solveCenterAtLowersRayleigh
  , prop_sweepLowersRayleigh
  , prop_moveRightPreservesMPS
  , prop_moveLeftPreservesMPS
  , prop_zipperTourPreservesMPS
  , prop_moveRightLeftPreservesMPS
  )

main :: IO ()
main = do
  mapM_ run
    [ ("gMat≈I", prop_gMatIsIdentity)
    , ("nMat≈I gauged", prop_nMatIsIdentityAtGaugedCentre)
    , ("nMat≈I after solve+move", prop_nMatIsIdentityAfterSolveAndMove)
    , ("solve lowers Rayleigh", prop_solveCenterAtLowersRayleigh)
    , ("sweep lowers Rayleigh", prop_sweepLowersRayleigh)
    , ("moveRight preserves ψ", prop_moveRightPreservesMPS)
    , ("moveLeft preserves ψ", prop_moveLeftPreservesMPS)
    , ("zipper tour preserves ψ", prop_zipperTourPreservesMPS)
    , ("moveRight/Left round-trip", prop_moveRightLeftPreservesMPS)
    ]
  where
    run (name, prop) = do
      putStrLn $ "=== " ++ name ++ " ==="
      r <- quickCheckResult prop
      print r
      putStrLn ""
