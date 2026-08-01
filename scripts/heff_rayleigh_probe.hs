{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Prelude
import Control.Lens ((^.), _1)
import Data.Complex (realPart)
import Data.VectorSpace (InnerSpace ((<.>)))

import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General

main :: IO ()
main = do
  let psiG = mixedCanonicalCentre3 $ unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      nb = hermitianNorm
      np = hermitianNorm
      c = psiG ^. mpsBulk . _1
  putStrLn ("mpsInner     = " ++ show (mpsInner nb np psiG psiG))
  putStrLn ("centre <.> c = " ++ show (c <.> c))
  putStrLn ("real ratio   = " ++ show (realPart (mpsInner nb np psiG psiG / (c <.> c))))
