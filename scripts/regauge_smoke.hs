{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
module Main where

import Prelude hiding (id)
import qualified Control.Category.Constrained as Cat
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import TensorNetwork.MPS.Fixed3 (genMPS222, mpsToFlat)
import TensorNetwork.MPS.Fixed3.Internal (Site (..), withMPS3, mps3, siteLin)
import TensorNetwork.DMRG.Fixed3
  ( normalizeLeft, regaugeDepartRight, rightGaugeMPS )
import TensorNetwork.Categorical ((⊗^))
import TensorNetwork.Dagger (transposeMap)
import Numeric.LinearAlgebra.Static (C, unwrap)
import qualified Data.Vector.Storable as VSt
import Data.Complex (magnitude)

maxDiff :: C n -> C n -> Double
maxDiff a b =
  VSt.maximum (VSt.map magnitude (VSt.zipWith (-) (unwrap a) (unwrap b)))

main :: IO ()
main = do
  let psi = unGen genMPS222 (mkQCGen 0) 30
  let flat0 = mpsToFlat psi
  let (_, psi1a) = regaugeDepartRight 1 psi
  print ("diff regaugeDepartRight: " ++ show (maxDiff flat0 (mpsToFlat psi1a)))
  print ("diff rightGaugeMPS: " ++ show (maxDiff flat0 (mpsToFlat (rightGaugeMPS psi))))

  withMPS3 psi $ \s1 s2 s3 -> do
    let (s1c, bond) = normalizeLeft s1
        s2post = Site (siteLin s2 . (bond ⊗^ (Cat.id :: C 2 +> C 2)))
        s2pre = Site ((bond ⊗^ (Cat.id :: C 2 +> C 2)) . siteLin s2)
        s2out = Site (bond . siteLin s2)
        s2dag = Site (siteLin s2 . (transposeMap bond ⊗^ (Cat.id :: C 2 +> C 2)))
    print ("diff g . F⊗id: " ++ show (maxDiff flat0 (mpsToFlat (mps3 s1c s2post s3))))
    print ("diff F⊗id . g: " ++ show (maxDiff flat0 (mpsToFlat (mps3 s1c s2pre s3))))
    print ("diff F . g (output): " ++ show (maxDiff flat0 (mpsToFlat (mps3 s1c s2out s3))))
    print ("diff g . F^T⊗id: " ++ show (maxDiff flat0 (mpsToFlat (mps3 s1c s2dag s3))))
