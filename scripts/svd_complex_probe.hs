{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

import Prelude hiding (($), (.))
import Control.Arrow.Constrained (arr, ($))
import Data.Functor.Identity (runIdentity)
import Data.VectorSpace (InnerSpace ((<.>)), magnitudeSq, (*^), (^-^))
import Data.Complex (realPart)
import Linear (V3 (..))
import Math.LinearMap.Category (LinearFunction (..), type (-+>), type (+>))
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Asserted
import Math.VectorSpace.Initializable
import Numeric.LinearAlgebra.Static (C, Sized (fromList))
import Numeric.LinearAlgebra.Static.COrphans ()
import System.Random (mkStdGen)
import Experiments.SVD

main :: IO ()
main = do
  putStrLn "=== real ==="
  let aR = randomEndoV3 (mkStdGen 42)
      psR = runIdentity (svd (FixedInitialVectors [V3 1 0 0, V3 0 1 0, V3 0 0 1]) aR 3)
  putStrLn $ "X Gram: " ++ show (assessOrthonormality (domainSingularVector <$> psR))
  putStrLn $ "Y Gram: " ++ show (assessOrthonormality (codomainSingularVector <$> psR))

  putStrLn "=== complex ==="
  let aMap = randomEndoC @3 (mkStdGen 42)
      aFun = arr $ LinearFunction (aMap $) :: C 3 -+> C 3
      psC =
        runIdentity
          ( svdC
              ( FixedInitialVectors
                  [ fromList [1, 0, 0]
                  , fromList [0, 1, 0]
                  , fromList [0, 0, 1]
                  ]
              )
              aFun
              3
          )
  putStrLn $ "X Gram Re: " ++ show (assessOrthonormalityC (domainSingularVector <$> psC))
  putStrLn $ "Y Gram Re: " ++ show (assessOrthonormalityC (codomainSingularVector <$> psC))
  -- Check A x ≈ σ y
  putStrLn "A x - σ y norms:"
  mapM_
    ( \p ->
        let x = domainSingularVector p
            y = codomainSingularVector p
            s = singularValue p
            res = (aFun $ x) ^-^ (s *^ y)
         in print (sqrt (realPart (magnitudeSq res)))
    )
    psC
  testPendantsReconstructionC
