{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}

import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Data.Complex (realPart)
import Data.List (sortOn)
import Data.Ord (Down (..))
import Data.VectorSpace
  ( magnitudeSq, (^-^), (*^), (^/), normalized
  )
import Math.LinearMap.Category
  ( FiniteDimensional (..), getLinearMap, type (-+>)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Asserted
import Numeric.LinearAlgebra.Static (C, Sized (extract))
import qualified Numeric.LinearAlgebra as HM
import Numeric.LinearAlgebra.Static.COrphans ()
import System.Random (mkStdGen)
import GHC.TypeLits (KnownNat)
import Experiments.SVD

reconErr
  :: forall n m k
   . (KnownNat n, KnownNat m, KnownNat k)
  => [SVDPendants (C n) (C m)]
  -> (C n -+> C m)
  -> Double
reconErr ps aFun
  | length ps < subbasisDimension (entireBasis :: SubBasis (C k)) = 1 / 0
  | otherwise =
      let rebuilt = reconstructFromPendants @(C k) ps
          es = enumerateSubBasis (entireBasis :: SubBasis (C n))
      in maximum
           [ sqrt (realPart (magnitudeSq ((aFun $ e) ^-^ (rebuilt $ e))))
           | e <- es
           ]

main :: IO ()
main = do
  let aMap = randomMapC @4 @2 (mkStdGen 45)
      aFun = asLinearFunction aMap
      seeds = enumerateSubBasis (entireBasis :: SubBasis (C 4))
      mat = extract (getLinearMap aMap)
      (_, sOracle, _) = HM.thinSVD mat
  putStrLn $ "oracle s = " ++ show sOracle

  let x0 = seeds !! 0
      y0 = aFun $ x0
      s0 = realSV (sqrt (realPart (magnitudeSq y0)))
      p0 = [SVDPendants (normalized x0) (y0 ^/ s0) s0]
      -- uncapped growth
      u1 = svdStepC (seeds !! 1) aFun p0
      u2 = svdStepC (seeds !! 2) aFun u1
      u3 = svdStepC (seeds !! 3) aFun u2
      -- capped at 2: grow then drop smallest
      cap2 ps v =
        let grown = svdStepC v aFun ps
         in take 2 $ sortOn (Down . realPart . singularValue) grown
      c1 = cap2 p0 (seeds !! 1)
      c2 = cap2 c1 (seeds !! 2)
      c3 = cap2 c2 (seeds !! 3)

  putStrLn "\n=== uncapped ==="
  mapM_
    ( \(lab, ps) -> do
        putStrLn $ lab ++ " sis=" ++ show (singularValue <$> ps)
        putStrLn $
          "  YGram=" ++ show (assessOrthonormalityC (codomainSingularVector <$> ps))
        when (length ps >= 2) $
          putStrLn $
            "  top2 err="
              ++ show
                ( reconErr @4 @2 @2
                    (take 2 $ sortOn (Down . realPart . singularValue) ps)
                    aFun
                )
    )
    [("p0", p0), ("u1", u1), ("u2", u2), ("u3", u3)]

  putStrLn "\n=== capped at 2 ==="
  mapM_
    ( \(lab, ps) -> do
        putStrLn $ lab ++ " sis=" ++ show (singularValue <$> ps)
        putStrLn $
          "  YGram=" ++ show (assessOrthonormalityC (codomainSingularVector <$> ps))
        putStrLn $ "  recon err=" ++ show (reconErr @4 @2 @2 ps aFun)
        putStrLn $ "  XGram=" ++ show (assessOrthonormalityC (domainSingularVector <$> ps))
    )
    [("c1", c1), ("c2", c2), ("c3", c3)]
  where
    when b m = if b then m else pure ()
