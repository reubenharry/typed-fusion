{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
import Prelude hiding (id, ($))
import Control.Category.Constrained (id)
import Control.Arrow.Constrained (($))
import TensorNetwork.Categorical ((⊗^), swapMap)
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗), FiniteDimensional (..), SubBasis
  , LinearMap (..), decomposeLinMap )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, M, Sized (fromList), extract)
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray, Dimension)
import qualified Numeric.LinearAlgebra.HMatrix as HM
import GHC.TypeLits (KnownNat, natVal)
import Data.Proxy (Proxy (..))
import Data.Complex (Complex ((:+)))
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Vector.Storable as VS

type ℂ = Complex Double

one1 :: C 1
one1 = fromList [1]

basisAt :: forall n. KnownNat n => Int -> C n
basisAt i =
  fromList [ if j == i then 1 else 0 | j <- [0 .. fromIntegral (natVal (Proxy @n)) - 1] ]

main :: IO ()
main = do
  putStrLn "=== atomic C2,C3 ==="
  let f = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) [basisAt @3 0, basisAt @3 1])
        :: C 2 +> C 3
      g = id :: C 3 +> C 3
      x = basisAt @2 0
      y = basisAt @3 0
      lhs = (f ⊗^ g) $ (x ⊗ y) :: C 3 ⊗ C 3
      rhs = (f $ x) ⊗ (g $ y) :: C 3 ⊗ C 3
  putStrLn $ "tensorOfMaps lhs == rhs: " ++ show (lhs == rhs)

  let x2 = fromList [2 :+ (-1), 1 :+ 1] :: C 2
      y2 = fromList [0 :+ (-1), 0 :+ 2, (-1) :+ (-2)] :: C 3
      lhsR = (f ⊗^ g) $ (x2 ⊗ y2) :: C 3 ⊗ C 3
      rhsR = (f $ x2) ⊗ (g $ y2) :: C 3 ⊗ C 3
  putStrLn $ "random vec lhs == rhs: " ++ show (lhsR == rhsR)
  putStrLn $ "swap lhs == rhs: " ++ show ((swapMap $ lhsR) == rhsR)
  putStrLn $ "random lhs arr: " ++ show (VS.toList (toArray lhsR :: VS.Vector ℂ))
  putStrLn $ "random rhs arr: " ++ show (VS.toList (toArray rhsR :: VS.Vector ℂ))

  let mf = extract (getLM f)
      mg = extract (getLM g)
      inp = HM.fromList $ VS.toList (toArray (x2 ⊗ y2) :: VS.Vector ℂ)
      out = HM.fromList $ VS.toList (toArray rhsR :: VS.Vector ℂ)
      af = HM.tr' mf
      ag = HM.tr' mg
  putStrLn $ "kron arr random: " ++ show (applyKron f g (x2 ⊗ y2) == rhsR)
  putStrLn $ "kron arr basis: " ++ show (applyKron f g (x ⊗ y) == rhs)

  putStrLn "\n=== site C1⊗C2 ==="
  let sf = fst (recomposeLinMap (entireBasis :: SubBasis (C 1 ⊗ C 2))
        [ basisAt @2 0, basisAt @2 1, basisAt @2 0, basisAt @2 1 ])
        :: (C 1 ⊗ C 2) +> C 2
      sid = id :: C 2 +> C 2
      sx = one1 ⊗ basisAt @2 0
      sy = basisAt @2 0
      lhs2 = (sf ⊗^ sid) $ (sx ⊗ sy)
      rhs2 = (sf $ sx) ⊗ sy
  putStrLn $ "tensorOfMaps lhs == rhs: " ++ show (lhs2 == rhs2)

  putStrLn $ "site kron arr basis: " ++ show (applyKron sf sid (sx ⊗ sy) == rhs2)

  let mfS = extract (getLM sf)
      mgS = extract (getLM sid)
      inpS = HM.fromList $ VS.toList (toArray (sx ⊗ sy) :: VS.Vector ℂ)
      outS = HM.fromList $ VS.toList (toArray rhs2 :: VS.Vector ℂ)
      afS = HM.tr' mfS
      agS = HM.tr' mgS
  putStrLn $ "site mf dims: " ++ show (HM.size mfS)
  mapM_ (\(name, op) -> putStrLn $ name ++ ": " ++ show (HM.norm_2 (op HM.#> inpS - outS) < 1e-10)) $
    [ ("kron(agS,afS)", HM.kronecker agS afS)
    , ("kron(afS,agS)", HM.kronecker afS agS)
    ]

getLM :: forall a b. (KnownNat (Dimension a), KnownNat (Dimension b))
      => (a +> b) -> M (Dimension b) (Dimension a)
getLM (LinearMap m) = unsafeCoerce m

applyKron :: forall u v u' v'. (u +> v) -> (u' +> v') -> (u ⊗ u') -> (v ⊗ v')
applyKron f g x =
  unsafeFromArray @(v ⊗ v') $
    HM.kronecker (operator g) (operator f) HM.#> toArray x
  where
    operator h = HM.tr' (extract (getLM h))
