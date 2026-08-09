{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}

-- | Where does one transferBulkSite spend time? Fresh densify each op.
--   cabal run mps-inner-micro
import Prelude hiding ((.), id, ($))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.), id)
import Control.Arrow.Constrained (($))
import Control.Exception (evaluate)
import Control.Lens ((^.))
import Data.Foldable (toList)
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Math.LinearMap.Category (getLinearMap, type (+>), type (⊗))
import Numeric.LinearAlgebra.Static (C)
import Text.Printf (printf)

import TensorNetwork.Categorical ((⊗^), swapMap)
import TensorNetwork.DMRG.Fixed (productMPS)
import TensorNetwork.MPS.General
  ( FullNorm, hermitianNorm, mpsBulk, mpsLeft, siteDagger
  , transferBulkSite, transferLeftSite
  )

timeMs :: String -> Int -> IO () -> IO ()
timeMs label nRep act = do
  act  -- warmup (builds + discards; next iters still rebuild)
  t0 <- getCurrentTime
  let go 0 = pure ()
      go k = act >> go (k - 1)
  go nRep
  t1 <- getCurrentTime
  let ms = 1000 * realToFrac (diffUTCTime t1 t0) :: Double
  printf "%-56s %8.3f ms total  %8.2f µs/op\n"
    label ms (1000 * ms / fromIntegral nRep)

main :: IO ()
main = do
  let nb = hermitianNorm :: FullNorm (C 3)
      np = hermitianNorm :: FullNorm (C 2)
      psi = productMPS @1
      l = psi ^. mpsLeft
      b0 = case toList (psi ^. mpsBulk) of
        (b : _) -> b
        [] -> error "empty bulk"
      env0 = transferLeftSite nb np l l
      !_ = getLinearMap env0
      n = 100
  printf "Fresh rebuild+densify each op (χ=3,p=2); nRep=%d\n\n" n

  timeMs "A  siteDagger" n $ do
    evaluate (getLinearMap (siteDagger nb np nb b0)) >> pure ()

  timeMs "B  env ⊗^ id_phys" n $ do
    let t = (env0 ⊗^ (id :: C 2 +> C 2)) :: (C 3 ⊗ C 2) +> (C 3 ⊗ C 2)
    evaluate (getLinearMap t) >> pure ()

  timeMs "C  swapMap densify (C3⊗C2 → C2⊗C3)" n $ do
    evaluate (getLinearMap (swapMap :: (C 3 ⊗ C 2) +> (C 2 ⊗ C 3))) >> pure ()

  timeMs "D  id_bond ⊗^ id_phys  (pure tensorOfMaps)" n $ do
    let t = ((id :: C 3 +> C 3) ⊗^ (id :: C 2 +> C 2))
          :: (C 3 ⊗ C 2) +> (C 3 ⊗ C 2)
    evaluate (getLinearMap t) >> pure ()

  timeMs "E  ket . siteDagger     (no ⊗^)" n $ do
    let d = siteDagger nb np nb b0
    evaluate (getLinearMap (b0 . d)) >> pure ()

  timeMs "F  ket . (env⊗^id) . dag" n $ do
    let d = siteDagger nb np nb b0
        t = (env0 ⊗^ (id :: C 2 +> C 2)) :: (C 3 ⊗ C 2) +> (C 3 ⊗ C 2)
    evaluate (getLinearMap (b0 . t . d)) >> pure ()

  timeMs "G  transferBulkSite" n $ do
    evaluate (getLinearMap (transferBulkSite nb np b0 b0 env0)) >> pure ()

  -- Does getLinearMap memoize? Second force of SAME thunk should be free.
  let step = transferBulkSite nb np b0 b0 env0
      !_ = getLinearMap step
  timeMs "H  re-force SAME transferBulkSite thunk" n $ do
    evaluate (getLinearMap step) >> pure ()

  printf "\n"
  printf "tensorOfMaps = fmap g ∘ transpose ∘ fmap f ∘ transpose\n"
  printf "fmapTensor Static = per-column toArray (matmul path commented out)\n"
