{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}

-- | Typecheck / smoke: 'lanczosQDag' / 'solveAtPrefix' on TFIM bulk Heff
-- (χ=3, p=2, q=1). Proves map-space centres work without @DualVector v ~ v@.
--
--   cabal run lanczos-heff-smoke
import Prelude hiding (($))
import Control.Arrow.Constrained (EnhancedCat (arr))
import Control.Lens ((^.), _1)
import qualified Data.List.NonEmpty as NE
import Math.LinearMap.Category (type (+>), type (-+>))
import Numeric.LinearAlgebra.Static (C)
import System.Exit (exitSuccess)

import GroundState (hilbertSchmidtFullNorm)
import Lanczos
  ( defaultLanczosTolerance
  , lanczosEmbed
  , lanczosLowestQ
  , lanczosQ
  , lanczosQDag
  , lanczosTridiag
  , normFromFull
  , solveAtPrefix
  )
import TensorNetwork.DMRG.Fixed (heffBulk, productMPS, tfimMPO)
import TensorNetwork.MPS.General
  ( BulkSite, hermitianNorm, mixedCanonicalCentre3, mpsBulk )

type Centre = BulkSite (C 3) (C 2)

main :: IO ()
main = do
  let nb = hermitianNorm
      np = hermitianNorm
      mpo = tfimMPO @1 1 0.7
      psi = mixedCanonicalCentre3 (productMPS @1)
      heff = heffBulk nb np 0 psi mpo :: Centre +> Centre
      f = arr heff :: Centre -+> Centre
      nv = hilbertSchmidtFullNorm @Centre
      seed = psi ^. mpsBulk . _1
      steps = take 2 (lanczosTridiag (normFromFull nv) f seed)
  case NE.nonEmpty steps of
    Nothing -> putStrLn "FAIL: empty Krylov"
    Just ne -> do
      let qs = fmap lanczosQ ne
          _q = lanczosEmbed @2 qs :: C 2 +> Centre
          _qDag = lanczosQDag @2 nv qs :: Centre +> C 2
          _spec = solveAtPrefix nv f ne
          (_θ, _v) = lanczosLowestQ nv f ne defaultLanczosTolerance
      putStrLn "OK: BulkSite Lanczos Q† / solveAtPrefix / lanczosLowestQ typecheck"
      exitSuccess
