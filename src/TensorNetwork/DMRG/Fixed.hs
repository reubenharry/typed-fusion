{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE ConstraintKinds #-}

-- | Single-site DMRG on "TensorNetwork.MPS.General".
--
-- Local effective Hamiltonians are morphism applies
-- ('effectiveHLeft' / 'effectiveHBulk' / 'effectiveHRight'); densification
-- happens only inside 'GroundState.groundState' (ROADMAP D3).
--
-- Gauge transport is not yet wired; 'sweep' solves every site in place.
module TensorNetwork.DMRG.Fixed
  ( energy
  , heffLeft
  , heffBulk
  , heffRight
  , solveLeft
  , solveBulk
  , solveRight
  , solveAllSites
  , sweep
  , dmrg
  , DmrgResult (..)
  , tfimMPO
  , productMPS
  ) where

import Prelude hiding (id, ($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained (id, (.))
import Control.Arrow.Constrained (($), arr)
import Math.LinearMap.Category
  ( type (+>), type (⊗), type (-+>), (⊗)
  , LinearFunction (..), pattern LinearFunction
  , LinearMap (..), FiniteDimensional, VectorSpace ((*^))
  , AdditiveGroup (zeroV)
  )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList, konst))
import Data.Complex (Complex ((:+)), realPart)
import Data.VectorSpace (InnerSpace, sumV)
import qualified Data.Vector as Vector
import Linear.V (V (..))
import GHC.TypeLits (KnownNat, Nat, type (*))
import Data.Proxy (Proxy (..))
import GHC.TypeNats (natVal)

import GroundState (groundState)
import TensorNetwork.Categorical ((⊗^))
import TensorNetwork.MPS.LinmapStorage (linMapFromColumnImages, siteLinFromRows)
import TensorNetwork.MPS.General
  ( FullNorm (..), MPS (..), MPO (..), EndoMPO
  , LeftSite, BulkSite, RightSite
  , MPSConstraints, hermitianNorm
  , mpsInner, mpsMPOInner
  , effectiveHLeft, effectiveHBulk, effectiveHRight
  )
import TensorNetwork.DMRG.Chain
  ( bulkCount, getBulk, setBulk, setLeft, setRight )
import TensorNetwork.DMRG.Env
  ( leftEnvBeforeBulk, leftEnvBeforeRight
  , rightEnvAfterBulk, rightEnvAfterLeft
  )

--------------------------------------------------------------------------------
-- Energy
--------------------------------------------------------------------------------

energy
  :: forall bond phys (q :: Nat).
  MPSConstraints bond phys =>
  FullNorm bond -> FullNorm phys ->
  EndoMPO bond phys q -> MPS bond phys q -> Double
energy nb np mpo psi =
  realPart (mpsMPOInner nb np psi mpo psi / mpsInner nb np psi psi)

--------------------------------------------------------------------------------
-- Effective Hamiltonian endomorphisms
--------------------------------------------------------------------------------

heffLeft
  :: forall bond phys (q :: Nat).
  (MPSConstraints bond phys, KnownNat q) =>
  FullNorm bond -> FullNorm phys ->
  MPS bond phys q -> EndoMPO bond phys q ->
  LeftSite bond phys +> LeftSite bond phys
heffLeft nb np mps mpo =
  let r = rightEnvAfterLeft nb np mps mpo
  in arr (LinearFunction (effectiveHLeft (mpoLeft mpo) r))

heffBulk
  :: forall bond phys (q :: Nat).
  (MPSConstraints bond phys, KnownNat q) =>
  FullNorm bond -> FullNorm phys ->
  Int -> MPS bond phys q -> EndoMPO bond phys q ->
  BulkSite bond phys +> BulkSite bond phys
heffBulk nb np j mps mpo =
  let l = leftEnvBeforeBulk nb np j mps mpo
      r = rightEnvAfterBulk nb np j mps mpo
      op = getBulk @q j (mpoBulk mpo)
  in arr (LinearFunction (effectiveHBulk l op r))

heffRight
  :: forall bond phys (q :: Nat).
  (MPSConstraints bond phys, KnownNat q) =>
  FullNorm bond -> FullNorm phys ->
  MPS bond phys q -> EndoMPO bond phys q ->
  RightSite bond phys +> RightSite bond phys
heffRight nb np mps mpo =
  let l = leftEnvBeforeRight nb np mps mpo
  in arr (LinearFunction (effectiveHRight l (mpoRight mpo)))

--------------------------------------------------------------------------------
-- Local solves (concrete @C χ@ / @C p@ centres for 'groundState')
--------------------------------------------------------------------------------

type DmrgNats χ p =
  ( KnownNat χ, KnownNat p
  , KnownNat (χ * p), KnownNat (p * χ)
  , MPSConstraints (C χ) (C p)
  , FiniteDimensional (LeftSite (C χ) (C p))
  , FiniteDimensional (BulkSite (C χ) (C p))
  , FiniteDimensional (RightSite (C χ) (C p))
  , InnerSpace (LeftSite (C χ) (C p))
  , InnerSpace (BulkSite (C χ) (C p))
  , InnerSpace (RightSite (C χ) (C p))
  )

solveLeft
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  FullNorm (C χ) -> FullNorm (C p) ->
  EndoMPO (C χ) (C p) q -> MPS (C χ) (C p) q -> (Double, MPS (C χ) (C p) q)
solveLeft nb np mpo mps =
  let (e, s) = groundState (heffLeft nb np mps mpo)
  in (e, setLeft s mps)

solveBulk
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  FullNorm (C χ) -> FullNorm (C p) ->
  Int -> EndoMPO (C χ) (C p) q -> MPS (C χ) (C p) q -> (Double, MPS (C χ) (C p) q)
solveBulk nb np j mpo mps =
  let (e, s) = groundState (heffBulk nb np j mps mpo)
  in (e, mps { mpsBulk = setBulk @q j s (mpsBulk mps) })

solveRight
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  FullNorm (C χ) -> FullNorm (C p) ->
  EndoMPO (C χ) (C p) q -> MPS (C χ) (C p) q -> (Double, MPS (C χ) (C p) q)
solveRight nb np mpo mps =
  let (e, s) = groundState (heffRight nb np mps mpo)
  in (e, setRight s mps)

-- | Solve every bulk centre left→right. Boundary sites are left alone for now:
-- writing back a 'groundState' left/right centre currently breaks subsequent
-- environment builds (map-space recompose / storage layout); bulk centres are fine.
solveAllSites
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  FullNorm (C χ) -> FullNorm (C p) ->
  EndoMPO (C χ) (C p) q -> MPS (C χ) (C p) q -> (Double, MPS (C χ) (C p) q)
solveAllSites nb np mpo mps0 =
  let mBulk =
        foldl
          (\m j -> snd (solveBulk @χ @p @q nb np j mpo m))
          mps0
          [0 .. bulkCount @q - 1]
      e = energy nb np mpo mBulk
  in (e, mBulk)

--------------------------------------------------------------------------------
-- Sweep / DMRG (no gauge transport yet)
--------------------------------------------------------------------------------

sweep
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  EndoMPO (C χ) (C p) q -> MPS (C χ) (C p) q -> (Double, MPS (C χ) (C p) q)
sweep mpo mps =
  let nb = hermitianNorm
      np = hermitianNorm
      (_, mps') = solveAllSites @χ @p @q nb np mpo mps
  in (energy nb np mpo mps', mps')

data DmrgResult χ p (q :: Nat) = DmrgResult
  { dmrgFinalEnergy :: !Double
  , dmrgFinalMPS :: !(MPS (C χ) (C p) q)
  , dmrgSweepEnergies :: ![Double]
  }

dmrg
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  Int -> Double ->
  EndoMPO (C χ) (C p) q -> MPS (C χ) (C p) q -> DmrgResult χ p q
dmrg maxSweeps tol mpo = go maxSweeps [] Nothing
  where
    nb = hermitianNorm
    np = hermitianNorm
    finish e psi hist =
      DmrgResult
        { dmrgFinalEnergy = e
        , dmrgFinalMPS = psi
        , dmrgSweepEnergies = reverse hist
        }
    go 0 hist mE psi =
      finish (maybe (energy nb np mpo psi) id mE) psi hist
    go k hist mE psi =
      let (e, psi') = sweep @χ @p @q mpo psi
          hist' = e : hist
      in case mE of
           Just ePrev | abs (e - ePrev) < tol -> finish e psi' hist'
           _ -> go (k - 1) hist' (Just e) psi'

--------------------------------------------------------------------------------
-- Pauli / TFIM (bond @C 3@ = MPS χ; physical @C 2@)
--------------------------------------------------------------------------------

cdim :: forall k. KnownNat k => Int
cdim = fromIntegral (natVal (Proxy @k))

basisC :: forall k. KnownNat k => Int -> C k
basisC i =
  fromList [ if j == i then 1 else 0 | j <- [0 .. cdim @k - 1] ]

unitMap
  :: forall m n. (KnownNat m, KnownNat n)
  => Int -> Int -> (C m +> C n)
unitMap i j =
  linMapFromColumnImages
    [ if k == i then basisC @n j else zeroV | k <- [0 .. cdim @m - 1] ]

pauliX :: C 2 +> C 2
pauliX = linMapFromColumnImages [basisC @2 1, basisC @2 0]

pauliZ :: C 2 +> C 2
pauliZ = linMapFromColumnImages [basisC @2 0, (-1) *^ basisC @2 1]

idC2 :: C 2 +> C 2
idC2 = arr (Cat.id :: C 2 -+> C 2)

-- | @phys ↦ bondVec ⊗ (f $ phys)@.
embedLeft
  :: (MPSConstraints (C b) (C p), KnownNat b, KnownNat p) =>
  C b -> (C p +> C p) -> (C p +> (C b ⊗ C p))
embedLeft v f = arr (LinearFunction (\x -> v ⊗ (f $ x)))

tfimBulkOp :: Double -> Double -> (C 3 ⊗ C 2) +> (C 3 ⊗ C 2)
tfimBulkOp j h =
  let jc = (-j) :+ 0
      hc = (-h) :+ 0
  in sumV
       [ unitMap @3 @3 0 0 ⊗^ idC2
       , unitMap @3 @3 1 0 ⊗^ pauliZ
       , unitMap @3 @3 2 0 ⊗^ (hc *^ pauliX)
       , unitMap @3 @3 2 1 ⊗^ (jc *^ pauliZ)
       , unitMap @3 @3 2 2 ⊗^ idC2
       ]

tfimLeftOp :: Double -> Double -> C 2 +> (C 3 ⊗ C 2)
tfimLeftOp j h =
  let jc = (-j) :+ 0
      hc = (-h) :+ 0
  in sumV
       [ embedLeft (basisC @3 0) (hc *^ pauliX)
       , embedLeft (basisC @3 1) (jc *^ pauliZ)
       , embedLeft (basisC @3 2) idC2
       ]

-- | Row order matches 'siteLinFromRows': image of @e_b ⊗ e_s@.
tfimRightOp :: Double -> Double -> (C 3 ⊗ C 2) +> C 2
tfimRightOp _j h =
  let hc = (-h) :+ 0
      img b s =
        case b of
          0 -> basisC @2 s
          1 -> pauliZ $ basisC @2 s
          2 -> (hc *^ pauliX) $ basisC @2 s
          _ -> zeroV
  in siteLinFromRows @3 @2 @2
       [ img b s | b <- [0 .. 2], s <- [0 .. 1] ]

-- | Transverse-field Ising MPO; MPS/MPO bond both @C 3@.
tfimMPO
  :: forall (q :: Nat). KnownNat q =>
  Double -> Double -> EndoMPO (C 3) (C 2) q
tfimMPO j h =
  MPO
    { mpoLeft = tfimLeftOp j h
    , mpoBulk =
        V $ Vector.replicate (fromIntegral (natVal (Proxy @q))) (tfimBulkOp j h)
    , mpoRight = tfimRightOp j h
    , mpoBondDimHint = 3
    }

-- | Uniform seed MPS (all-ones maps), bond @C 3@, physical @C 2@.
productMPS :: forall (q :: Nat). KnownNat q => MPS (C 3) (C 2) q
productMPS =
  MPS
    (LinearMap (konst 1))
    (V $ Vector.replicate (fromIntegral (natVal (Proxy @q))) (LinearMap (konst 1)))
    (LinearMap (konst 1))
