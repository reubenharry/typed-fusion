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
-- ('effectiveHLeft' / 'effectiveHBulk' / 'effectiveHRight'). Local solves use
-- 'GroundState.groundStateDense' (HS densification + eigSH). Do not use
-- 'groundStateSimple' / library 'eigen' here: on map-space centres it returns
-- vectors whose true HS Rayleigh is not the reported eigenvalue
-- ('cabal run dmrg-site-variational').
--
-- For bulk length 1, 'sweep' gauge-centres left → bulk → right before each
-- local solve. Multi-bulk gauge transport is not wired yet.
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
import GHC.TypeLits (KnownNat, Nat, type (*), type (<=))
import Data.Proxy (Proxy (..))
import GHC.TypeNats (natVal, sameNat)
import Data.Type.Equality ((:~:) (Refl))

import Control.Lens ((^.), (&), (%~), (^?))
import GroundState (groundStateDense)
import TensorNetwork.Categorical ((⊗^))
import TensorNetwork.MPS.LinmapStorage (linMapFromColumnImages, siteLinFromRows)
import TensorNetwork.MPS.General
  ( FullNorm (..), MPS (..), MPO (..)
  , LeftSite, BulkSite, RightSite
  , MPSConstraints, SiteDagger, hermitianNorm
  , mpsInner, mpsMPOInner
  , effectiveHLeft, effectiveHBulk, effectiveHRight
  , mixedCanonicalCentre3, mixedCanonicalLeft3, mixedCanonicalRight3
  , mpsBulk, mpoLeft, mpoBulk, mpoRight, mpsLeft, mpsRight, mpoApplyExact
  )
import TensorNetwork.DMRG.Chain
  ( getBulk )
import TensorNetwork.DMRG.Env
  ( leftEnvBeforeBulk, leftEnvBeforeRight
  , rightEnvAfterBulk, rightEnvAfterLeft
  )
import Control.Lens.Setter ((.~))
import Control.Lens.At (Ixed(ix))
import Control.Lens.Combinators (to)
import Control.Monad.RWS (MonadWriter(..))
import Control.Monad.Trans.Writer (runWriter)
import Debug.Trace (traceM)

--------------------------------------------------------------------------------
-- Energy
--------------------------------------------------------------------------------

energy
  :: forall bond phys (q :: Nat).
  (MPSConstraints bond phys, SiteDagger bond phys bond) =>
  FullNorm bond -> FullNorm phys ->
  MPO bond q phys phys -> MPS bond phys q -> Double
energy nb np mpo psi =
  realPart (mpsMPOInner nb np psi mpo psi / mpsInner nb np psi psi)

--------------------------------------------------------------------------------
-- Effective Hamiltonian endomorphisms
--------------------------------------------------------------------------------

heffLeft
  :: forall bond phys (q :: Nat).
  (MPSConstraints bond phys, KnownNat q, SiteDagger bond phys bond) =>
  FullNorm bond -> FullNorm phys ->
  MPS bond phys q -> MPO bond q phys phys ->
  LeftSite bond phys +> LeftSite bond phys
heffLeft nb np mps mpo =
  let r = rightEnvAfterLeft nb np mps mpo
  in arr (LinearFunction (effectiveHLeft (mpo ^. mpoLeft) r))

heffBulk
  :: forall bond phys (q :: Nat).
  (MPSConstraints bond phys, KnownNat q, SiteDagger bond phys bond) =>
  FullNorm bond -> FullNorm phys ->
  Int -> MPS bond phys q -> MPO bond q phys phys ->
  BulkSite bond phys +> BulkSite bond phys
heffBulk nb np j mps mpo =
  let l = leftEnvBeforeBulk nb np j mps mpo
      r = rightEnvAfterBulk nb np j mps mpo
      op = getBulk @q j (mpo ^. mpoBulk)
  in arr (LinearFunction (effectiveHBulk l op r))

heffRight
  :: forall bond phys (q :: Nat).
  (MPSConstraints bond phys, KnownNat q, SiteDagger bond phys bond) =>
  FullNorm bond -> FullNorm phys ->
  MPS bond phys q -> MPO bond q phys phys ->
  RightSite bond phys +> RightSite bond phys
heffRight nb np mps mpo =
  let l = leftEnvBeforeRight nb np mps mpo
  in arr (LinearFunction (effectiveHRight l (mpo ^. mpoRight)))

--------------------------------------------------------------------------------
-- Local solves (concrete @C χ@ / @C p@ centres for 'groundState')
--------------------------------------------------------------------------------

type DmrgNats χ p =
  ( KnownNat χ, KnownNat p
  , KnownNat (χ * p), KnownNat (p * χ)
  , χ * p ~ p * χ, p <= χ
  )

solveLeft
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  FullNorm (C χ) -> FullNorm (C p) ->
  MPO (C χ) q (C p) (C p) -> MPS (C χ) (C p) q -> (Double, MPS (C χ) (C p) q)
solveLeft nb np mpo mps =
  let (e, s) = groundStateDense (heffLeft nb np mps mpo)
  in (e, mps & mpsLeft .~ s)

solveBulk
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  FullNorm (C χ) -> FullNorm (C p) ->
  Int -> MPO (C χ) q (C p) (C p) -> MPS (C χ) (C p) q -> (Double, MPS (C χ) (C p) q)
solveBulk nb np j mpo mps =
  let (e, s) = groundStateDense (heffBulk nb np j mps mpo)
  in (e, mps & mpsBulk %~ ix j .~ s)

solveRight
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  FullNorm (C χ) -> FullNorm (C p) ->
  MPO (C χ) q (C p) (C p) -> MPS (C χ) (C p) q -> (Double, MPS (C χ) (C p) q)
solveRight nb np mpo mps =
  let (e, s) = groundStateDense (heffRight nb np mps mpo)
  in (e, mps & mpsRight .~ s)

swap (a,b) = (b,a)

-- | One left→right pass of local solves.
--
-- For three-site chains (@q = 1@), each site is mixed-canonicalized about the
-- orthogonality centre before its Krylov solve (HS @Heff@ is only variational
-- there). Longer chains still solve bulk sites only (zipper gauge not wired).
solveAllSites
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  FullNorm (C χ) -> FullNorm (C p) ->
  MPO (C χ) q (C p) (C p) -> MPS (C χ) (C p) q -> (MPS (C χ) (C p) q, [Double])
solveAllSites nb np mpo mps0 =
  case sameNat (Proxy @q) (Proxy @1) of
    Just Refl -> runWriter $ do 
      let mpsL = mixedCanonicalLeft3 mps0
      (_, m1) <- pure $ solveLeft @χ @p @1 nb np mpo mpsL
      tell [energy nb np mpo m1]
      traceM $ show $ energy nb np mpo m1

      let mpsC = mixedCanonicalCentre3 m1
      (_, m2) <- pure $ solveBulk @χ @p @1 nb np 0 mpo mpsC
      tell [energy nb np mpo m2]
      traceM $ show $ energy nb np mpo m2

      let mpsR = mixedCanonicalRight3 m2
      (_, m3) <- pure $ solveRight @χ @p @1 nb np mpo mpsR
      tell [energy nb np mpo m3]
      traceM $ show $ energy nb np mpo m3
      return m3
    Nothing -> undefined
      -- let mBulk =
      --       foldl
      --         (\m j -> snd (solveBulk @χ @p @q nb np j mpo m))
      --         mps0
      --         [0 .. cdim @q - 1]
      -- in (energy nb np mpo mBulk, mBulk)


--------------------------------------------------------------------------------
-- Sweep / DMRG
--------------------------------------------------------------------------------

sweep
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  MPO (C χ) q (C p) (C p) -> MPS (C χ) (C p) q -> (MPS (C χ) (C p) q, [Double])
sweep mpo mps =
  let nb = hermitianNorm
      np = hermitianNorm
      (mps', energies) =solveAllSites @χ @p @q nb np mpo mps
  in (mps', energies)

data DmrgResult χ p (q :: Nat) = DmrgResult
  { dmrgFinalEnergy :: !Double
  , dmrgFinalMPS :: !(MPS (C χ) (C p) q)
  , dmrgSweepEnergies :: ![Double]
  }

dmrg
  :: forall χ p (q :: Nat).
  (DmrgNats χ p, KnownNat q) =>
  Int -> Double ->
  MPO (C χ) q (C p) (C p) -> MPS (C χ) (C p) q -> DmrgResult χ p q
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
      let (psi', energies) = sweep @χ @p @q mpo psi
          hist' = hist <> energies
      in case mE of
           Just ePrev | abs (last energies - ePrev) < tol -> finish (last energies) psi' hist'
           _ -> go (k - 1) hist' (Just (last energies)) psi'

--------------------------------------------------------------------------------
-- Finite-state transducers → MPO
--
-- A transducer is the local law
--   W : B → B ⊗ End(V),   W(|b⟩) = Σ_{b'} |b'⟩ ⊗ op_{b→b'}
-- plus boundary states (start, accept). Compilation:
--
--   left  :: V → B ⊗ V     = W(|start⟩)          (no incoming bond)
--   bulk  :: B ⊗ V → B ⊗ V = full W              (each edge |src⟩↦|dst⟩ ⊗ op)
--   right :: B ⊗ V → V     = ⟨accept| ∘ W        (keep only edges into accept)
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

-- | @phys ↦ |bond⟩ ⊗ (op $ phys)@.
embedLeft
  :: (MPSConstraints (C b) (C p), KnownNat b, KnownNat p) =>
  C b -> (C p +> C p) -> (C p +> (C b ⊗ C p))
embedLeft v f = arr (LinearFunction (\x -> v ⊗ (f $ x)))

-- | Sparse finite transducer on a named bond basis @b@ (with @Enum@/@Bounded@
-- indexing into @C χ@).
data FiniteTransducer b p = FiniteTransducer
  { ftStart  :: b
  , ftAccept :: b
  , ftStep   :: b -> [(b, p +> p)]  -- W(|b⟩)
  }

-- | One transducer edge @src -op→ dst@ as a bulk Kronecker term
-- @(|dst⟩⟨src|) ⊗ op@.
compileEdge
  :: forall χ p b. (KnownNat χ, KnownNat p, Enum b) =>
  b -> b -> (C p +> C p) -> (C χ ⊗ C p) +> (C χ ⊗ C p)
compileEdge src dst op =
  unitMap @χ @χ (fromEnum src) (fromEnum dst) ⊗^ op

-- | Bulk tensor: sum of all edges of @W@.
compileBulk
  :: forall χ p b. (KnownNat χ, KnownNat p, Enum b, Bounded b) =>
  (b -> [(b, C p +> C p)]) -> (C χ ⊗ C p) +> (C χ ⊗ C p)
compileBulk step =
  sumV
    [ compileEdge @χ @p src dst op
    | src <- [minBound .. maxBound]
    , (dst, op) <- step src
    ]

-- | Left tensor: apply @W@ at @start@ (inject physical space into @B ⊗ V@).
compileLeft
  :: forall χ p b. (KnownNat χ, KnownNat p, Enum b, MPSConstraints (C χ) (C p)) =>
  b -> (b -> [(b, C p +> C p)]) -> C p +> (C χ ⊗ C p)
compileLeft start step =
  sumV
    [ embedLeft (basisC @χ (fromEnum dst)) op
    | (dst, op) <- step start
    ]

-- | Op along the unique edge @src → accept@, or zero if none.
acceptingOp
  :: (Eq b, KnownNat p) => b -> (b -> [(b, C p +> C p)]) -> b -> (C p +> C p)
acceptingOp accept step src =
  case [op | (dst, op) <- step src, dst == accept] of
    (op : _) -> op
    []       -> zeroV

-- | Right tensor: on basis @|src⟩ ⊗ |s⟩@ apply the accepting op at @src@.
-- Equivalently @⟨accept| ∘ W@ with the outgoing bond discarded.
compileRight
  :: forall χ p b.
  ( KnownNat χ, KnownNat p, KnownNat (χ * p), KnownNat (p * p)
  , Enum b, Bounded b, Eq b
  ) =>
  b -> (b -> [(b, C p +> C p)]) -> (C χ ⊗ C p) +> C p
compileRight accept step = siteLinFromRows @χ @p @p
       [ acceptingOp accept step (toEnum b) $ basisC @p s
       | b <- [0 .. cdim @χ - 1]
       , s <- [0 .. cdim @p - 1]
       ]

-- | Compile a transducer on @C χ@ into an open-boundary MPO of bulk length @q@.
-- Requires @fromEnum@ of @b@ to land in @[0 .. χ)@.
compileTransducerMPO
  :: forall χ q b p.
  ( KnownNat χ, KnownNat q, KnownNat p, KnownNat (χ * p), KnownNat (p * p)
  , Enum b, Bounded b, Eq b
  , MPSConstraints (C χ) (C p)
  ) =>
  FiniteTransducer b (C p) -> MPO (C χ) q (C p) (C p)
compileTransducerMPO (FiniteTransducer start accept step) =
  MPO
    { _mpoLeft = compileLeft @χ @p start step
    , _mpoBulk =
        V $ Vector.replicate (fromIntegral (natVal (Proxy @q))) (compileBulk @χ @p step)
    , _mpoRight = compileRight @χ @p accept step
    , _mpoBondDimHint = cdim @χ
    }

--------------------------------------------------------------------------------
-- TFIM transducer (bond @C 3@, physical @C 2@)
--
--   B = span{|f⟩, |z⟩, |s⟩} with indices F=0, ZHalf=1, S=2
--   W(|s⟩) = |s⟩⊗I + |z⟩⊗(-J Z) + |f⟩⊗(-h X)
--   W(|z⟩) = |f⟩⊗Z
--   W(|f⟩) = |f⟩⊗I
--   start = S, accept = F
--------------------------------------------------------------------------------

pauliX :: C 2 +> C 2
pauliX = linMapFromColumnImages [basisC @2 1, basisC @2 0]

pauliZ :: C 2 +> C 2
pauliZ = linMapFromColumnImages [basisC @2 0, (-1) *^ basisC @2 1]

idC2 :: C 2 +> C 2
idC2 = arr (Cat.id :: C 2 -+> C 2)

data TfimBond = F | ZHalf | S
  deriving (Eq, Ord, Show, Enum, Bounded)

tfimW :: Double -> Double -> TfimBond -> [(TfimBond, C 2 +> C 2)]
tfimW j h b =
  let jc = (-j) :+ 0
      hc = (-h) :+ 0
  in case b of
       S     -> [(S, idC2), (ZHalf, jc *^ pauliZ), (F, hc *^ pauliX)]
       ZHalf -> [(F, pauliZ)]
       F     -> [(F, idC2)]

tfimTransducer :: Double -> Double -> FiniteTransducer TfimBond (C 2)
tfimTransducer j h =
  FiniteTransducer
    { ftStart  = S
    , ftAccept = F
    , ftStep   = tfimW j h
    }

-- | Transverse-field Ising MPO; MPS/MPO bond both @C 3@.
tfimMPO
  :: forall (q :: Nat). KnownNat q =>
  Double -> Double -> MPO (C 3) q (C 2) (C 2)
tfimMPO j h = compileTransducerMPO @3 @q (tfimTransducer j h)

-- | Uniform seed MPS (all-ones maps), bond @C 3@, physical @C 2@.
productMPS :: forall (q :: Nat). KnownNat q => MPS (C 3) (C 2) q
productMPS =
  MPS
    (LinearMap (konst 1))
    (V $ Vector.replicate (fromIntegral (natVal (Proxy @q))) (LinearMap (konst 1)))
    (LinearMap (konst 1))


dmrgExample :: DmrgResult 3 2 1
dmrgExample = dmrg 2 5e-4 (tfimMPO 0.5 0.5) productMPS

dmrgExample2 :: MPS   (C 3 ⊗ C 3)   (C 2)   1
dmrgExample2 = mpoApplyExact (tfimMPO 0.5 0.5) productMPS

dmrgExample3 = (e1, e2) where 
  e1 = energy hermitianNorm hermitianNorm (tfimMPO @1 0.5 0.5) productMPS
  e2 = energy hermitianNorm hermitianNorm (tfimMPO @1 0.5 0.5) (mixedCanonicalLeft3 productMPS)

-- displayMPS :: MPS (C 3) (C 2) 1 -> String
displayMPS mps = "MPS:\n " <> "Left Boundary: " <> show (mps ^. mpsLeft . to getLinearMap) <> "\n" <> "Bulk: " <> show (mps ^? mpsBulk . ix 0 . to getLinearMap) <> "\n" <> "Right Boundary: " <> show (mps ^. mpsRight . to getLinearMap)

-- try:
-- compute energy and check it matches 
-- apply mpo and see that it works