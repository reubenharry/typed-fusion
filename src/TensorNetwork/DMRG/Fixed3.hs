{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Single-site DMRG on the typed 3-site MPS, top-down (ROADMAP Phases 4–5).
--
-- All contractions are morphism-level — composition, monoidal products of
-- maps, associators, daggers, partial traces — never coefficient loops (see
-- 'TensorNetwork.Categorical'). The two dense numerical kernels (the local
-- Hermitian eigensolve and the SVD used for gauge transport) sit behind
-- 'GroundState.groundState' and the @normalize*@ bridge below, mirroring
-- decision D3: bases live inside solvers, not in the network code.
--
-- Conventions (ROADMAP §4a):
--
--   * Site @(C bl ⊗ C p) +> C br@, transfer orientation, boundary bonds @C 1@.
--   * MPO sites in transfer orientation (domain physical = bra index).
--   * Bras are formed by 'dagger' inside the transfer/environment maps.
--   * Environments are /typed/ morphisms between tensor products of bond
--     spaces — never flattened to @C (w·a·b)@.
--
-- __Right environments as functionals.__ A left environment is the literal
-- transfer state @C a +> (C w ⊗ C b)@. A right environment represents the
-- /rest of the contraction/, i.e. the linear functional
-- @env ↦ trace (lunit ∘ T_rest env)@; it is reified as the map
-- @R : (C w ⊗ C b) +> C a@ paired by @env ↦ trace (R ∘ env)@. With that
-- representation, both the recursion 'extendRight' (a partial trace over the
-- physical leg) and the effective Hamiltonian (plain composition, see
-- 'effectiveH') follow from cyclicity of the trace.
module TensorNetwork.DMRG.Fixed3 where

import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import qualified Control.Functor.Constrained as CF
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗)
  , TensorSpace (..), FiniteDimensional (..), SubBasis
  , sampleLinearFunction, contractTensorMap
  , LinearFunction, pattern LinearFunction, (-+$>)
  , getLinearMap, LinearMap (..), linearId, euclideanNorm )
import Math.LinearMap.Coercion
  ( curryLinearMap, uncurryLinearMap, (-+$=>) )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static
  ( C, M, R, Sized (fromList, unwrap, create, extract), Domain (diagR), complex )
import Numeric.LinearAlgebra.Static.MPSLayout (siteLinearMap)
import qualified Numeric.LinearAlgebra as HM
import GHC.TypeLits (KnownNat, type (*))
import Data.Maybe (fromMaybe)
import Data.Complex (Complex ((:+)), conjugate, realPart, magnitude)
import Data.VectorSpace (InnerSpace ((<.>)), VectorSpace ((*^)), AdditiveGroup (zeroV), sumV)

import TensorNetwork.MPS.Fixed3.Internal
  ( Site (..), MPS (..), OpSite (..), MPO (..), cdim, basis )
import TensorNetwork.MPS.Fixed3
  ( mpoTransferStep, opWire, mpsInner, mpsMPOInner, mpoToMatrix
  , genMPS222, genMPO222, pauliX, pauliZ )
import TensorNetwork.Categorical
  ( (⊗^), lunit, lunitInv, swapMap, splitBond, fuseBond )
import TensorNetwork.Dagger (dagger, transposeMap)
import GroundState (groundState, groundStateDense, groundStateEigen)

import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import TensorNetwork.MPS.Fixed3 (diagMap, leftSvdFactor, rightSvdFactor)

--------------------------------------------------------------------------------
-- Spaces
--------------------------------------------------------------------------------

-- | The variational space at the active site: an MPS site map itself.
-- @Centre 1 p b1@, @Centre b1 p b2@, @Centre b2 p 1@ are the three site
-- positions of the 3-site chain.
type Centre bl p br = (C bl ⊗ C p) +> C br

-- | Left environment with MPO bond @w@, bra bond @a@, ket bond @b@: the
-- contraction of everything strictly left of the active site,
--
--   @L : C a +> (C w ⊗ C b)@   (bra bond in; MPO ⊗ ket bonds out).
type LeftEnv w a b = C a +> (C w ⊗ C b)

-- | Right environment with MPO bond @w@, bra bond @a@, ket bond @b@: the
-- functional representation of everything strictly right of the active site,
--
--   @R : (C w ⊗ C b) +> C a@,   paired with a transfer state @E@ by
--   @trace (R ∘ E)@.
type RightEnv w a b = (C w ⊗ C b) +> C a

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

-- | The trivial left environment at the open left boundary: the inverse left
-- unitor @C 1 +> (C 1 ⊗ C 1)@ (same boundary object 'mpsMPOInner' starts
-- from).
leftBoundary :: LeftEnv 1 1 1
leftBoundary = lunitInv @(C 1)

-- | The trivial right environment at the open right boundary: the left
-- unitor @(C 1 ⊗ C 1) +> C 1@, so that @trace (lunit ∘ E)@ is exactly how
-- 'mpsMPOInner' closes the chain.
rightBoundary :: RightEnv 1 1 1
rightBoundary = lunit @(C 1)

-- | Absorb one (bra site, MPO site, ket site) column into a left
-- environment. This /is/ 'mpoTransferStep':
--
--   @extendLeft L bra op ket = opWire op ket ∘ (L ⊗^ id_p) ∘ dagger bra@
extendLeft
  :: ( KnownNat wl, KnownNat wr, KnownNat p
     , KnownNat al, KnownNat ar, KnownNat bl, KnownNat br )
  => LeftEnv wl al bl
  -> Site al p ar          -- ^ bra site (conjugated internally via 'dagger')
  -> OpSite wl p wr
  -> Site bl p br          -- ^ ket site
  -> LeftEnv wr ar br
extendLeft env bra op ket = mpoTransferStep bra op ket env

-- | Absorb one column into a right environment, growing it leftwards.
--
-- Derivation: the new functional must satisfy, for every centre-side
-- environment @env : C ar +> (C wl ⊗ C br)@,
--
--   @trace (R' ∘ env) = trace (R ∘ opWire op ket ∘ (env ⊗^ id_p) ∘ dagger bra)@
--
-- Cyclicity of the trace turns the right side into
-- @trace ((env ⊗^ id_p) ∘ K)@ with @K = dagger bra ∘ R ∘ opWire op ket@, so
-- @R' = ptr_p K@ — the partial trace over the physical leg, realised as
-- 'curryLinearMap' followed by 'contractTensorMap'.
extendRight
  :: forall p wl wr al ar bl br.
     ( KnownNat wl, KnownNat wr, KnownNat p
     , KnownNat al, KnownNat ar, KnownNat bl, KnownNat br )
  => Site ar p al          -- ^ bra site
  -> OpSite wl p wr
  -> Site br p bl          -- ^ ket site
  -> RightEnv wr al bl
  -> RightEnv wl ar br
extendRight (Site bra) (OpSite op) (Site ket) envR =
  CF.fmap (contractTensorMap Cat.. CF.fmap transposeTensor)
    -+$> (curryLinearMap -+$=> k)
  where
    k :: ((C wl ⊗ C br) ⊗ C p) +> (C ar ⊗ C p)
    k = dagger bra . envR . opWire @p op ket

--------------------------------------------------------------------------------
-- Effective Hamiltonian and local solve
--------------------------------------------------------------------------------

-- | The single-site effective Hamiltonian at the active site, as an
-- endomorphism of the site's own map space (never flattened). For a centre
-- tensor @x@, ⟨ψ_y|H|φ_x⟩ = @trace (R ∘ opWire op x ∘ (L ⊗^ id_p) ∘ dagger y)@
-- = ⟨y, Heff x⟩ (Hilbert–Schmidt), so by cyclicity
--
--   @effectiveH L op R $ x = R ∘ opWire op x ∘ (L ⊗^ id_p)@.
effectiveH
  :: forall p w1 w2 b1 b2.
     ( KnownNat p, KnownNat w1, KnownNat w2, KnownNat b1, KnownNat b2 )
  => LeftEnv w1 b1 b1
  -> OpSite w1 p w2
  -> RightEnv w2 b2 b2
  -> Centre b1 p b2 +> Centre b1 p b2
effectiveH l (OpSite op) r =
  sampleLinearFunction -+$> LinearFunction
    (\x -> r . opWire @p op x . (l ⊗^ (Cat.id :: C p +> C p)))

-- | Lowest eigenpair of the effective Hamiltonian, via the dense Hermitian
-- solver 'GroundState.groundState' (ROADMAP D3) — generic over the map space,
-- so the centre is solved in place.
solveCentre
  :: ( KnownNat p, KnownNat bl, KnownNat br )
  => (Centre bl p br +> Centre bl p br)
  -> (Double, Centre bl p br)
solveCentre = groundState

--------------------------------------------------------------------------------
-- Gauge transport (SVD on flattened-domain compositions)
--------------------------------------------------------------------------------

-- | Dense matrix of a site map: row @(l·p + s)@ is the image of
-- @e_l ⊗ e_s@ — read off purely by application, so no storage-layout
-- assumptions enter the bridge.
siteMatrix
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br)
  => Site bl p br -> HM.Matrix (Complex Double)
siteMatrix (Site f) =
  HM.fromRows
    [ unwrap (f $ (basis @bl l ⊗ basis @p s))
    | l <- [0 .. cdim @bl - 1], s <- [0 .. cdim @p - 1] ]

-- | Inverse of 'siteMatrix': prescribe the image of each @e_l ⊗ e_s@ and
-- build the map by nested 'recomposeLinMap' + 'uncurryLinearMap' (the only
-- basis enumeration relied on is that of @C n@ itself).
siteFromMatrix
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br)
  => HM.Matrix (Complex Double) -> Site bl p br
siteFromMatrix m = Site (uncurryLinearMap -+$=> outer)
  where
    rows' = HM.toRows m
    img :: Int -> Int -> C br
    img l s = fromList (HM.toList (rows' !! (l * cdim @p + s)))
    inner :: Int -> (C p +> C br)
    inner l =
      fst (recomposeLinMap (entireBasis :: SubBasis (C p))
            [ img l s | s <- [0 .. cdim @p - 1] ])
    outer :: C bl +> (C p +> C br)
    outer =
      fst (recomposeLinMap (entireBasis :: SubBasis (C bl))
            [ inner l | l <- [0 .. cdim @bl - 1] ])



-- | Thin SVD via dynamic hmatrix, wrapping the factors as static matrices.
-- Intended for tall @m × n@ site layouts (@m ≥ n@); callers must ensure this.
svdTallC
  :: forall m n. (KnownNat m, KnownNat n)
  => M m n -> (M m n, R n, M n n)
svdTallC mat =
  let (u, s, v) = HM.thinSVD (extract mat)
  in ( fromMaybe (error "svdTallC: u") $ create u
     , fromMaybe (error "svdTallC: s") $ create s
     , fromMaybe (error "svdTallC: v") $ create v
     )

-- | Wrap an @M bl (p·br)@ site matrix as a 'Site'.
siteFromStorage
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br))
  => M bl (p * br) -> Site bl p br
siteFromStorage = Site . siteLinearMap

-- | Same site map with domain flattened to @C (bl·p)@ for tall SVD:
-- @f ∘ swapMap ∘ splitBond@ (flat index @l·p + s@ via 'splitBond' @p @bl).
siteForLeftSVD
  :: forall bl p br.
     ( KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * bl), KnownNat (bl * p)
     , p * bl ~ bl * p )
  => (C bl ⊗ C p) +> C br -> C (bl * p) +> C br
siteForLeftSVD f = f . swapMap . splitBond @p @bl

-- | Inverse of 'siteForLeftSVD': @g ∘ fuseBond @p @bl ∘ swapMap@.
siteFromLeftSVD
  :: forall bl p br.
     (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * bl), p * bl ~ bl * p)
  => C (bl * p) +> C br -> (C bl ⊗ C p) +> C br
siteFromLeftSVD g = g . fuseBond @p @bl . swapMap

-- | Left-orthonormalize a site (requires @bl·p ≥ br@): thin SVD
-- @M = U Σ V†@ of the @(bl·p) × br@ site matrix; the site becomes the
-- isometry @U@ and the residual bond factor @Σ V†@ is returned, to be
-- absorbed into the right neighbour as @next ∘ (factor ⊗^ id_p)@.
normalizeLeft
  :: forall bl p br.
     ( KnownNat bl, KnownNat p, KnownNat br
     , KnownNat (p * br), KnownNat (bl * p), KnownNat (p * bl), p * bl ~ bl * p )
  => Site bl p br -> (Site bl p br, C br +> C br)
normalizeLeft (Site f) =
  let (u, sv, v) = svdTallC @(bl * p) @br (getLinearMap (siteForLeftSVD f))
  in ( Site (siteFromLeftSVD (LinearMap u))
     , diagMap sv . transposeMap (LinearMap v)
     )

-- | Right-orthonormalize a site (requires @bl ≤ p·br@): thin SVD
-- @M₂ = U Σ V†@ of the @bl × (p·br)@ storage matrix; the site becomes
-- the co-isometry @V†@ and the residual bond factor @U Σ@ is returned, to be
-- absorbed into the left neighbour as @factor ∘ prev@.
normalizeRight
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br))
  => Site bl p br -> (C bl +> C bl, Site bl p br)
normalizeRight (Site f) =
  let storage = getLinearMap f
      (u, sv, v) = HM.thinSVD (extract storage)
      uM = fromMaybe (error "normalizeRight: u") $ create u
      svR = fromMaybe (error "normalizeRight: sv") $ create sv
      vh = fromMaybe (error "normalizeRight: vh") $ create (HM.tr v)
  in (rightSvdFactor uM svR, siteFromStorage @bl @p @br vh)

--------------------------------------------------------------------------------
-- Sweeping
--------------------------------------------------------------------------------

-- | Rayleigh quotient @Re ⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩@ (gauge-independent).
energy
  :: ( KnownNat p, KnownNat w, KnownNat b )
  => MPO p w -> MPS p b -> Double
energy mpo psi = realPart (mpsMPOInner psi mpo psi / mpsInner psi psi)

-- | One full left→right→left sweep of single-site updates (sites 1, 2, 3, 2),
-- with SVD gauge transport between solves so the active site is always the
-- orthogonality centre. Returns the energy of the final local solve (the
-- exact Rayleigh quotient, since its environments are isometric) and the
-- updated MPS.
sweep
  :: forall p w b.
     ( KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (p * b), KnownNat (b * p), KnownNat (b * p)
     , p * b ~ b * p, p * b ~ b * p )
  => MPO p w -> MPS p b -> (Double, MPS p b)
sweep (MPO o1 o2 o3) (MPS s1 s2 s3) =
  let -- Right-normalize so the orthogonality centre starts at site 1.
      (f3, s3r) = normalizeRight s3
      (_f2, s2r) = normalizeRight (Site (f3 . siteLin s2))
      -- (the factor absorbed into site 1 is irrelevant: site 1 is re-solved)

      -- Site 1.
      r3 = extendRight @p s3r o3 s3r rightBoundary
      r23 = extendRight @p s2r o2 s2r r3
      (_, c1) = solveCentre (effectiveH @p leftBoundary o1 r23)
      (s1n, _g1) = normalizeLeft (Site c1)
      l1 = extendLeft leftBoundary s1n o1 s1n

      -- Site 2 (rightward).
      (_, c2) = solveCentre (effectiveH @p l1 o2 r3)
      (s2n, _g2) = normalizeLeft (Site c2)
      l2 = extendLeft l1 s2n o2 s2n

      -- Site 3.
      (_, c3) = solveCentre (effectiveH @p l2 o3 rightBoundary)
      (_g3, s3n) = normalizeRight (Site c3)
      r3' = extendRight @p s3n o3 s3n rightBoundary

      -- Site 2 (leftward) — final solve of the sweep.
      (e2, c2') = solveCentre (effectiveH @p l1 o2 r3')
  in (e2, MPS s1n (Site c2') s3n)

-- | DMRG driver: sweep until the energy change drops below the tolerance or
-- the sweep budget is exhausted.
dmrg  
  :: ( KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (p * b), KnownNat (b * p), KnownNat (b * p)
     , p * b ~ b * p, p * b ~ b * p )
  => Int                       -- ^ maximum number of sweeps
  -> Double                    -- ^ energy convergence tolerance
  -> MPO p w
  -> MPS p b
  -> (Double, MPS p b)
dmrg maxSweeps tol mpo = go maxSweeps Nothing
  where
    go 0 mE psi = (maybe (energy mpo psi) id mE, psi)
    go k mE psi =
      let (e, psi') = sweep mpo psi
      in case mE of
           Just ePrev | abs (e - ePrev) < tol -> (e, psi')
           _ -> go (k - 1) (Just e) psi'

--------------------------------------------------------------------------------
-- Benchmark model
--------------------------------------------------------------------------------

-- | The elementary bond map @e_i ↦ e_j@ (data entry).
unitMap
  :: forall m n. (KnownNat m, KnownNat n)
  => Int -> Int -> (C m +> C n)
unitMap i j =
  fst (recomposeLinMap (entireBasis :: SubBasis (C m))
        [ if k == i then basis @n j else zeroV | k <- [0 .. cdim @m - 1] ])

-- | Transverse-field Ising on 3 sites, open boundaries:
--
--   @H = -J (σᶻ₁σᶻ₂ + σᶻ₂σᶻ₃) - h (σˣ₁ + σˣ₂ + σˣ₃)@
--
-- as the standard bond-dimension-3 MPO
--
--   @W = [[1, 0, 0], [σᶻ, 0, 0], [-h·σˣ, -J·σᶻ, 1]]@
--
-- with the left boundary picking row 2 and the right boundary column 0. The
-- sites are sums of @bond-unit ⊗^ physical-block@ — no basis enumeration of
-- the tensor space.
tfimMPO
  :: Double                    -- ^ coupling J
  -> Double                    -- ^ transverse field h
  -> MPO 2 3
tfimMPO j h = MPO opL opC opR
  where
    jc = (-j) :+ 0
    hc = (-h) :+ 0
    idP = Cat.id :: C 2 +> C 2
    opC = OpSite $ sumV
      [ unitMap @3 @3 0 0 ⊗^ idP
      , unitMap @3 @3 1 0 ⊗^ pauliZ
      , unitMap @3 @3 2 0 ⊗^ (hc *^ pauliX)
      , unitMap @3 @3 2 1 ⊗^ (jc *^ pauliZ)
      , unitMap @3 @3 2 2 ⊗^ idP
      ]
    opL = OpSite $ sumV
      [ unitMap @1 @3 0 0 ⊗^ (hc *^ pauliX)
      , unitMap @1 @3 0 1 ⊗^ (jc *^ pauliZ)
      , unitMap @1 @3 0 2 ⊗^ idP
      ]
    opR = OpSite $ sumV
      [ unitMap @3 @1 0 0 ⊗^ idP
      , unitMap @3 @1 1 0 ⊗^ pauliZ
      , unitMap @3 @1 2 0 ⊗^ (hc *^ pauliX)
      ]

--------------------------------------------------------------------------------
-- Validation helpers and properties
--------------------------------------------------------------------------------

-- | Exact ground energy of the dense @C (p³)@ operator ('mpoToMatrix'),
-- via the Hermitian eigensolver.
denseGroundEnergy
  :: forall p w.
     ( KnownNat p, KnownNat w, KnownNat (w * p)
     , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p)
     , KnownNat (p * p), KnownNat (p * p), KnownNat (p * 1)
     , KnownNat (p * p), p * p ~ p * p )
  => MPO p w -> Double
denseGroundEnergy mpo =
  let m = unwrap (mpoToMatrix mpo)
      (vals, _) = HM.eigSH (HM.sym m)
  in HM.minElement vals

-- | Deterministic pseudo-random @MPS 2 2 2@ (Gaussian-integer entries).
seededMPS222 :: Int -> MPS 2 2
seededMPS222 seed = unGen genMPS222 (mkQCGen seed) 30

-- | ⟨y, Heff x⟩ (Hilbert–Schmidt, via the library inner product on the
-- centre's map space) equals the full network contraction
-- ⟨ψ_y|H|φ_x⟩ with the surrounding sites frozen.
prop_effectiveHMatchesInner :: QC.Property
prop_effectiveHMatchesInner =
  QC.forAll genMPS222 $ \(MPS s1 y s3) ->
  QC.forAll genMPS222 $ \(MPS _ x _) ->
  QC.forAll genMPO222 $ \mpo@(MPO o1 o2 o3) ->
    let l1 = extendLeft leftBoundary s1 o1 s1
        r3 = extendRight @2 s3 o3 s3 rightBoundary
        heff = effectiveH @2 l1 o2 r3
        lhs = siteLin y <.> (heff $ siteLin x)
        rhs = mpsMPOInner (MPS s1 y s3) mpo (MPS s1 x s3)
    in lhs QC.=== rhs

-- | For a Hermitian MPO (TFIM) the effective Hamiltonian is Hermitian:
-- ⟨x, Heff y⟩ = conj ⟨y, Heff x⟩. Tested explicitly because a solver that
-- symmetrises would mask a violation.
-- (Up to floating-point rounding: unlike the Gaussian-integer site entries,
-- the TFIM couplings are not exact in binary.)
prop_effectiveHHermitian :: QC.Property
prop_effectiveHHermitian =
  QC.forAll genMPS222 $ \(MPS s1 y s3) ->
  QC.forAll genMPS222 $ \(MPS _ x _) ->
    let MPO o1 o2 o3 = tfimMPO 1 0.7
        l1 = extendLeft leftBoundary s1 o1 s1
        r3 = extendRight @2 s3 o3 s3 rightBoundary
        heff = effectiveH @2 l1 o2 r3
        lhs = siteLin x <.> (heff $ siteLin y)
        rhs = conjugate (siteLin y <.> (heff $ siteLin x))
        scale = 1 + magnitude lhs + magnitude rhs
    in QC.counterexample (show lhs ++ " /≈ " ++ show rhs)
         (magnitude (lhs - rhs) <= 1e-9 * scale)

-- | Flattening the domain via @swapMap ∘ splitBond@ yields the same @(bl·p) × br@
-- matrix as the application-based 'siteMatrix' oracle.
prop_flatLeftSVDMatchesSiteMatrix :: QC.Property
prop_flatLeftSVDMatchesSiteMatrix =
  QC.forAll genMPS222 $ \(MPS s122 s222 s221) ->
    extract (getLinearMap (siteForLeftSVD @1 @2 @2 (siteLin s122)))
      QC.=== siteMatrix @1 @2 @2 s122
      QC..&&. extract (getLinearMap (siteForLeftSVD @2 @2 @2 (siteLin s222)))
              QC.=== siteMatrix @2 @2 @2 s222
      QC..&&. extract (getLinearMap (siteForLeftSVD @2 @2 @1 (siteLin s221)))
              QC.=== siteMatrix @2 @2 @1 s221

-- | Map-space 'groundState' agrees with the dense oracle on TFIM effective
-- Hamiltonians (interim: both use 'groundStateDense' until map-space 'eigen'
-- is unblocked).
prop_groundStateMatchesDense :: QC.Property
prop_groundStateMatchesDense =
  QC.forAll genMPS222 $ \(MPS s1 _ s3) ->
    let MPO o1 o2 o3 = tfimMPO 1 0.7
        l1 = extendLeft leftBoundary s1 o1 s1
        r3 = extendRight @2 s3 o3 s3 rightBoundary
        heff = effectiveH @2 l1 o2 r3
        (eEigen, _) = groundState heff
        (eDense, _) = groundStateDense heff
    in eEigen QC.=== eDense

-- | On a 'HilbertSpace' (@C 4@), the 'eigen' path matches the dense oracle.
prop_eigenMatchesDenseC4 :: QC.Property
prop_eigenMatchesDenseC4 =
  let f = (2 :: Complex Double) *^ (linearId :: C 4 +> C 4)
      (eEigen, _) = groundStateEigen euclideanNorm f
      (eDense, _) = groundStateDense f
  in eEigen QC.=== eDense QC..&&. eEigen QC.=== 2
