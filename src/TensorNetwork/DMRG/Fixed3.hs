{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs #-}

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
import GHC.TypeLits (KnownNat, type (*), Nat, type (-), type (+))
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Complex (Complex ((:+)), conjugate, realPart, magnitude)
import Data.VectorSpace (InnerSpace ((<.>)), VectorSpace ((*^)), AdditiveGroup (zeroV), sumV)

import TensorNetwork.MPS.Fixed3.Internal
  ( Site (..), MPS (..), OpSite (..), MPO (..), cdim, basis
  , MPS3, MPO3, mps3, mpo3, withMPS3, withMPO3 )
import TensorNetwork.MPS.Fixed3
  ( mpoTransferStep, opWire, mpsInner, mpsMPOInner, mpoToMatrix
  , genMPS222, genMPO222, pauliX, pauliZ )
import TensorNetwork.Categorical
  ( (⊗^), lunit, lunitInv, swapMap, splitBond, fuseBond )
import TensorNetwork.Dagger (dagger, transposeMap)
import GroundState (groundState, groundStateDense, groundStateEigen)
import TensorNetwork.DMRG.Chain
  ( chainLength
  , getSite, getOp, setSite, SomeSite (..), SomeOpSite (..) )
import TensorNetwork.DMRG.Env
  ( LeftEnv, RightEnv, leftBoundary, rightBoundary, extendLeft, extendRight
  , MoveRightEnv' (..), moveRightEnv'
  , MoveLeftEnv' (..), moveLeftEnv'
  , LeftEnvAtCentre (..), RightEnvAtCentre (..)
  , buildRightEnvFromSite
  , updateEnvsMoveRight, updateEnvsMoveLeft )

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
  => MPO3 p w -> MPS p b 1 -> Double
energy mpo psi = realPart (mpsMPOInner psi mpo psi / mpsInner psi psi)

--------------------------------------------------------------------------------
-- Zipper ('MPS' + value-level centre index)
--------------------------------------------------------------------------------

-- | DMRG workspace: full chain, active site index, environments.
data MPSZipper p b w l = MPSZipper
  { theMPO :: MPO p w l
  , theMPS :: MPS p b l
  , centreIndex :: Int
  , leftEnv :: LeftEnvAtCentre w b
  , rightEnv :: RightEnvAtCentre w b
  }

departLeft
  :: forall bl p br
   . ( KnownNat bl, KnownNat p, KnownNat br
     , KnownNat (p * br), KnownNat (bl * p), KnownNat (p * bl)
     , p * bl ~ bl * p )
  => Site bl p br -> Site bl p br
departLeft = fst . normalizeLeft

departRight
  :: forall bl p br
   . ( KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br) )
  => Site bl p br -> Site bl p br
departRight = snd . normalizeRight

departSiteLeft
  :: forall p b
   . ( KnownNat p, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  => SomeSite p b -> SomeSite p b
departSiteLeft (SiteLeft s) = SiteLeft (departLeft s)
departSiteLeft (SiteBulk s) = SiteBulk (departLeft s)
departSiteLeft SiteRight{} =
  error "departSiteLeft: unexpected right-end site"

departSiteRight
  :: forall p b. (KnownNat p, KnownNat b, KnownNat (p * b))
  => SomeSite p b -> SomeSite p b
departSiteRight (SiteBulk s) = SiteBulk (departRight s)
departSiteRight (SiteRight s) = SiteRight (departRight s)
departSiteRight SiteLeft{} =
  error "departSiteRight: unexpected left-end site"

-- | Right-orthonormalize sites @n .. 2@, absorbing bond factors leftwards.
rightGaugeMPS
  :: forall p b l
   . ( KnownNat l, KnownNat p, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  => MPS p b l -> MPS p b l
rightGaugeMPS = go (chainLength @l) Cat.id
  where
    n = chainLength @l
    go k bondIn mpsAcc
      | k <= 1 = mpsAcc
      | k == n =
          case getSite k mpsAcc of
            SiteRight s ->
              let (bondOut, sr) = normalizeRight s
              in go (k - 1) bondOut (setSite k (SiteRight sr) mpsAcc)
            _ -> error "rightGaugeMPS: expected last site"
      | otherwise =
          case getSite k mpsAcc of
            SiteBulk s ->
              let s' = Site (bondIn . siteLin s)
                  (bondOut, sb) = normalizeRight s'
              in go (k - 1) bondOut (setSite k (SiteBulk sb) mpsAcc)
            _ -> error "rightGaugeMPS: expected bulk site"

solveCentreSite
  :: forall p wl wr bl br
   . ( KnownNat p, KnownNat wl, KnownNat wr, KnownNat bl, KnownNat br )
  => LeftEnv wl bl bl
  -> OpSite wl p wr
  -> RightEnv wr br br
  -> Site bl p br
  -> (Double, Site bl p br)
solveCentreSite l op r (Site _) =
  let (e, c) = solveCentre (effectiveH @p l op r)
  in (e, Site c)

solveSiteAt
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b )
  => Int
  -> LeftEnvAtCentre w b
  -> SomeOpSite p w
  -> RightEnvAtCentre w b
  -> SomeSite p b
  -> SomeSite p b
solveSiteAt i l op r cn =
  let n = chainLength @l
  in case (i, l, op, r, cn) of
       (1, LeftEnvFirst lv, OpLeft o, RightEnvBulk rv, SiteLeft c) ->
         SiteLeft (snd (solveCentreSite lv o rv c))
       (j, LeftEnvBulk lv, OpBulk o, RightEnvBulk rv, SiteBulk c)
         | j > 1 && j < n ->
             SiteBulk (snd (solveCentreSite lv o rv c))
       (n, LeftEnvBulk lv, OpRight o, RightEnvLast rv, SiteRight c) ->
         SiteRight (snd (solveCentreSite lv o rv c))
       _ ->
         error ("solveSiteAt: site/op/env shape mismatch at index " ++ show i)

centreEnergyAt
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b )
  => Int
  -> LeftEnvAtCentre w b
  -> SomeOpSite p w
  -> RightEnvAtCentre w b
  -> Double
centreEnergyAt i l op r =
  let n = chainLength @l
  in case (i, l, op, r) of
       (1, LeftEnvFirst lv, OpLeft o, RightEnvBulk rv) ->
         fst (solveCentre (effectiveH @p lv o rv))
       (j, LeftEnvBulk lv, OpBulk o, RightEnvBulk rv) | j > 1 && j < n ->
         fst (solveCentre (effectiveH @p lv o rv))
       (n, LeftEnvBulk lv, OpRight o, RightEnvLast rv) ->
         fst (solveCentre (effectiveH @p lv o rv))
       _ ->
         error ("centreEnergyAt: site/op/env shape mismatch at index " ++ show i)

moveRight
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  => MPSZipper p b w l -> MPSZipper p b w l
moveRight z@MPSZipper{centreIndex = i, theMPS = mps, theMPO = mpo, leftEnv = l, rightEnv = r}
  | i >= chainLength @l =
      error ("moveRight: centre " ++ show i ++ " at right boundary")
  | otherwise =
    let wit = moveRightEnv' @l i
        cn = departSiteLeft (getSite i mps)
        mps' = setSite i cn mps
        (l', r') =
          updateEnvsMoveRight @p @w @b @l
            i wit mpo mps' l cn (getOp i mpo) r
    in z { centreIndex = i + 1, theMPS = mps', leftEnv = l', rightEnv = r' }

moveLeft
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  => MPSZipper p b w l -> MPSZipper p b w l
moveLeft z@MPSZipper{centreIndex = i, theMPS = mps, theMPO = mpo, rightEnv = r}
  | i <= 1 =
      error ("moveLeft: centre " ++ show i ++ " at left boundary")
  | otherwise =
    let wit = moveLeftEnv' i
        cn = departSiteRight (getSite i mps)
        mps' = setSite i cn mps
        (l', r') =
          updateEnvsMoveLeft @p @w @b @l
            i wit mpo mps' r cn (getOp i mpo)
    in z { centreIndex = i - 1, theMPS = mps', leftEnv = l', rightEnv = r' }

toZipper
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  => MPO p w l -> MPS p b l -> MPSZipper p b w l
toZipper mpo mps =
  let mps' = rightGaugeMPS mps
      rEnv = buildRightEnvFromSite 2 mpo mps'
  in MPSZipper mpo mps' 1 (LeftEnvFirst leftBoundary) (RightEnvBulk rEnv)



solveCenterAt
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b )
  => MPSZipper p b w l -> MPSZipper p b w l
solveCenterAt z@MPSZipper{centreIndex = i, theMPS = mps, theMPO = mpo, leftEnv = l, rightEnv = r} =
  let solved = solveSiteAt @p @w @b @l i l (getOp i mpo) r (getSite i mps)
  in z { theMPS = setSite i solved mps }

centreEnergy
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b )
  => MPSZipper p b w l -> Double
centreEnergy MPSZipper{centreIndex = i, theMPO = mpo, leftEnv = l, rightEnv = r} =
  centreEnergyAt @p @w @b @l i l (getOp i mpo) r

type ZipperStep p b w l = MPSZipper p b w l -> MPSZipper p b w l

-- | One left→right pass (solve at each site), then a partial left pass
-- stopping at site @2@. Returns the local energy at the final centre.
sweepSchedule
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  => MPO p w l
  -> ZipperStep p b w l
  -> MPS p b l
  -> (Double, MPS p b l)
sweepSchedule mpo step mps0 =
  let z0 = toZipper mpo mps0
      n = chainLength @l
      zRight = (iterate (step . moveRight) (step z0) !! (n - 1))
      zFinal = (iterate (step . moveLeft) zRight !! (n - 2))
  in (centreEnergy zFinal, theMPS zFinal)



-- | One full sweep via 'sweepSchedule': right pass over all sites, then partial
-- left pass stopping at site @2@ (legacy 3-site schedule @1→2→3→2@). Gauge
-- transport happens in 'moveRight'/'moveLeft'. Returns the final centre energy
-- and the updated MPS.
sweep
  :: forall p w b.
     ( KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (p * b), KnownNat (b * p), KnownNat (b * p)
     , p * b ~ b * p, p * b ~ b * p )
  => SweepFunction p w b
sweep mpo psi0 =
  let (e, mps') = sweepSchedule mpo solveCenterAt psi0
  in (e, mps')

-- | DMRG driver: sweep until the energy change drops below the tolerance or
-- the sweep budget is exhausted.
dmrg
  :: ( KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (p * b), KnownNat (b * p), KnownNat (b * p)
     , p * b ~ b * p, p * b ~ b * p )
  => Int                       -- ^ maximum number of sweeps
  -> Double                    -- ^ energy convergence tolerance
  -> MPO3 p w
  -> SweepFunction p w b
  -> MPS p b 1
  -> (Double, MPS p b 1)
dmrg maxSweeps tol mpo sweepFunction = go maxSweeps Nothing
  where
    go 0 mE psi = (maybe (energy mpo psi) id mE, psi)
    go k mE psi =
      let (e, psi') = sweepFunction mpo psi
      in case mE of
           Just ePrev | abs (e - ePrev) < tol -> (e, psi')
           _ -> go (k - 1) (Just e) psi'

-- | DMRG driver in 'SvdM' (run with 'runSvdM' and a fixed seed).
dmrgM
  :: forall p w b m.
    (Monad m, KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p)
     , p * b ~ b * p )
  => Int -> Double -> MPO3 p w -> SweepFunctionM m p w b -> MPS p b 1 -> m (Double, MPS p b 1)
dmrgM maxSweeps tol mpo sweepFunction psi0 = go maxSweeps Nothing psi0
  where
    go 0 mE psi = pure (fromMaybe (energy mpo psi) mE, psi)
    go k mE psi = do
      (e, psi') <- sweepFunction mpo psi
      case mE of
        Just ePrev | abs (e - ePrev) < tol -> pure (e, psi')
        _ -> go (k - 1) (Just e) psi'


type SweepFunctionM m p w b = MPO3 p w -> MPS p b 1 -> m (Double, MPS p b 1)
type SweepFunction p w b = MPO3 p w -> MPS p b 1 -> (Double, MPS p b 1)


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
  -> MPO3 2 3
tfimMPO j h = mpo3 opL opC opR
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
  => MPO3 p w -> Double
denseGroundEnergy mpo =
  let m = unwrap (mpoToMatrix mpo)
      (vals, _) = HM.eigSH (HM.sym m)
  in HM.minElement vals

-- | Deterministic pseudo-random @MPS 2 2 2@ (Gaussian-integer entries).
seededMPS222 :: Int -> MPS3 2 2
seededMPS222 seed = unGen genMPS222 (mkQCGen seed) 30

-- | ⟨y, Heff x⟩ (Hilbert–Schmidt, via the library inner product on the
-- centre's map space) equals the full network contraction
-- ⟨ψ_y|H|φ_x⟩ with the surrounding sites frozen.
prop_effectiveHMatchesInner :: QC.Property
prop_effectiveHMatchesInner =
  QC.forAll genMPS222 $ \psiY ->
  QC.forAll genMPS222 $ \psiX ->
  QC.forAll genMPO222 $ \mpo ->
    withMPS3 psiY $ \s1 y s3 ->
    withMPS3 psiX $ \_ x _ ->
    withMPO3 mpo $ \o1 o2 o3 ->
      let l1 = extendLeft leftBoundary s1 o1 s1
          r3 = extendRight @2 s3 o3 s3 rightBoundary
          heff = effectiveH @2 l1 o2 r3
          lhs = siteLin y <.> (heff $ siteLin x)
          rhs = mpsMPOInner (mps3 s1 y s3) mpo (mps3 s1 x s3)
      in lhs QC.=== rhs

-- | For a Hermitian MPO (TFIM) the effective Hamiltonian is Hermitian:
prop_effectiveHHermitian :: QC.Property
prop_effectiveHHermitian =
  QC.forAll genMPS222 $ \psiY ->
  QC.forAll genMPS222 $ \psiX ->
    withMPS3 psiY $ \s1 y s3 ->
    withMPS3 psiX $ \_ x _ ->
    withMPO3 (tfimMPO 1 0.7) $ \o1 o2 o3 ->
      let l1 = extendLeft leftBoundary s1 o1 s1
          r3 = extendRight @2 s3 o3 s3 rightBoundary
          heff = effectiveH @2 l1 o2 r3
          lhs = siteLin x <.> (heff $ siteLin y)
          rhs = conjugate (siteLin y <.> (heff $ siteLin x))
          scale = 1 + magnitude lhs + magnitude rhs
      in QC.counterexample (show lhs ++ " /≈ " ++ show rhs)
           (magnitude (lhs - rhs) <= 1e-9 * scale)

-- | Flattening the domain via @swapMap ∘ splitBond@ yields the same @(bl·p) × br@
prop_flatLeftSVDMatchesSiteMatrix :: QC.Property
prop_flatLeftSVDMatchesSiteMatrix =
  QC.forAll genMPS222 $ \mps ->
    withMPS3 mps $ \s122 s222 s221 ->
      extract (getLinearMap (siteForLeftSVD @1 @2 @2 (siteLin s122)))
        QC.=== siteMatrix @1 @2 @2 s122
        QC..&&. extract (getLinearMap (siteForLeftSVD @2 @2 @2 (siteLin s222)))
                QC.=== siteMatrix @2 @2 @2 s222
        QC..&&. extract (getLinearMap (siteForLeftSVD @2 @2 @1 (siteLin s221)))
                QC.=== siteMatrix @2 @2 @1 s221

-- | DMRG on the 3-site TFIM converges to the dense @C (p³)@ ground energy.
prop_dmrgGroundEnergyMatchesDense :: QC.Property
prop_dmrgGroundEnergyMatchesDense =
  QC.forAll (QC.choose (0, 99)) $ \seed ->
    let mpo = tfimMPO 1 0.7
        psi0 = seededMPS222 seed
        (e, psi) = dmrg 10 1e-12 mpo sweep psi0
        eDense = denseGroundEnergy mpo
        tol = 1e-9
    in QC.counterexample ("DMRG " ++ show e ++ " vs dense " ++ show eDense)
         (abs (e - eDense) <= tol QC..&&. energy mpo psi >= eDense - tol)


-- | On a 'HilbertSpace' (@C 4@), the 'eigen' path matches the dense oracle.
prop_eigenMatchesDenseC4 :: QC.Property
prop_eigenMatchesDenseC4 =
  let f = (2 :: Complex Double) *^ (linearId :: C 4 +> C 4)
      (eEigen, _) = groundStateEigen euclideanNorm f
      (eDense, _) = groundStateDense f
  in eEigen QC.=== eDense QC..&&. eEigen QC.=== 2

prop_mpsGetSite :: QC.Property
prop_mpsGetSite =
  QC.forAll genMPS222 $ \mps ->
    withMPS3 mps $ \s1 s2 s3 ->
      case (getSite 1 mps, getSite 2 mps, getSite 3 mps) of
        (SiteLeft a, SiteBulk b, SiteRight c) ->
          siteMapsEqual s1 a
          QC..&&. siteMapsEqual s2 b
          QC..&&. siteMapsEqual s3 c
        _ -> QC.property False

prop_mpsSetSiteRoundTrip :: QC.Property
prop_mpsSetSiteRoundTrip =
  QC.forAll genMPS222 $ \mps ->
    withMPS3 mps $ \s1 s2 s3 ->
      let mps' =
            setSite 1 (SiteLeft s1)
              (setSite 2 (SiteBulk s2) (setSite 3 (SiteRight s3) mps))
      in withMPS3 mps' $ \s1' s2' s3' ->
           siteMapsEqual s1 s1'
           QC..&&. siteMapsEqual s2 s2'
           QC..&&. siteMapsEqual s3 s3'

siteMapsEqual
  :: forall bl p br
   . ( KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br) )
  => Site bl p br -> Site bl p br -> QC.Property
siteMapsEqual (Site f) (Site g) =
  extract (getLinearMap f) QC.=== extract (getLinearMap g)
