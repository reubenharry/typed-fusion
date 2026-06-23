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
import Control.Arrow.Constrained (($), EnhancedCat (arr))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗)
  , TensorSpace (..), FiniteDimensional (..), SubBasis
  , sampleLinearFunction, contractTensorMap
  , LinearFunction, pattern LinearFunction, (-+$>)
  , getLinearMap, LinearMap (..), linearId, euclideanNorm
  , recomposeLinMap, entireBasis, constructEigenSystem, Eigenvector (..), type (-+>), finishEigenSystem )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static
  ( C, M, R, Sized (fromList, unwrap, create, extract), Domain (diagR), complex, mul )
import Numeric.LinearAlgebra.Static.MPSLayout (siteLinearMap)
import qualified Numeric.LinearAlgebra as HM
import GHC.TypeLits (KnownNat, type (*), Nat, type (-), type (+), natVal)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Maybe (fromMaybe)
import qualified Data.Vector.Sized as VS
import Data.Complex (Complex ((:+)), conjugate, realPart, magnitude)
import Data.VectorSpace (InnerSpace ((<.>)), VectorSpace ((*^)), AdditiveGroup (zeroV), sumV)

import TensorNetwork.MPS.Fixed3.Internal
  ( Site (..), MPS (..), OpSite (..), MPO (..), cdim, basis
  , MPS3, MPO3, mps3, mpo3, withMPS3, withMPO3, siteLin )
import TensorNetwork.MPS.Fixed3
  ( mpoTransferStep, opWire, mpsInner, mpsMPOInner, mpoToMatrix, mpsToFlat
  , genMPS222, genMPO222, genSite, pauliX, pauliZ )
import TensorNetwork.Categorical
  ( (⊗^), lunit, lunitInv, swapMap, splitBond, fuseBond )
import GroundState (groundState, groundStateDense, groundStateEigen, hilbertSchmidtNorm)
import TensorNetwork.DMRG.Chain
  ( ChainEnd
  , chainLength
  , siteInt, firstSite, advanceSite, retreatSite, isFirstSite, isLastSite
  , getSite, getOp, setSite, SomeSite (..), SomeOpSite (..) )
import Data.Finite (Finite)
import TensorNetwork.DMRG.Env
  ( LeftEnv, RightEnv, leftBoundary, rightBoundary, extendLeft, extendRight
  , MoveRightEnv (..), moveRightEnv'
  , MoveLeftEnv (..), moveLeftEnv'
  , LeftEnvAtCentre (..), RightEnvAtCentre (..)
  , buildRightEnvFromSite
  , updateEnvsMoveRight, updateEnvsMoveLeft )

import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import TensorNetwork.MPS.Fixed3.Reference (amplitude)
import Control.Monad (replicateM)
import Control.Monad.Identity (Identity, runIdentity)
import Control.Exception (SomeException, evaluate, try)
import Data.Ord (comparing)
import Data.List (sortBy)
import qualified Data.Vector.Storable as VSt
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

-- | Push a left-SVD bond factor onto the left bond of the site to the right:
-- left-multiply the @bl × (p·br)@ storage matrix.
absorbLeftBond
  :: forall p bl br
   . (KnownNat p, KnownNat bl, KnownNat br, KnownNat (p * br))
  => C bl +> C bl -> Site bl p br -> Site bl p br
absorbLeftBond (LinearMap fMat) (Site g) =
  Site (LinearMap (mul fMat (getLinearMap g)))
absorbLeftBond _ _ = error "absorbLeftBond: expected LinearMap bond factor"

-- | Left-orthonormalize a site (requires @bl·p ≥ br@): thin SVD
-- @M = U Σ V†@ of the @(bl·p) × br@ layout matrix; the site becomes @U@ and
-- the bond factor @U† M = Σ V†@ is returned for absorption into the right neighbour.
normalizeLeft
  :: forall bl p br.
     ( KnownNat bl, KnownNat p, KnownNat br
     , KnownNat (p * br), KnownNat (bl * p), KnownNat (p * bl), p * bl ~ bl * p )
  => Site bl p br -> (Site bl p br, C br +> C br)
normalizeLeft (Site f) =
  let mDyn = extract (getLinearMap (siteForLeftSVD f))
      (uDyn, _s, _v) = HM.thinSVD mDyn
      u = fromMaybe (error "normalizeLeft: u") $ create uDyn
      bondDyn = adjointMat uDyn HM.<> mDyn
      bond = fromMaybe (error "normalizeLeft: bond") $ create bondDyn
  in ( Site (siteFromLeftSVD (LinearMap u))
     , LinearMap bond
     )

-- | Conjugate transpose of a dense matrix (for bond extraction @U† M@).
adjointMat :: HM.Matrix (Complex Double) -> HM.Matrix (Complex Double)
adjointMat m =
  let rows = HM.toLists m
      (nRows, nCols) = HM.size m
  in HM.fromLists
       [ [ conjugate (rows !! j !! i) | j <- [0 .. nRows - 1] ]
       | i <- [0 .. nCols - 1]
       ]

-- | Right-orthonormalize a site (requires @bl ≤ p·br@): thin SVD
-- @M = U Σ V†@ of the @bl × (p·br)@ storage matrix; the site becomes
-- @V†@ and the residual bond factor @M V = U Σ@ is returned, to be
-- absorbed into the left neighbour on the outgoing bond.
normalizeRight
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br))
  => Site bl p br -> (C bl +> C bl, Site bl p br)
normalizeRight (Site f) =
  let mDyn = extract (getLinearMap f)
      (uDyn, _s, vDyn) = HM.thinSVD mDyn
      vh = fromMaybe (error "normalizeRight: vh") $ create (HM.tr vDyn)
      bondDyn = mDyn HM.<> vDyn
      bond = fromMaybe (error "normalizeRight: bond") $ create bondDyn
  in (LinearMap bond, siteFromStorage @bl @p @br vh)

-- | Push a right-SVD bond factor onto the output bond of a left-end site.
absorbRightBondLeftEnd
  :: forall p b. (KnownNat p, KnownNat b, KnownNat (p * b))
  => C b +> C b -> Site 1 p b -> Site 1 p b
absorbRightBondLeftEnd f (Site g) = Site (f . g)

-- | Push a right-SVD bond factor onto the right bond of a bulk site:
-- post-compose on the outgoing bond, @g' = f ∘ g@.
absorbRightBond
  :: forall p bl br. (KnownNat p, KnownNat bl, KnownNat br, KnownNat (p * br))
  => C br +> C br -> Site bl p br -> Site bl p br
absorbRightBond f (Site g) = Site (f . g)

-- | Left-canonicalize site @i@ and absorb the bond factor into site @i+1@.
regaugeDepartRight
  :: forall p b l
   . ( KnownNat l, KnownNat p, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  => Int -> MPS p b l -> (SomeSite p b, MPS p b l)
regaugeDepartRight i mps =
  case (getSite i mps, getSite (i + 1) mps) of
    (SiteLeft s, SiteBulk n) ->
      let (sc, bond) = normalizeLeft s
          n' = absorbLeftBond bond n
      in ( SiteLeft sc
         , setSite (i + 1) (SiteBulk n') (setSite i (SiteLeft sc) mps)
         )
    (SiteBulk s, SiteBulk n) ->
      let (sc, bond) = normalizeLeft s
          n' = absorbLeftBond bond n
      in ( SiteBulk sc
         , setSite (i + 1) (SiteBulk n') (setSite i (SiteBulk sc) mps)
         )
    (SiteBulk s, SiteRight n) ->
      let (sc, bond) = normalizeLeft s
          n' = absorbLeftBond bond n
      in ( SiteBulk sc
         , setSite (i + 1) (SiteRight n') (setSite i (SiteBulk sc) mps)
         )
    _ ->
      error ("regaugeDepartRight: unexpected site pair at " ++ show i)

-- | Right-canonicalize site @i@ and absorb the bond factor into site @i-1@.
regaugeDepartLeft
  :: forall p b l
   . ( KnownNat l, KnownNat p, KnownNat b, KnownNat (p * b) )
  => Int -> MPS p b l -> (SomeSite p b, MPS p b l)
regaugeDepartLeft i mps =
  case (getSite (i - 1) mps, getSite i mps) of
    (SiteLeft prev, SiteBulk s) ->
      let (bond, sc) = normalizeRight s
          prev' = absorbRightBondLeftEnd bond prev
      in ( SiteBulk sc
         , setSite (i - 1) (SiteLeft prev') (setSite i (SiteBulk sc) mps)
         )
    (SiteBulk prev, SiteBulk s) ->
      let (bond, sc) = normalizeRight s
          prev' = absorbRightBond bond prev
      in ( SiteBulk sc
         , setSite (i - 1) (SiteBulk prev') (setSite i (SiteBulk sc) mps)
         )
    (SiteBulk prev, SiteRight s) ->
      let (bond, sc) = normalizeRight s
          prev' = absorbRightBond bond prev
      in ( SiteRight sc
         , setSite (i - 1) (SiteBulk prev') (setSite i (SiteRight sc) mps)
         )
    _ ->
      error ("regaugeDepartLeft: unexpected site pair at " ++ show i)

--------------------------------------------------------------------------------
-- Sweeping
--------------------------------------------------------------------------------

-- | Rayleigh quotient @Re ⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩@ (gauge-independent).
energy
  :: (KnownNat l, KnownNat p, KnownNat w, KnownNat b )
  => MPO p w l -> MPS p b l -> Double
energy mpo psi = realPart (mpsMPOInner psi mpo psi / mpsInner psi psi)

--------------------------------------------------------------------------------
-- Zipper ('MPS' + value-level centre index)
--------------------------------------------------------------------------------

-- | DMRG workspace: full chain, active site cursor, environments.
--
-- 'centreIndex' is 0-based ('Data.Finite'); use 'siteInt' for 1-based 'getSite'.
data MPSZipper p b w l = MPSZipper
  { theMPO :: MPO p w l
  , theMPS :: MPS p b l
  , centreIndex :: Finite (ChainEnd l)
  , leftEnv :: LeftEnvAtCentre w b
  , rightEnv :: RightEnvAtCentre w b
  }

-- | Right-orthonormalize sites @n .. 2@, absorbing bond factors leftwards.
rightGaugeMPS
  :: forall p b l
   . ( KnownNat l, KnownNat p, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  => MPS p b l -> MPS p b l
rightGaugeMPS mps0 =
  case go (chainLength @l) Cat.id mps0 of
    (bondOut, mpsAcc) ->
      case getSite 1 mpsAcc of
        SiteLeft s1 ->
          setSite 1 (SiteLeft (absorbRightBondLeftEnd bondOut s1)) mpsAcc
        _ -> error "rightGaugeMPS: expected left-end site"
  where
    n = chainLength @l
    go k bondIn mpsAcc
      | k <= 1 = (bondIn, mpsAcc)
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
  let sys = (effectiveH @p l op r)
      (e, c) = groundState sys
  in (e, Site c)


solveCentreSite'
  :: forall p wl wr bl br
   . ( KnownNat p, KnownNat wl, KnownNat wr, KnownNat bl, KnownNat br )
  => LeftEnv wl bl bl
  -> OpSite wl p wr
  -> RightEnv wr br br
  -> Site bl p br
  -> (Double, Site bl p br)
solveCentreSite' l op r (Site _) =
  let sys = arr (effectiveH @p l op r) :: Centre bl p br -+> Centre bl p br
      (e, c) = groundStateEigen hilbertSchmidtNorm sys
  in (e, Site c)

solveSiteAt
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b )
  => Finite (ChainEnd l)
  -> LeftEnvAtCentre w b
  -> SomeOpSite p w
  -> RightEnvAtCentre w b
  -> SomeSite p b
  -> SomeSite p b
solveSiteAt c l op r cn =
  let i = siteInt c
      n = chainLength @l
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
  => Finite (ChainEnd l)
  -> LeftEnvAtCentre w b
  -> SomeOpSite p w
  -> RightEnvAtCentre w b
  -> Double
centreEnergyAt c l op r =
  let i = siteInt c
      n = chainLength @l
  in case (i, l, op, r) of
       (1, LeftEnvFirst lv, OpLeft o, RightEnvBulk rv) ->
         fst (groundState (effectiveH @p lv o rv))
       (j, LeftEnvBulk lv, OpBulk o, RightEnvBulk rv) | j > 1 && j < n ->
         fst (groundState (effectiveH @p lv o rv))
       (n, LeftEnvBulk lv, OpRight o, RightEnvLast rv) ->
         fst (groundState (effectiveH @p lv o rv))
       _ ->
         error ("centreEnergyAt: site/op/env shape mismatch at index " ++ show i)

moveRight
  :: forall p w b l
   . ( KnownNat l, KnownNat (ChainEnd l), KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  => MPSZipper p b w l -> MPSZipper p b w l
moveRight z@MPSZipper{centreIndex = c, theMPS = mps, theMPO = mpo, leftEnv = l, rightEnv = r}
  | isLastSite @l c =
      error ("moveRight: centre " ++ show (siteInt c) ++ " at right boundary")
  | otherwise =
    let i = siteInt c
        c' = fromMaybe (error "moveRight: advanceSite failed") (advanceSite c)
        (cn, mps') = regaugeDepartRight i mps
        (l', r') = updateEnvsMoveRight i (moveRightEnv' @l i) mpo mps' (l,r) cn (getOp i mpo)
    in z { centreIndex = c', theMPS = mps', leftEnv = l', rightEnv = r' }

moveLeft
  :: forall p w b l
   . ( KnownNat l, KnownNat (ChainEnd l), KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  => MPSZipper p b w l -> MPSZipper p b w l
moveLeft z@MPSZipper{centreIndex = c, theMPS = mps, theMPO = mpo, rightEnv = r}
  | isFirstSite c =
      error ("moveLeft: centre " ++ show (siteInt c) ++ " at left boundary")
  | otherwise =
    let i = siteInt c
        c' = fromMaybe (error "moveLeft: retreatSite failed") (retreatSite c)
        wit = moveLeftEnv' i
        (cn, mps') = regaugeDepartLeft i mps
        (l', r') =
          updateEnvsMoveLeft @p @w @b @l
            i wit mpo mps' r cn (getOp i mpo)
    in z { centreIndex = c', theMPS = mps', leftEnv = l', rightEnv = r' }

toZipper
  :: forall p w b l
   . ( KnownNat l, KnownNat (ChainEnd l), KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  => MPO p w l -> MPS p b l -> MPSZipper p b w l
toZipper mpo mps =
  let mps' = rightGaugeMPS mps
      rEnv = buildRightEnvFromSite 2 mpo mps'
  in MPSZipper mpo mps' (firstSite @l) (LeftEnvFirst leftBoundary) (RightEnvBulk rEnv)



solveCenterAt
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b )
  => MPSZipper p b w l -> MPSZipper p b w l
solveCenterAt z@MPSZipper{centreIndex = c, theMPS = mps, theMPO = mpo, leftEnv = l, rightEnv = r} =
  let i = siteInt c
      solved = solveSiteAt @p @w @b @l c l (getOp i mpo) r (getSite i mps)
  in z { theMPS = setSite i solved mps }

centreEnergy
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b )
  => MPSZipper p b w l -> Double
centreEnergy MPSZipper{centreIndex = c, theMPO = mpo, leftEnv = l, rightEnv = r} =
  let i = siteInt c
  in centreEnergyAt @p @w @b @l c l (getOp i mpo) r

type ZipperStep p b w l = MPSZipper p b w l -> MPSZipper p b w l

-- | One left→right pass (solve at each site), then a partial left pass
-- stopping at site @2@. Returns the local energy at the final centre.
sweep
  :: forall p w b l m
   . ( KnownNat l, KnownNat (ChainEnd l), KnownNat p, KnownNat w, KnownNat b, Monad m
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p )
  =>
  ZipperStep p b w l
  -> MPO p w l
  -> MPS p b l
  -> m (Double, MPS p b l)
sweep step mpo  mps0 =
  let z0 = toZipper mpo mps0
      n = chainLength @l
      zRight = (iterate (step . moveRight) (step z0) !! (n - 1))
      zFinal = (iterate (step . moveLeft) zRight !! (n - 2))
  in pure (centreEnergy zFinal, theMPS zFinal)


-- | DMRG driver. Records the local centre energy returned by each sweep in
-- 'dmrgSweepEnergies' (sweep @1@ is the first entry). Use 'energy' on
-- 'dmrgFinalMPS' for the full Rayleigh quotient when needed.
dmrg
  :: forall p w b m l.
    (Monad m, KnownNat p, KnownNat w, KnownNat b, KnownNat l
     , KnownNat (p * b), KnownNat (b * p)
     , p * b ~ b * p )
  => Int -> Double -> MPO p w l -> SweepFunction m p w b l -> MPS p b l -> m (DmrgResult p b l)
dmrg maxSweeps tol mpo sweepFunction = go maxSweeps [] Nothing
  where
    finish e psi hist =
      DmrgResult
        { dmrgFinalEnergy = e
        , dmrgFinalMPS = psi
        , dmrgSweepEnergies = reverse hist
        }
    go 0 hist mE psi =
      let e = fromMaybe (energy mpo psi) mE
      in pure (finish e psi hist)
    go k hist mE psi = do
      (e, psi') <- sweepFunction mpo psi
      let hist' = e : hist
      case mE of
        Just ePrev | abs (e - ePrev) < tol -> pure (finish e psi' hist')
        _ -> go (k - 1) hist' (Just e) psi'


type SweepFunction m p w b l = MPO p w l -> MPS p b l -> m (Double, MPS p b l)

-- | Result of a 'dmrg' run, including the centre energy after each sweep.
data DmrgResult p b l = DmrgResult
  { dmrgFinalEnergy :: !Double
  , dmrgFinalMPS :: !(MPS p b l)
  , dmrgSweepEnergies :: ![Double]
  }


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

-- | Bulk TFIM MPO site (bond dimension @3@, physical @2@).
tfimBulkOp :: Double -> Double -> OpSite 3 2 3
tfimBulkOp j h =
  let jc = (-j) :+ 0
      hc = (-h) :+ 0
      idP = Cat.id :: C 2 +> C 2
  in OpSite $ sumV
       [ unitMap @3 @3 0 0 ⊗^ idP
       , unitMap @3 @3 1 0 ⊗^ pauliZ
       , unitMap @3 @3 2 0 ⊗^ (hc *^ pauliX)
       , unitMap @3 @3 2 1 ⊗^ (jc *^ pauliZ)
       , unitMap @3 @3 2 2 ⊗^ idP
       ]

-- | Left boundary TFIM MPO site.
tfimLeftOp :: Double -> Double -> OpSite 1 2 3
tfimLeftOp j h =
  let jc = (-j) :+ 0
      hc = (-h) :+ 0
      idP = Cat.id :: C 2 +> C 2
  in OpSite $ sumV
       [ unitMap @1 @3 0 0 ⊗^ (hc *^ pauliX)
       , unitMap @1 @3 0 1 ⊗^ (jc *^ pauliZ)
       , unitMap @1 @3 0 2 ⊗^ idP
       ]

-- | Right boundary TFIM MPO site.
tfimRightOp :: Double -> Double -> OpSite 3 2 1
tfimRightOp _j h =
  let hc = (-h) :+ 0
      idP = Cat.id :: C 2 +> C 2
  in OpSite $ sumV
       [ unitMap @3 @1 0 0 ⊗^ idP
       , unitMap @3 @1 1 0 ⊗^ pauliZ
       , unitMap @3 @1 2 0 ⊗^ (hc *^ pauliX)
       ]

-- | Transverse-field Ising on @l + 2@ sites, open boundaries:
--
--   @H = -J Σᵢ σᶻᵢσᶻᵢ₊₁ - h Σᵢ σˣᵢ@
--
-- as the standard bond-dimension-3 MPO
--
--   @W = [[1, 0, 0], [σᶻ, 0, 0], [-h·σˣ, -J·σᶻ, 1]]@
--
-- with the left boundary picking row 2 and the right boundary column 0.
tfimMPOChain
  :: forall l. KnownNat l
  => Double -> Double -> MPO 2 3 l
tfimMPOChain j h =
  MPO (tfimLeftOp j h) bulkOps (tfimRightOp j h)
  where
    bulkOps =
      fromMaybe (error "tfimMPOChain: bulk vector length mismatch") $
        VS.fromList (replicate (fromIntegral (natVal (Proxy @l))) (tfimBulkOp j h))

-- | Three-site TFIM (@l = 1@).
tfimMPO :: Double -> Double -> MPO3 2 3
tfimMPO = tfimMPOChain @1


-- | Deterministic pseudo-random MPS with @l@ bulk sites.
seededMPSChain
  :: forall p b l. (KnownNat p, KnownNat b, KnownNat l)
  => Int -> MPS p b l
seededMPSChain seed = unGen genMPSChain (mkQCGen seed) 30

-- | Random open-boundary MPS with @l@ bulk sites.
genMPSChain
  :: forall p b l. (KnownNat p, KnownNat b, KnownNat l)
  => QC.Gen (MPS p b l)
genMPSChain = do
  lSite <- genSite @1 @p @b
  bulk <- replicateM (fromIntegral (natVal (Proxy @l))) (genSite @b @p @b)
  rSite <- genSite @b @p @1
  pure $
    MPS lSite
      (fromMaybe (error "genMPSChain: bulk vector length mismatch") (VS.fromList bulk))
      rSite

--------------------------------------------------------------------------------
-- Validation helpers and properties
--------------------------------------------------------------------------------

-- | MPS site with bond dimension 1 selecting a single physical index.
deltaSite
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br)
  => Int -> Site bl p br
deltaSite s =
  Site $
    fst (recomposeLinMap (entireBasis :: SubBasis (C bl ⊗ C p))
           [ if lb == 0 && t == s then basis @br 0 else zeroV
           | lb <- [0 .. cdim @bl - 1]
           , t <- [0 .. cdim @p - 1]
           ])

-- | Product state @|s₁…sₙ⟩@ as a bond-dimension-1 MPS (@n = l + 2@).
productStateMPS
  :: forall p l. (KnownNat p, KnownNat l)
  => [Int] -> MPS p 1 l
productStateMPS indices
  | length indices /= nSites =
      error "productStateMPS: index count does not match chain length"
  | otherwise =
      MPS (deltaSite @1 @p @1 (head indices))
          (fromMaybe (error "productStateMPS: bulk vector length mismatch") $
             VS.fromList [deltaSite @1 @p @1 i | i <- bulkIndices])
          (deltaSite @1 @p @1 (last indices))
  where
    nSites = chainLength @l
    bulkIndices = take (nSites - 2) (drop 1 indices)

-- | Exact ground energy via dense diagonalisation on the physical Hilbert
-- space @C (pⁿ)@ (@n = l + 2@). For @l = 1@ this matches 'mpoToMatrix'.
denseGroundEnergyChain
  :: forall p w l
   . ( KnownNat p, KnownNat w, KnownNat l )
  => MPO p w l -> Double
denseGroundEnergyChain mpo =
  let pDim = cdim @p
      configs = physicalConfigs pDim (chainLength @l)
      psi cfg = productStateMPS @p @l cfg
      matrixElem bra ket = realPart (mpsMPOInner (psi bra) mpo (psi ket))
      matrix = HM.fromLists
        [ [ matrixElem bra ket | ket <- configs ] | bra <- configs ]
      (vals, _) = HM.eigSH (HM.sym matrix)
  in HM.minElement vals

physicalConfigs :: Int -> Int -> [[Int]]
physicalConfigs pDim nSites = sequence (replicate nSites [0 .. pDim - 1])

-- | Three-site specialization of 'denseGroundEnergyChain'.
denseGroundEnergy
  :: forall p w.
     ( KnownNat p, KnownNat w, KnownNat (w * p)
     , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p)
     , KnownNat (p * p), KnownNat (p * p), KnownNat (p * 1)
     , KnownNat (p * p), p * p ~ p * p )
  => MPO p w 1 -> Double
denseGroundEnergy = denseGroundEnergyChain

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
        DmrgResult { dmrgFinalEnergy = e, dmrgFinalMPS = psi } =
          runIdentity $ dmrg 10 1e-12 mpo (sweep solveCenterAt) psi0
        eDense = denseGroundEnergy mpo
        tol = 1e-9
    in QC.counterexample ("DMRG " ++ show e ++ " vs dense " ++ show eDense)
         (abs (e - eDense) <= tol QC..&&. energy mpo psi >= eDense - tol)


-- | On a 'HilbertSpace' (@C 4@), the Krylov path matches the dense oracle.
prop_eigenMatchesDenseC4 :: QC.Property
prop_eigenMatchesDenseC4 =
  let f = (2 :: Complex Double) *^ (linearId :: C 4 +> C 4)
      (eEigen, _) = groundStateEigen euclideanNorm (arr f)
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

-- | @M ≈ U F@ in the 'siteForLeftSVD' layout after 'normalizeLeft'.
prop_leftSvdDecomposition :: QC.Property
prop_leftSvdDecomposition =
  QC.forAll genMPS222 $ \mps ->
    withMPS3 mps $ \s1 _ _ ->
      let mat = getLinearMap (siteForLeftSVD @1 @2 @2 (siteLin s1))
          m0 = extract mat
          (s1c, bond) = normalizeLeft s1
          u = extract (getLinearMap (siteForLeftSVD @1 @2 @2 (siteLin s1c)))
          f = extract (getLinearMap bond)
          tol = 1e-9
      in QC.counterexample "site 1 M ≈ U F"
           (matrixNear tol m0 (u HM.<> f))

matrixNear :: Double -> HM.Matrix (Complex Double) -> HM.Matrix (Complex Double) -> QC.Property
matrixNear tol a b =
  QC.property $
    matrixMaxAbs (a - b) <= tol * (1 + matrixMaxAbs a + matrixMaxAbs b)

matrixMaxAbs :: HM.Matrix (Complex Double) -> Double
matrixMaxAbs m = maximum (0 : [ magnitude x | x <- concat (HM.toLists m) ])

-- | Left-canonicalizing site @i@ and absorbing the bond factor into site @i+1@
-- must preserve all physical amplitudes.
-- | Left-canonicalizing site @i@ and absorbing the bond factor into site @i+1@
-- must preserve all physical amplitudes.
prop_regaugeDepartRightPreservesAmplitudes :: QC.Property
prop_regaugeDepartRightPreservesAmplitudes =
  QC.forAll genMPS222 $ \mps ->
    withMPS3 mps $ \_ _ _ ->
      let (_, mps') = regaugeDepartRight 1 mps
      in QC.conjoin
           [ QC.counterexample ("amp " ++ show (a, b, c))
               (ampApproxEq (amplitude mps a b c) (amplitude mps' a b c))
           | a <- [0, 1], b <- [0, 1], c <- [0, 1]
           ]

ampApproxEq :: Complex Double -> Complex Double -> QC.Property
ampApproxEq x y =
  QC.property $ magnitude (x - y) <= 1e-9 * (1 + magnitude x + magnitude y)

-- | Left-canonicalizing site @i@ and absorbing the bond factor into site @i+1@
-- must preserve the flattened physical vector.
prop_regaugeDepartRightPreservesMPS :: QC.Property
prop_regaugeDepartRightPreservesMPS =
  QC.forAll genMPS222 $ \mps ->
    withMPS3 mps $ \_s1 _s2 _s3 ->
      let flat0 = mpsToFlat mps
          (_, mps1) = regaugeDepartRight 1 mps
          (_, mps2) = regaugeDepartRight 2 mps1
      in QC.conjoin
           [ QC.counterexample "site 1 → 2" (flatApproxEq @8 1e-9 flat0 (mpsToFlat mps1))
           , QC.counterexample "site 2 → 3" (flatApproxEq @8 1e-9 flat0 (mpsToFlat mps2))
           ]

-- | Right-canonicalizing site @i@ and absorbing into site @i-1@ preserves @ψ@.
prop_regaugeDepartLeftPreservesMPS :: QC.Property
prop_regaugeDepartLeftPreservesMPS =
  QC.forAll genMPS222 $ \mps ->
    withMPS3 mps $ \_s1 _s2 _s3 ->
      let (_, mps1) = regaugeDepartRight 1 mps
          (_, mps2) = regaugeDepartRight 2 mps1
          flat0 = mpsToFlat mps2
          (_, mps3) = regaugeDepartLeft 3 mps2
          (_, mps4) = regaugeDepartLeft 2 mps3
      in QC.conjoin
           [ QC.counterexample "site 3 → 2" (flatApproxEq @8 1e-9 flat0 (mpsToFlat mps3))
           , QC.counterexample "site 2 → 1" (flatApproxEq @8 1e-9 flat0 (mpsToFlat mps4))
           ]

-- | 'moveRight' / 'moveLeft' on a zipper must not change the physical state.
prop_moveRightLeftPreservesMPS :: QC.Property
prop_moveRightLeftPreservesMPS =
  QC.forAll genMPS222 $ \mps ->
    let mpo = tfimMPO 1 0.7
        flat0 = mpsToFlat (theMPS (toZipper mpo mps))
        zRight =
          moveRight . moveRight $ toZipper mpo mps
        zBack =
          moveLeft . moveLeft $ zRight
    in QC.conjoin
         [ QC.counterexample "moveRight × 2"
             (flatApproxEq @8 1e-9 flat0 (mpsToFlat (theMPS zRight)))
         , QC.counterexample "moveRight then moveLeft"
             (flatApproxEq @8 1e-9 flat0 (mpsToFlat (theMPS zBack)))
         ]

flatApproxEq
  :: forall n. KnownNat n
  => Double -> C n -> C n -> Bool
flatApproxEq tol a b =
  VSt.all (\d -> magnitude d <= tol) (VSt.zipWith (-) (unwrap a) (unwrap b))

siteMapsEqual
  :: forall bl p br
   . ( KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br) )
  => Site bl p br -> Site bl p br -> QC.Property
siteMapsEqual (Site f) (Site g) =
  extract (getLinearMap f) QC.=== extract (getLinearMap g)

-- | Compare dense and Krylov ground-state solves on network effective Hamiltonians.
smokeNetworkEffectiveHamiltonian :: IO ()
smokeNetworkEffectiveHamiltonian = do
  putStrLn "=== TFIM centre effective Hamiltonian (seed 42) ==="
  withMPS3 (seededMPS222 42) $ \s1 _y s3 ->
    withMPO3 (tfimMPO 1 0.7) $ \o1 o2 o3 ->
      reportEffectiveH "Centre site 2:"
        (effectiveH @2 (extendLeft leftBoundary s1 o1 s1) o2
           (extendRight @2 s3 o3 s3 rightBoundary))

  putStrLn ""
  putStrLn "=== Random MPS/MPO effective Hamiltonian (QC seed 7) ==="
  let psi = unGen genMPS222 (mkQCGen 7) 30
      mpo = unGen genMPO222 (mkQCGen 7) 30
  withMPS3 psi $ \s1 _y s3 ->
    withMPO3 mpo $ \o1 o2 o3 ->
      reportEffectiveH "Centre site 2:"
        (effectiveH @2 (extendLeft leftBoundary s1 o1 s1) o2
           (extendRight @2 s3 o3 s3 rightBoundary))
  where
    reportEffectiveH label heff = do
      let (eDense, _) = groundStateDense heff
      putStrLn label
      putStrLn $ "  dense eigenvalue = " ++ show eDense
      eigenOutcome <- try (evaluate (fst (groundStateEigen hilbertSchmidtNorm (arr heff))))
      case eigenOutcome of
        Left (ex :: SomeException) ->
          putStrLn $ "  constructEigen CRASHED = " ++ show ex
        Right eEigen -> do
          let diff = abs (eDense - eEigen)
          putStrLn $ "  constructEigen eigen = " ++ show eEigen
          putStrLn $ "  |dense - krylov|     = " ++ show diff
          if diff <= 1e-8
            then putStrLn "  OK (within 1e-8)"
            else putStrLn "  MISMATCH — possible Krylov / norm bug"