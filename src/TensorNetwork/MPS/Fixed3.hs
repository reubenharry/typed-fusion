{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{- HLINT ignore "Move brackets to avoid $" -}

-- | A finite, typed-bond, three-site matrix product state.
--
-- Design (see ROADMAP §4a — settled):
--
--   * __Site orientation: transfer / contraction.__ Each site is a linear map
--     taking @incoming-bond ⊗ physical@ to @outgoing-bond@. The boundary bonds
--     are the monoidal unit @C 1@. Bonds are typed (@KnownNat@), so a
--     bond-dimension mismatch between adjacent sites is a type error.
--
--   * __Morphism-level production path.__ Every contraction below is built
--     from composition, monoidal products of maps ('⊗^'), associators,
--     braiding, unitors, bond fusion and 'dagger' — no coefficient loops, no
--     matrix reshaping. The explicit basis sums live only in
--     "TensorNetwork.MPS.Fixed3.Reference" as QuickCheck oracles.
--
--   * __MPO sites are stored in transfer orientation__ (domain physical =
--     bra-side index, codomain physical = ket-side index); see
--     'TensorNetwork.MPS.Fixed3.Internal.OpSite'.
module TensorNetwork.MPS.Fixed3 where

import Prelude hiding (id, ($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained (id, (.))
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗), Tensor (..)
  , FiniteDimensional (..), SubBasis
  , getLinearMap
  , trace, (-+$>), LinearMap (..)
  , sampleLinearFunction, LinearFunction, pattern LinearFunction )
import Math.LinearMap.Category.Instances.Deriving ()
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import TensorNetwork.MPS.Fixed3.Internal
  ( Site (..), MPS (..), OpSite (..), MPO (..), one1, cdim, basis
  , MPS3, MPO3, mps3, mpo3, withMPS3, withMPO3 )
import TensorNetwork.MPS.Fixed3.Reference
  ( applySite, applyOpSite, siteCoeff, opSiteCoeff, envCoeff, env3Coeff
  , matrixTransferCoeff, matrixMPOTransferCoeff
  , mpsInnerReference, mpsToFlatReference, mpsMPOInnerReference )
import qualified TensorNetwork.MPS.Fixed3.Reference as Ref
import GroundState (toDenseMatrix)
import TensorNetwork.Categorical
  ( (⊗^), swapMap, lassocMap, rassocMap, lunit, lunitInv
  , fuseBond, splitBond, conjugateMap )
import TensorNetwork.Dagger (dagger, transposeMap)
-- Orphan instances making @C n@ (and tensors over it) linearmap-category spaces.
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static
  ( C, M, R, Sized (..)
  , Domain (diagR, mul), complex, extract )
import Numeric.LinearAlgebra.Static.MPSLayout (siteLinearMap)
import qualified Numeric.LinearAlgebra.HMatrix as HM
import GHC.TypeLits (KnownNat, type (*))
import Data.Complex (Complex ((:+)), conjugate, realPart, imagPart, magnitude)
import Data.Maybe (fromMaybe)
import Data.VectorSpace (InnerSpace ((<.>)), VectorSpace ((*^)), sumV)
import Control.Monad (replicateM)
import qualified Data.Vector.Storable as VS
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)



-- | The physical state in @C p ⊗ (C p ⊗ C p)@: transpose the chain morphism
-- (turning the functional into a vector, no conjugation), close the boundary
-- with the left unitor, reassociate, and apply to @1 ∈ C 1@.
mpsToTensor
  :: forall p b.
     ( KnownNat p, KnownNat b )
  => MPS3 p b -> C p ⊗ (C p ⊗ C p)
mpsToTensor mps =
  ( rassocMap
      . ((lunit ⊗^ idC @p) ⊗^ idC @p)
      . transposeMap (mpsChainMap mps) )
    $ konst 1


-- | Encode a physical tensor as an MPS via two-step TT-SVD on morphisms.
--
--   1. View tensor as @C p +> (C p ⊗ C p)@, SVD → left site + residual.
--   2. Reshape residual to @C (b₁·p) +> C p@, SVD → center + right sites.
--
-- Exact round-trip with 'mpsToTensor' / 'mpsToFlat' when bond dimensions are
-- large enough (@b₁, b₂ ≥ p@ suffices for generic @p@-dimensional legs).
mpsFromPhysical
  :: forall p b
   . ( KnownNat p, KnownNat b
     , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p)
     , KnownNat (p * b), KnownNat (p * b), KnownNat (p * 1)
     , KnownNat (b * p), p * b ~ b * p )
  => Physical3 p -> MPS3 p b
mpsFromPhysical tensor =
  let (leftFactor, rest) = svdSplitTensor @p @p @p @b ((LinearMap . getTensorProduct) tensor)
      (centerFactor, rightFactor) =
        svdSplit @(b * p) @p @b (restForSecondCut @p @b rest)
  in mps3
       (leftSiteFromFactor leftFactor)
       (Site (siteFromLeftSVD @b centerFactor))
       (rightSiteFromFactor rightFactor)



-- | The MPS inner product ⟨ψ|φ⟩: three transfer steps from the identity
-- boundary environment, closed with the trace on @C 1 +> C 1@.
mpsInner
  :: forall p a.
     ( KnownNat p, KnownNat a )
  => MPS3 p a -> MPS3 p a -> Complex Double
mpsInner mps1 mps2 =
  withMPS3 mps1 $ \lB cB rB ->
  withMPS3 mps2 $ \lK cK rK ->
    trace -+$>
      ( transferStep @p rB rK $
          transferStep @p cB cK $
            transferStep @p lB lK Cat.id )













instance (KnownNat bl, KnownNat p, KnownNat br) => Show (Site bl p br) where
  show _ = "Site"

instance Show (MPS p b l) where
  show _ = "MPS"

instance Show (MPO p w l) where
  show _ = "MPO"

instance (KnownNat wl, KnownNat p, KnownNat wr) => Show (OpSite wl p wr) where
  show _ = "OpSite"

-- | Identity on @C n@ (morphism-level; @id @(C n)@ is ill-kinded).
idC :: forall n. KnownNat n => C n +> C n
idC = id


-- | Diagonal map @x ↦ (diag σ) x@ on @C n@.
diagMap
  :: forall n. KnownNat n
  => R n -> C n +> C n
diagMap sigma = LinearMap (diagR 0 (complex sigma) :: M n n)

-- | Pauli @σˣ@ and @σᶻ@ in the canonical @C 2@ (computational) basis.
-- Both are symmetric, so the MPO transfer transpose is @id@.
-- Data entry on a finite space always fixes a basis; the production
-- contraction path does not enumerate one.
pauliX, pauliZ :: C 2 +> C 2
pauliX = LinearMap $
  createOrFail (HM.fromLists [[0 :+ 0, 1 :+ 0], [1 :+ 0, 0 :+ 0]])
pauliZ = diagMap @2 $ createOrFail (HM.fromList [1, -1])

-- | Left SVD bond transport @Σ Vᵀ@ as composition of maps on @C n@.
leftSvdFactor
  :: forall n. KnownNat n
  => R n -> M n n -> C n +> C n
leftSvdFactor sigma v = diagMap sigma . transposeMap (LinearMap v)

-- | Right SVD bond transport @U Σ@ as composition of maps on @C n@.
rightSvdFactor
  :: forall n. KnownNat n
  => M n n -> R n -> C n +> C n
rightSvdFactor u sigma = LinearMap u . diagMap sigma


-- | Unwrap a dynamic hmatrix value as a static matrix (or fail).
createOrFail :: Sized t s d => d t -> s
createOrFail x = fromMaybe (error "createOrFail") (create x)


--------------------------------------------------------------------------------
-- Map to physical space
--------------------------------------------------------------------------------

-- | The whole chain as one morphism eating the boundary bond and all three
-- physical legs: @(((C 1 ⊗ p) ⊗ p) ⊗ p) +> C 1@. Pure composition.
mpsChainMap
  :: forall p b.
     ( KnownNat p, KnownNat b )
  => MPS3 p b -> ((((C 1 ⊗ C p) ⊗ C p) ⊗ C p) +> C 1)
mpsChainMap mps =
  withMPS3 mps $ \(Site l) (Site c) (Site r) ->
    r . ((c . (l ⊗^ idC @p)) ⊗^ idC @p)



-- | Flattened physical state @C (p³)@ in the canonical 'toArray'
-- (co-lexicographic) order — the same order
-- 'TensorNetwork.Categorical.fuseBond' realises, and the order used by the
-- flat oracles in "TensorNetwork.MPS.Fixed3.Reference".
mpsToFlat
  :: forall p b.
     ( KnownNat p, KnownNat b
     , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p) )
  => MPS3 p b -> C (p * p * p)
mpsToFlat mps =
  unsafeFromArray (toArray (mpsToTensor mps) :: VS.Vector (Complex Double))

--------------------------------------------------------------------------------
-- Physical space ↔ MPS (SVD / TT decomposition)
--
-- Flat index @(s₁,s₂,s₃) ↦ s₁ + p·s₂ + p²·s₃@ matches 'mpsToFlat' /
-- 'flatIndex3'. The first SVD matricization is @M[s₁, s₂ + p·s₃]@.
--------------------------------------------------------------------------------

-- | Three-site physical Hilbert space, right-nested to match 'mpsToTensor':
-- @C p ⊗ (C p ⊗ C p)@.
type Physical3 p = C p ⊗ (C p ⊗ C p)



-- | Thin SVD with bond truncation/padding to a typed width @b@.
--
-- Returns @U@ (@M m b@), singular values (@R b@), and @Vᵀ@ (@M b n@) with
-- @M ≈ U · diag s · Vᵀ@.  Dynamic 'extract' only at the LAPACK boundary.
svdCut
  :: forall m n b. (KnownNat m, KnownNat n, KnownNat b)
  => M m n -> (M m b, R b, M b n)
svdCut mat =
  let b = cdim @b
      (u, s, v) = HM.thinSVD (extract mat)
  in ( createOrFail (fitColsHM b u)
     , fitSingularBondFromHM @b s
     , createOrFail (fitRowsHM b (HM.tr v)) )

fitSingularBondFromHM :: forall b. KnownNat b => VS.Vector Double -> R b
fitSingularBondFromHM s =
  createOrFail $
    let b = cdim @b
    in if VS.length s >= b then VS.take b s else s VS.++ VS.replicate (b - VS.length s) 0

-- | Pad or truncate matrix columns (dynamic helper for bond fitting).
fitColsHM :: Int -> HM.Matrix (Complex Double) -> HM.Matrix (Complex Double)
fitColsHM n m
  | HM.cols m >= n = HM.subMatrix (0, 0) (HM.rows m, n) m
  | otherwise      = m HM.||| HM.konst 0 (HM.rows m, n - HM.cols m)

-- | Pad or truncate matrix rows (dynamic helper for bond fitting).
fitRowsHM :: Int -> HM.Matrix (Complex Double) -> HM.Matrix (Complex Double)
fitRowsHM n m
  | HM.rows m >= n = HM.subMatrix (0, 0) (n, HM.cols m) m
  | otherwise      = HM.konst 0 (n - HM.rows m, HM.cols m) HM.=== m

-- | Element of a static complex matrix via dynamic 'extract'.
staticMatAt :: (KnownNat m, KnownNat n) => M m n -> Int -> Int -> Complex Double
staticMatAt m r c = (HM.toLists (extract m)) !! r !! c

-- isometry @C n +> C b@ and residual @C b +> C d@.
svdSplit
  :: forall n d b. (KnownNat n, KnownNat d, KnownNat b)
  => C n +> C d -> (C n +> C b, C b +> C d)
svdSplit (LinearMap lm) =
  let (u, s, vt) = svdCut @n @d @b lm
  in ( LinearMap u
     , LinearMap (mul (diagR 0 (complex s)) vt) )

-- | Split @C n +> (C m ⊗ C p)@ (tensor codomain) at bond @b@.
svdSplitTensor
  :: forall n m p b mp
   . ( KnownNat n, KnownNat m, KnownNat p, KnownNat b, KnownNat mp
     , mp ~ m * p )
  => C n +> (C m ⊗ C p) -> (C n +> C b, C b +> (C m ⊗ C p))
svdSplitTensor (LinearMap lm) =
  let (u, s, vt) = svdCut @n @mp @b lm
  in ( LinearMap u
     , LinearMap (mul (diagR 0 (complex s)) vt) )

-- | Reshape the first-cut residual @C b₁ +> (C p ⊗ C p)@ for the second SVD:
-- @C (b₁·p) +> C p@.
restForSecondCut
  :: forall p b
   . (KnownNat p, KnownNat b, KnownNat (p * p), KnownNat (b * p))
  => C b +> (C p ⊗ C p) -> C (b * p) +> C p
restForSecondCut (LinearMap lm) =
  LinearMap (reshapeResidual @p @b lm)

-- | Inverse of 'siteForLeftSVD' (see 'TensorNetwork.DMRG.Fixed3'): flatten
-- @(bond ⊗ physical)@ to @C (bl·p)@ before SVD, then re-expand.
siteFromLeftSVD
  :: forall bl p br
   . (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * bl), p * bl ~ bl * p)
  => C (bl * p) +> C br -> (C bl ⊗ C p) +> C br
siteFromLeftSVD g = g . fuseBond @p @bl . swapMap

-- | Left boundary site from the first SVD factor @C p +> C b@.
leftSiteFromFactor
  :: forall p b1. (KnownNat p, KnownNat b1) => (C p +> C b1) -> Site 1 p b1
leftSiteFromFactor f = Site (f . lunit @(C p))

-- | Right boundary site from the second-cut residual @C b +> C p@.
rightSiteFromFactor
  :: forall p b2
   . (KnownNat p, KnownNat b2, KnownNat (p * 1))
  => (C b2 +> C p) -> Site b2 p 1
rightSiteFromFactor (LinearMap m) = Site (siteLinearMap m)

-- | Reshape @M b₁ (p²)@ to @M (b₁·p) p@ for the second TT-SVD cut.
reshapeResidual
  :: forall p b1
   . (KnownNat p, KnownNat b1, KnownNat (b1 * p), KnownNat (p * p))
  => M b1 (p * p) -> M (b1 * p) p
reshapeResidual g1 =
  createOrFail $
    HM.fromLists
      [ [ staticMatAt g1 α (s2 + p * s3) | s3 <- [0 .. p - 1] ]
      | α <- [0 .. b1 - 1], s2 <- [0 .. p - 1] ]
  where
    p = cdim @p
    b1 = cdim @b1


-- | Encode a flat physical vector as an MPS via TT-SVD.
mpsFromPhysicalFlat
  :: forall p b
   . ( KnownNat p, KnownNat b
     , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p)
     , KnownNat (p * b), KnownNat (p * b), KnownNat (p * 1)
     , KnownNat (b * p), p * b ~ b * p )
  => C (p * p * p) -> MPS3 p b
mpsFromPhysicalFlat = mpsFromPhysical . physicalFromFlat

-- -- | Encode a flat @C (p³)@ vector as an MPS.
-- mpsFromFlat
--   :: forall p b
--    . ( KnownNat p, KnownNat b1, KnownNat b2
--      , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p)
--      , KnownNat (p * b1), KnownNat (p * b2), KnownNat (p * 1)
--      , KnownNat (b1 * p), p * b1 ~ b1 * p )
--   => C (p * p * p) -> MPS3 p b
-- mpsFromFlat = mpsFromPhysicalFlat

-- | Re-encode an MPS from its physical tensor (SVD gauge).
canonicalMPS
  :: forall p b
   . ( KnownNat p, KnownNat b
     , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p)
     , KnownNat (p * b), KnownNat (p * b), KnownNat (p * 1)
     , KnownNat (b * p), p * b ~ b * p )
  => MPS3 p b -> MPS3 p b
canonicalMPS = mpsFromPhysical . mpsToTensor

--------------------------------------------------------------------------------
-- Phase 2: Hilbert-space structure (inner product, norm)
--
-- Conjugation convention (memory `conjugation-conventions`): conjugation
-- happens in exactly one place — 'dagger' applied to bra sites inside
-- 'transferStep' / 'mpoTransferStep'. Everything else is bilinear.
--------------------------------------------------------------------------------

-- | Entry-wise complex conjugation of a site map ('conjugateMap', i.e.
-- 'vectorConjugate' on the map's own vector-space structure).
conjugateSite
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br)
  => Site bl p br -> Site bl p br
conjugateSite (Site f) = Site (conjugateMap f)

-- | The conjugated MPS — i.e. the bra ⟨ψ| as a (still ket-oriented) MPS.
mpsConjugate
  :: (KnownNat p, KnownNat b)
  => MPS3 p b -> MPS3 p b
mpsConjugate mps =
  withMPS3 mps $ \l c r ->
    mps3 (conjugateSite l) (conjugateSite c) (conjugateSite r)

-- | One transfer-matrix update for ⟨ψ|φ⟩. The environment maps the bra bond
-- to the ket bond; the bra site enters via 'dagger' (the only conjugation):
--
--   @transferStep bra ket env = ket ∘ (env ⊗^ id_p) ∘ dagger bra@
transferStep
  :: forall p alB arB alK arK.
     ( KnownNat p, KnownNat alB, KnownNat arB, KnownNat alK, KnownNat arK )
  => Site alB p arB        -- ^ bra site (conjugated internally)
  -> Site alK p arK        -- ^ ket site
  -> (C alB +> C alK)      -- ^ environment: bra bond ↦ ket bond
  -> (C arB +> C arK)
transferStep (Site bra) (Site ket) env =
  ket . (env ⊗^ idC @p) . dagger bra



-- | The MPS norm @√⟨ψ|ψ⟩@.
mpsNorm
  :: (KnownNat p, KnownNat b)
  => MPS3 p b -> Double
mpsNorm psi = sqrt (realPart (mpsInner psi psi))

--------------------------------------------------------------------------------
-- Phase 3: MPOs and expectation values
--------------------------------------------------------------------------------

-- | The shared MPO-column wiring: route the physical leg emitted on the right
-- of a @(bond-pair ⊗ physical)@ tensor through the MPO site (transfer
-- orientation) and then into the ket site:
--
--   @(C wl ⊗ C bl) ⊗ C p  +>  C wr ⊗ C br@
opWire
  :: forall p wl wr bl br.
     ( KnownNat p, KnownNat wl, KnownNat wr, KnownNat bl, KnownNat br )
  => ((C wl ⊗ C p) +> (C wr ⊗ C p))     -- ^ MPO site map
  -> ((C bl ⊗ C p) +> C br)             -- ^ ket site map
  -> (((C wl ⊗ C bl) ⊗ C p) +> (C wr ⊗ C br))
opWire op ket =
  (idC @wr ⊗^ ket)          -- wr ⊗ (bl ⊗ s)  →  wr ⊗ br
    . (idC @wr ⊗^ swapMap)  -- wr ⊗ (s ⊗ bl)  →  wr ⊗ (bl ⊗ s)
    . rassocMap             -- (wr ⊗ s) ⊗ bl  →  wr ⊗ (s ⊗ bl)
    . (op ⊗^ idC @bl)       -- (wl ⊗ t) ⊗ bl  →  (wr ⊗ s) ⊗ bl
    . lassocMap             -- wl ⊗ (t ⊗ bl)  →  (wl ⊗ t) ⊗ bl
    . (idC @wl ⊗^ swapMap)  -- wl ⊗ (bl ⊗ t)  →  wl ⊗ (t ⊗ bl)
    . rassocMap             -- (wl ⊗ bl) ⊗ t  →  wl ⊗ (bl ⊗ t)

-- | One MPO–MPS transfer update for ⟨ψ|H|φ⟩, with /typed/ environments
-- @C braBond +> (C mpoBond ⊗ C ketBond)@ — never flattened:
--
--   @mpoTransferStep bra op ket env = opWire op ket ∘ (env ⊗^ id_p) ∘ dagger bra@
mpoTransferStep
  :: forall p wl wr alB arB alK arK.
     ( KnownNat p, KnownNat wl, KnownNat wr
     , KnownNat alB, KnownNat arB, KnownNat alK, KnownNat arK )
  => Site alB p arB        -- ^ bra site (conjugated internally)
  -> OpSite wl p wr
  -> Site alK p arK        -- ^ ket site
  -> (C alB +> (C wl ⊗ C alK))
  -> (C arB +> (C wr ⊗ C arK))
mpoTransferStep (Site bra) (OpSite op) (Site ket) env =
  opWire @p op ket . (env ⊗^ idC @p) . dagger bra

-- | Apply one MPO site to one MPS site; the product bond is fused into the
-- typed bond @C (w·b)@ via 'fuseBond' / 'splitBond'.
applyOpSiteToSite
  :: forall wl p wr bl br.
     ( KnownNat wl, KnownNat p, KnownNat wr, KnownNat bl, KnownNat br
     , KnownNat (wl * bl), KnownNat (wr * br) )
  => OpSite wl p wr -> Site bl p br -> Site (wl * bl) p (wr * br)
applyOpSiteToSite (OpSite op) (Site ket) =
  Site $
    fuseBond @wr @br
      . opWire @p op ket
      . (splitBond @wl @bl ⊗^ idC @p)

-- | Apply an MPO to an MPS, staying in MPS form. Internal bond dimensions
-- multiply: @(wᵢ, bᵢ) ↦ wᵢ·bᵢ@.
mpoApplyMPS
  :: forall p w b.
     ( KnownNat p, KnownNat w, KnownNat b
     , KnownNat (w * b) )
  => MPO3 p w -> MPS3 p b -> MPS3 p (w * b)
mpoApplyMPS mpo mps =
  withMPO3 mpo $ \lOp cOp rOp ->
  withMPS3 mps $ \lSite cSite rSite ->
    mps3
      (applyOpSiteToSite @1 @p @w @1 @b lOp lSite)
      (applyOpSiteToSite @w @p @w @b @b cOp cSite)
      (applyOpSiteToSite @w @p @1 @b @1 rOp rSite)

-- | ⟨ψ|H|φ⟩ via left-to-right MPO–MPS transfer contraction: start from the
-- inverse left unitor as the boundary environment, take three
-- 'mpoTransferStep's, close with the left unitor and the trace.
mpsMPOInner
    :: forall p a w b.
     ( KnownNat p
     , KnownNat a, KnownNat b
     , KnownNat w )
  => MPS3 p a -> MPO3 p w -> MPS3 p b -> Complex Double
mpsMPOInner mpsB mpo mpsK =
  withMPS3 mpsB $ \lB cB rB ->
  withMPO3 mpo $ \lOp cOp rOp ->
  withMPS3 mpsK $ \lK cK rK ->
    trace -+$>
      ( lunit
          . ( mpoTransferStep @p rB rOp rK $
                mpoTransferStep @p cB cOp cK $
                  mpoTransferStep @p lB lOp lK (lunitInv @(C 1)) ) )

-- | The identity operator as a bond-dimension-one MPO.
identityMPO :: forall p. KnownNat p => MPO3 p 1
identityMPO =
  let identSite = OpSite (Cat.id :: (C 1 ⊗ C p) +> (C 1 ⊗ C p))
  in mpo3 identSite identSite identSite

-- | Apply an MPO to a physical tensor: 'mpsFromPhysical' encode,
-- 'mpoApplyMPS', then 'mpsToTensor' decode. The MPO step and decode are
-- morphism-level (like 'mpsToTensor'); the encode still uses TT-SVD.
mpoApplyPhysical
  :: forall p w.
     ( KnownNat p, KnownNat w, KnownNat (w * p)
     , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p)
     , KnownNat (p * p), KnownNat (p * p), KnownNat (p * 1)
     , KnownNat (p * p), p * p ~ p * p )
  => MPO3 p w -> Physical3 p -> Physical3 p
mpoApplyPhysical mpo =
  mpsToTensor . mpoApplyMPS mpo . mpsFromPhysical @p @p

-- | Apply an MPO to a flattened @C (p³)@ state (same path as
-- 'mpoApplyPhysical', with 'physicalFromFlat' / 'mpsToFlat').
mpoApplyFlat
  :: forall p w.
     ( KnownNat p, KnownNat w, KnownNat (w * p)
     , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p)
     , KnownNat (p * p), KnownNat (p * p), KnownNat (p * 1)
     , KnownNat (p * p), p * p ~ p * p )
  => MPO3 p w -> C (p * p * p) -> C (p * p * p)
mpoApplyFlat mpo =
  mpsToFlat . mpoApplyMPS mpo . mpsFromPhysicalFlat @p @p

-- | Matrix form on @C (p³)@: materialise the morphism above in the canonical
-- basis ('toDenseMatrix'). Row/column order matches 'flatIndex3'.
mpoToMatrix
  :: forall p w.
     ( KnownNat p, KnownNat w, KnownNat (w * p)
     , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p)
     , KnownNat (p * p), KnownNat (p * p), KnownNat (p * 1)
     , KnownNat (p * p), p * p ~ p * p )
  => MPO3 p w -> M (p * p * p) (p * p * p)
mpoToMatrix mpo =
  createOrFail
    (toDenseMatrix (sampleLinearFunction -+$> LinearFunction (mpoApplyFlat mpo)))










-- | Flatten a physical tensor in the same co-lexicographic order as 'mpsToFlat'.
physicalToFlat
  :: forall p.
     ( KnownNat p, KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p) )
  => Physical3 p -> C (p * p * p)
physicalToFlat =
  unsafeFromArray . (toArray :: Physical3 p -> VS.Vector (Complex Double))

-- | Reconstruct a physical tensor from a flat @C (p³)@ vector (inverse of
-- 'physicalToFlat' via the canonical 'toArray' order).
physicalFromFlat
  :: forall p.
     ( KnownNat p, KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p) )
  => C (p * p * p) -> Physical3 p
physicalFromFlat v = unsafeFromArray (unwrap v)



--------------------------------------------------------------------------------
-- Property tests. Entries are small Gaussian integers, so all
-- amplitudes/overlaps are exact and comparable with '==='.
--------------------------------------------------------------------------------

-- | Small Gaussian-integer complex number (exact arithmetic).
smallComplex :: QC.Gen (Complex Double)
smallComplex = do
  r <- QC.elements [-2 .. 2 :: Int]
  i <- QC.elements [-2 .. 2 :: Int]
  pure (fromIntegral r :+ fromIntegral i)

-- | Random @C n@ with small Gaussian-integer entries.
genC
  :: forall n. KnownNat n
  => QC.Gen (C n)
genC = do
  xs <- replicateM (cdim @n) smallComplex
  pure (fromList xs)

-- | Random endomorphism @C n +> C n@.
genEndo
  :: forall n. KnownNat n => QC.Gen (C n +> C n)
genEndo = do
  imgs <- replicateM (cdim @n) (genC @n)
  pure (fst $ recomposeLinMap (entireBasis :: SubBasis (C n)) imgs)

-- | Random tensor @C a ⊗ C b@ with small Gaussian-integer entries.
genTensor
  :: forall a b. (KnownNat a, KnownNat b)
  => QC.Gen (C a ⊗ C b)
genTensor = do
  xs <- replicateM (cdim @a * cdim @b) smallComplex
  pure $
    sumV
      [ (xs !! (i * cdim @b + j)) *^ (basis @a i ⊗ basis @b j)
      | i <- [0 .. cdim @a - 1], j <- [0 .. cdim @b - 1] ]

-- | Random typed MPO environment @C a +> (C w ⊗ C b)@.
genEnv3
  :: forall a w b. (KnownNat a, KnownNat w, KnownNat b)
  => QC.Gen (C a +> (C w ⊗ C b))
genEnv3 = do
  imgs <- replicateM (cdim @a) (genTensor @w @b)
  pure (fst $ recomposeLinMap (entireBasis :: SubBasis (C a)) imgs)

-- | Random site in the linearmap-category basis order.
genSite
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br)
  => QC.Gen (Site bl p br)
genSite = do
  imgs <- replicateM (cdim @bl * cdim @p) (genC @br)
  let lin = fst $ recomposeLinMap (entireBasis :: SubBasis (C bl ⊗ C p)) imgs
  pure (Site lin)

-- | Random @MPS 2 2 2@ (physical dim 2, both bonds 2).
genMPS222 :: QC.Gen (MPS3 2 2)
genMPS222 = mps3 <$> genSite @1 @2 @2 <*> genSite @2 @2 @2 <*> genSite @2 @2 @1

-- | Random @MPS 3 3 3@ (physical dim 3, both bonds 3).
genMPS333 :: QC.Gen (MPS3 3 3)
genMPS333 = mps3 <$> genSite @1 @3 @3 <*> genSite @3 @3 @3 <*> genSite @3 @3 @1

-- | Random MPO site in the linearmap-category basis order.
genOpSite
  :: forall wl p wr. (KnownNat wl, KnownNat p, KnownNat wr)
  => QC.Gen (OpSite wl p wr)
genOpSite = do
  imgs <- replicateM (cdim @wl * cdim @p) (genTensor @wr @p)
  let lin = fst $ recomposeLinMap (entireBasis :: SubBasis (C wl ⊗ C p)) imgs
  pure (OpSite lin)

-- | Random @MPO 2 2 2@ (physical dim 2, both operator bonds 2).
genMPO222 :: QC.Gen (MPO3 2 2)
genMPO222 = mpo3 <$> genOpSite @1 @2 @2 <*> genOpSite @2 @2 @2 <*> genOpSite @2 @2 @1

-- | 'applySite' is linear in the bond and matches the coefficient oracle.
prop_applySiteMatchesCoeff :: QC.Property
prop_applySiteMatchesCoeff =
  QC.forAll (genSite @2 @2 @2) $ \site ->
  QC.forAll (QC.choose (0, 1)) $ \s ->
  QC.forAll (genC @2) $ \bond ->
    let ref =
          fromList
            [ sum
                [ siteCoeff @2 @2 @2 site lB s r * (unwrap bond VS.! lB)
                | lB <- [0 .. 1] ]
            | r <- [0 .. 1] ]
    in applySite @2 @2 @2 site bond s QC.=== ref

-- | 'applyOpSite' is linear in the bond and matches the coefficient oracle.
prop_applyOpSiteMatchesCoeff :: QC.Property
prop_applyOpSiteMatchesCoeff =
  QC.forAll (genOpSite @2 @2 @2) $ \site ->
  QC.forAll (QC.choose (0, 1)) $ \t ->
  QC.forAll (QC.choose (0, 1)) $ \s ->
  QC.forAll (genC @2) $ \bond ->
    let ref =
          fromList
            [ sum
                [ opSiteCoeff @2 @2 @2 site lW t r s * (unwrap bond VS.! lW)
                | lW <- [0 .. 1] ]
            | r <- [0 .. 1] ]
    in applyOpSite @2 @2 @2 site bond t s QC.=== ref

-- | Categorical 'transferStep' agrees with the explicit matrix formula.
prop_transferStepMatchesMatrix :: QC.Property
prop_transferStepMatchesMatrix =
  QC.forAll (genSite @2 @2 @2) $ \bra ->
  QC.forAll (genSite @2 @2 @2) $ \ket ->
  QC.forAll (QC.Blind <$> genEndo @2) $ \(QC.Blind env) ->
  QC.forAll (QC.choose (0, 1)) $ \rB ->
  QC.forAll (QC.choose (0, 1)) $ \rK ->
    envCoeff @2 @2 (transferStep @2 bra ket env) rB rK
      QC.=== matrixTransferCoeff @2 @2 @2 bra ket env rB rK

-- | 'conjugateSite' matches entry-wise coefficient conjugation.
prop_conjSiteMatchesCoeff :: QC.Property
prop_conjSiteMatchesCoeff =
  QC.forAll (genSite @2 @2 @2) $ \site ->
  QC.forAll (QC.choose (0, 1)) $ \l ->
  QC.forAll (QC.choose (0, 1)) $ \s ->
  QC.forAll (QC.choose (0, 1)) $ \r ->
    siteCoeff @2 @2 @2 (conjugateSite site) l s r
      QC.=== conjugate (siteCoeff @2 @2 @2 site l s r)

-- | Categorical 'mpsToFlat' agrees with the basis-sum reference.
prop_mpsToFlatMatchesReference :: QC.Property
prop_mpsToFlatMatchesReference =
  QC.forAll genMPS222 $ \psi ->
    mpsToFlat psi QC.=== mpsToFlatReference psi

-- | Basis-sum reference agrees with flattened sesquilinear overlap.
prop_referenceMatchesFlat :: QC.Property
prop_referenceMatchesFlat =
  QC.forAll genMPS222 $ \psi ->
  QC.forAll genMPS222 $ \phi ->
    mpsInnerReference psi phi QC.=== (mpsToFlatReference psi <.> mpsToFlatReference phi)

-- | ⟨ψ|φ⟩ via transfer matrices agrees with the flattened-vector overlap.
prop_innerMatchesFlat :: QC.Property
prop_innerMatchesFlat =
  QC.forAll genMPS222 $ \psi ->
  QC.forAll genMPS222 $ \phi ->
    mpsInner psi phi QC.=== (mpsToFlat psi <.> mpsToFlat phi)

-- | The categorical transfer contraction agrees with the explicit basis oracle.
prop_innerMatchesReference :: QC.Property
prop_innerMatchesReference =
  QC.forAll genMPS222 $ \psi ->
  QC.forAll genMPS222 $ \phi ->
    mpsInner psi phi QC.=== mpsInnerReference psi phi

-- | ⟨ψ|φ⟩ = conjugate ⟨φ|ψ⟩.
prop_innerConjugateSymmetric :: QC.Property
prop_innerConjugateSymmetric =
  QC.forAll genMPS222 $ \psi ->
  QC.forAll genMPS222 $ \phi ->
    mpsInner psi phi QC.=== conjugate (mpsInner phi psi)

-- | ⟨ψ|ψ⟩ is real and non-negative.
prop_normNonNegative :: QC.Property
prop_normNonNegative =
  QC.forAll genMPS222 $ \psi ->
    let z = mpsInner psi psi
    in QC.counterexample (show z) (imagPart z == 0 && realPart z >= 0)

-- | Categorical 'mpoTransferStep' agrees with the explicit typed-env formula.
prop_mpoTransferStepMatchesMatrix :: QC.Property
prop_mpoTransferStepMatchesMatrix =
  QC.forAll (genSite @2 @2 @2) $ \bra ->
  QC.forAll (genOpSite @2 @2 @2) $ \op ->
  QC.forAll (genSite @2 @2 @2) $ \ket ->
  QC.forAll (QC.Blind <$> genEnv3 @2 @2 @2) $ \(QC.Blind env) ->
  QC.forAll (QC.choose (0, 1)) $ \rB ->
  QC.forAll (QC.choose (0, 1)) $ \rW ->
  QC.forAll (QC.choose (0, 1)) $ \rK ->
    env3Coeff @2 @2 @2 (mpoTransferStep @2 bra op ket env) rB rW rK
      QC.=== matrixMPOTransferCoeff @2 @2 @2 @2 @2 bra op ket env rB rW rK

-- | Categorical @⟨ψ|H|φ⟩@ agrees with the basis-sum reference.
prop_mpsMPOInnerMatchesReference :: QC.Property
prop_mpsMPOInnerMatchesReference =
  QC.forAll genMPS222 $ \psi ->
  QC.forAll genMPO222 $ \h ->
  QC.forAll genMPS222 $ \phi ->
    mpsMPOInner psi h phi QC.=== mpsMPOInnerReference psi h phi

-- | Categorical flattened MPO apply agrees with the basis-sum reference.
prop_mpoApplyFlatMatchesReference :: QC.Property
prop_mpoApplyFlatMatchesReference =
  QC.forAll genMPO222 $ \h ->
  QC.forAll (genC @(2 * 2 * 2)) $ \v ->
    flatApproxEq @8 1e-9 (mpoApplyFlat @2 @2 h v) (Ref.mpoApplyFlat @2 @2 h v)

-- | Categorical 'mpoToMatrix' agrees with the basis-sum reference.
prop_mpoToMatrixMatchesReference :: QC.Property
prop_mpoToMatrixMatchesReference =
  QC.forAll genMPO222 $ \h ->
    matrixApproxEq @8 1e-9 (mpoToMatrix @2 @2 h) (Ref.mpoToMatrix @2 @2 h)

-- | ⟨ψ|H|φ⟩ agrees with applying the flattened dense MPO to @φ@ first.
prop_mpoInnerMatchesFlat :: QC.Property
prop_mpoInnerMatchesFlat =
  QC.forAll genMPS222 $ \psi ->
  QC.forAll genMPO222 $ \h ->
  QC.forAll genMPS222 $ \phi ->
    complexApproxEq 1e-9
      (mpsMPOInner psi h phi)
      (mpsToFlat psi <.> mpoApplyFlat h (mpsToFlat phi))

-- | Applying an MPO in MPS form agrees with applying the flattened dense operator.
prop_mpoApplyMPSMatchesFlat :: QC.Property
prop_mpoApplyMPSMatchesFlat =
  QC.forAll genMPO222 $ \h ->
  QC.forAll genMPS222 $ \psi ->
    flatApproxEq @8 1e-9
      (mpsToFlat (mpoApplyMPS h psi))
      (mpoApplyFlat h (mpsToFlat psi))

-- | The identity MPO reduces the Phase-3 contraction to the Phase-2 inner product.
prop_identityMPOMatchesInner :: QC.Property
prop_identityMPOMatchesInner =
  QC.forAll genMPS222 $ \psi ->
  QC.forAll genMPS222 $ \phi ->
    mpsMPOInner psi (identityMPO @2) phi QC.=== mpsInner psi phi

-- | Componentwise approximate equality on flattened physical vectors.
flatApproxEq
  :: forall n. KnownNat n
  => Double -> C n -> C n -> Bool
flatApproxEq tol a b =
  VS.all (\d -> magnitude d <= tol) (VS.zipWith (-) (unwrap a) (unwrap b))

complexApproxEq :: Double -> Complex Double -> Complex Double -> Bool
complexApproxEq tol z w =
  magnitude (z - w) <= tol * (1 + magnitude z + magnitude w)

matrixApproxEq
  :: forall m n. (KnownNat m, KnownNat n)
  => Double -> M m n -> M m n -> Bool
matrixApproxEq tol a b =
  let la = concat (HM.toLists (extract a))
      lb = concat (HM.toLists (extract b))
  in all (uncurry (complexApproxEq tol)) (zip la lb)

-- | SVD 'mpsFromFlat' round-trips on flattened physical space (up to FP noise).
prop_mpsFromFlatRoundTripP2 :: QC.Property
prop_mpsFromFlatRoundTripP2 =
  QC.forAll genMPS222 $ \m ->
    flatApproxEq @8 1e-9 (mpsToFlat (mpsFromPhysicalFlat @2 @2 (mpsToFlat m))) (mpsToFlat m)

prop_mpsFromFlatOnRandomFlatP2 :: QC.Property
prop_mpsFromFlatOnRandomFlatP2 =
  QC.forAll (genC @(2 * 2 * 2)) $ \v ->
    flatApproxEq @8 1e-9 (mpsToFlat (mpsFromPhysicalFlat @2 @2 v)) v

prop_mpsFromFlatRoundTripP3 :: QC.Property
prop_mpsFromFlatRoundTripP3 =
  QC.forAll genMPS333 $ \m ->
    flatApproxEq @27 1e-9 (mpsToFlat (mpsFromPhysicalFlat @3 @3 (mpsToFlat m))) (mpsToFlat m)

-- | SVD 'canonicalMPS' preserves the flattened physical vector (up to FP noise).
prop_canonicalMPSRoundTripP2 :: QC.Property
prop_canonicalMPSRoundTripP2 =
  QC.forAll genMPS222 $ \m ->
    flatApproxEq @8 1e-9 (mpsToFlat (canonicalMPS @2 @2 m)) (mpsToFlat m)

prop_canonicalMPSRoundTripP3 :: QC.Property
prop_canonicalMPSRoundTripP3 =
  QC.forAll genMPS333 $ \m ->
    flatApproxEq @27 1e-9 (mpsToFlat (canonicalMPS @3 @3 m)) (mpsToFlat m)

-- | Run the Phase-2 property tests.
runMPSTests :: IO ()
runMPSTests = do
  putStrLn "SVD mpsFromFlat round-trips on physical space (p = 2)..."
  QC.quickCheck prop_mpsFromFlatRoundTripP2
  putStrLn "SVD mpsFromFlat on random flat C^8 (p = 2)..."
  QC.quickCheck prop_mpsFromFlatOnRandomFlatP2
  putStrLn "SVD mpsFromFlat round-trips on physical space (p = 3)..."
  QC.quickCheck prop_mpsFromFlatRoundTripP3
  putStrLn "SVD canonicalMPS round-trips on physical space (p = 2)..."
  QC.quickCheck prop_canonicalMPSRoundTripP2
  putStrLn "SVD canonicalMPS round-trips on physical space (p = 3)..."
  QC.quickCheck prop_canonicalMPSRoundTripP3
  putStrLn "MPS inner product matches flattened overlap..."
  QC.quickCheck prop_innerMatchesFlat
  putStrLn "MPS inner product matches basis reference..."
  QC.quickCheck prop_innerMatchesReference
  putStrLn "MPS inner product is conjugate-symmetric..."
  QC.quickCheck prop_innerConjugateSymmetric
  putStrLn "MPS norm-squared is real and non-negative..."
  QC.quickCheck prop_normNonNegative
  putStrLn "MPS-MPO-MPS contraction matches flattened operator..."
  QC.quickCheck prop_mpoInnerMatchesFlat
  putStrLn "MPO application in MPS form matches flattened operator..."
  QC.quickCheck prop_mpoApplyMPSMatchesFlat
  putStrLn "Identity MPO matches MPS inner product..."
  QC.quickCheck prop_identityMPOMatchesInner

-- NOTE (re @AI basis→HasBasis): `basis`/`one1` are ad-hoc standard-basis
-- builders; once a HasBasis (C n) instance is in use they can be replaced by
-- its `basisValue`. Kept explicit for now.

-- | Deterministically sample sites and print their storage dimensions.
debugSiteLayouts :: IO ()
debugSiteLayouts = do
  let s122 = unGen (genSite @1 @2 @2) (mkQCGen 0) 10
  let s222 = unGen (genSite @2 @2 @2) (mkQCGen 0) 10
  let s221 = unGen (genSite @2 @2 @1) (mkQCGen 0) 10
  let dims site =
        let m = unwrap (getLinearMap (siteLin site))
        in (HM.rows m, HM.cols m)
  putStrLn ("Site 1 2 2 dims: " ++ show (dims s122))
  putStrLn ("Site 2 2 2 dims: " ++ show (dims s222))
  putStrLn ("Site 2 2 1 dims: " ++ show (dims s221))

printSeededMPSInner :: IO ()
printSeededMPSInner = do
  let psi = unGen genMPS222 (mkQCGen 42) 30
  let mpo = unGen genMPO222 (mkQCGen 42) 30
  putStrLn ("<MPS | MPS> = " ++ show (mpsInner psi psi))
  putStrLn ("<MPS | MPO | MPS> = " ++ show (mpsMPOInner psi mpo psi))

test :: IO ()
test = do 
  let mps = unGen genMPS222 (mkQCGen 1) 30
      inner = mpsInner mps mps
  putStrLn $ show inner
  putStrLn (show $ siteL mps)