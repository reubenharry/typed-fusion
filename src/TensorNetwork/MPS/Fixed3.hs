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
--   * __Inner product.__ 'mpsInner' contracts via morphism composition
--     ('transferStep': @ket ∘ (env ⊗^ id) ∘ dagger bra@).
--     Explicit basis sums live in "TensorNetwork.MPS.Fixed3.Reference"
--     as QuickCheck oracles.
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
  , FiniteDimensional (..), SubBasis, entireBasis
  , getLinearMap, getLinearFunction
  , trace, (-+$>), LinearMap (..)
  , sampleLinearFunction, LinearFunction, pattern LinearFunction )
import Math.LinearMap.Coercion (curryLinearMap, uncurryLinearMap, (-+$=>))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import TensorNetwork.MPS.Fixed3.Internal
  ( Site (..), MPS (..), OpSite (..), MPO (..), one1, cdim, basis
  , MPS3, MPO3, mps3, mpo3, withMPS3, withMPO3, OpWireNats )
import TensorNetwork.MPS.Fixed3.Reference
  ( applySite, applyOpSite, siteCoeff, opSiteCoeff, envCoeff, env3Coeff
  , matrixTransferCoeff, matrixMPOTransferCoeff
  , mpsInnerReference, mpsToFlatReference, mpsMPOInnerReference
  , permuteFlatLegs13, flatIndex3 )
import qualified TensorNetwork.MPS.Fixed3.Reference as Ref
import GroundState (toDenseMatrix)
import TensorNetwork.Categorical
  ( (⊗^), swapMap, lassocMap, rassocMap, lunit, lunitInv
  , fuseBond, splitBond, conjugateMap )
import TensorNetwork.Dagger (dagger, transposeMap, siteDagger)
-- Orphan instances making @C n@ (and tensors over it) linearmap-category spaces.
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static
  ( C, M, R, Sized (fromList, create)
  , Domain (diagR, mul), complex, extract, unwrap )
import TensorNetwork.MPS.LinmapStorage
  ( siteLinFromRows, tensorCodomainLinFromFlatRows
  , linMapFromColumnImages, envLinFromTensorImages )
import qualified Numeric.LinearAlgebra.HMatrix as HM
import GHC.TypeLits (KnownNat, type (*))
import Data.Complex (Complex ((:+)), conjugate, realPart, imagPart, magnitude)
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Data.Vector.Sized (toList)
import Data.VectorSpace (InnerSpace ((<.>)), VectorSpace ((*^), Scalar), sumV)
import Control.Monad (replicateM)
import qualified Data.Vector.Storable as VS
import qualified Test.QuickCheck as QC



-- | The physical state in @C p ⊗ (C p ⊗ C p)@: transpose the chain morphism
-- (turning the functional into a vector, no conjugation), close the boundary
-- with the left unitor, reassociate, and apply to @1 ∈ C 1@.
mpsToTensor
  :: forall p b.
     ( KnownNat p, KnownNat b
     , KnownNat (p * p), KnownNat (b * p), KnownNat (b * p * p) )
  => MPS3 p b -> C p ⊗ (C p ⊗ C p)
mpsToTensor = physicalFromClosedLegs . mpsChainClose


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



-- | Left-to-right ⟨ψ|φ⟩ transfer contraction over an open-boundary MPS chain.
foldTransferInner
  :: forall p b l.
     ( KnownNat p, KnownNat b, KnownNat l
     , KnownNat (b * p), KnownNat (p * b), p * b ~ b * p )
  => MPS p b l -> MPS p b l -> C 1 +> C 1
foldTransferInner (MPS lB bulkB rB) (MPS lK bulkK rK) =
  let env0 = transferStep @p lB lK (Cat.id :: C 1 +> C 1)
      envBulk =
        foldl'
          (\env (sB, sK) -> transferStep @p sB sK env)
          env0
          (zip (toList bulkB) (toList bulkK))
  in transferStep @p rB rK envBulk

-- | The MPS inner product ⟨ψ|φ⟩: transfer steps from the identity boundary
-- environment at the left, closed with the trace on @C 1 +> C 1@.
mpsInner
  :: forall p a l.
     ( KnownNat p, KnownNat a, KnownNat l
     , KnownNat (a * p), KnownNat (p * a), p * a ~ a * p )
  => MPS p a l -> MPS p a l -> Complex Double
mpsInner mps1 mps2 = trace -+$> foldTransferInner @p @a @l mps1 mps2













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

-- | @(C 1 ⊗ C p) +> C b@ from a left boundary site.
leftTransfer
  :: Site 1 p b -> (C 1 ⊗ C p) +> C b
leftTransfer (Site f) = f

-- | @(C b ⊗ C p) +> C b@ from a bulk site (uncurried transfer orientation).
bulkTransfer
  :: Site b p b -> (C b ⊗ C p) +> C b
bulkTransfer (Site f) = f

-- | @(C b ⊗ C p) +> C 1@ from a right boundary site.
rightTransfer
  :: Site b p 1 -> (C b ⊗ C p) +> C 1
rightTransfer (Site f) = f

-- | The whole chain as one morphism eating the boundary bond and all three
-- physical legs: @(((C 1 ⊗ p) ⊗ p) ⊗ p) +> C 1@. Pure composition.
mpsChainMap
  :: forall p b.
     ( KnownNat p, KnownNat b
     , KnownNat (p * p), KnownNat (b * p), KnownNat (b * p * p) )
  => MPS3 p b -> ((((C 1 ⊗ C p) ⊗ C p) ⊗ C p) +> C 1)
mpsChainMap mps =
  withMPS3 mps $ \l c r ->
    rightTransfer r
      . ((bulkTransfer c . (leftTransfer l ⊗^ idC @p)) ⊗^ idC @p)

-- | Close the categorical chain to 'Physical3' (before @s₁ ↔ s₃@ correction).
mpsChainClose
  :: forall p b.
     ( KnownNat p, KnownNat b
     , KnownNat (p * p), KnownNat (b * p), KnownNat (b * p * p) )
  => MPS3 p b -> Physical3 p
mpsChainClose mps =
  ( rassocMap
      . ((lunit ⊗^ idC @p) ⊗^ idC @p)
      . transposeMap (mpsChainMap mps) )
    $ one1

-- | Flattened physical state @C (p³)@ in the canonical 'toArray'
-- (co-lexicographic) order — the same order
-- 'TensorNetwork.Categorical.fuseBond' realises, and the order used by the
-- flat oracles in "TensorNetwork.MPS.Fixed3.Reference".
mpsToFlat
  :: forall p b.
     ( KnownNat p, KnownNat b
     , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p)
     , KnownNat (b * p), KnownNat (b * p * p) )
  => MPS3 p b -> C (p * p * p)
mpsToFlat mps =
  unsafeFromArray
    ( permuteFlatLegs13 @p (toArray (mpsChainClose mps) :: VS.Vector (Complex Double)) )

--------------------------------------------------------------------------------
-- Physical space ↔ MPS (SVD / TT decomposition)
--
-- Flat index @(s₁,s₂,s₃) ↦ s₁ + p·s₂ + p²·s₃@ matches 'mpsToFlat' /
-- 'flatIndex3'. The first SVD matricization is @M[s₁, s₂ + p·s₃]@.
--------------------------------------------------------------------------------

-- | Three-site physical Hilbert space, right-nested to match 'mpsToTensor':
-- @C p ⊗ (C p ⊗ C p)@.
type Physical3 p = C p ⊗ (C p ⊗ C p)

-- | Rebuild 'Physical3' from closed coefficients with @s₁ ↔ s₃@ leg order
-- corrected (matches 'mpsToFlatReference' / 'flatIndex3').
physicalFromClosedLegs
  :: forall p. KnownNat p => Physical3 p -> Physical3 p
physicalFromClosedLegs closed =
  let perm = permuteFlatLegs13 @p (toArray closed :: VS.Vector (Complex Double))
      p = cdim @p
  in sumV
       [ perm VS.! flatIndex3 p s1 s2 s3
           *^ (basis @p s1 ⊗ (basis @p s2 ⊗ basis @p s3))
       | s1 <- [0 .. p - 1]
       , s2 <- [0 .. p - 1]
       , s3 <- [0 .. p - 1]
       ]


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
  let (u, s, vt) = svdCut @d @n @b lm
  in ( LinearMap (mul (diagR 0 (complex s)) vt)
     , LinearMap u )

-- | Split @C n +> (C m ⊗ C p)@ (tensor codomain) at bond @b@.
svdSplitTensor
  :: forall n m p b mp
   . ( KnownNat n, KnownNat m, KnownNat p, KnownNat b, KnownNat mp
     , mp ~ m * p )
  => C n +> (C m ⊗ C p) -> (C n +> C b, C b +> (C m ⊗ C p))
svdSplitTensor (LinearMap lm) =
  let (u, s, vt) = svdCut @mp @n @b lm
  in ( LinearMap (mul (diagR 0 (complex s)) vt)
     , LinearMap u )

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

-- | Embed @C b₂ +> C p@ as right boundary site @(C b₂ ⊗ C p) +> C 1@.
rightSiteFromFactor
  :: forall p b2
   . (KnownNat p, KnownNat b2, KnownNat (p * 1), KnownNat (b2 * p), KnownNat (p * b2))
  => (C b2 +> C p) -> Site b2 p 1
rightSiteFromFactor f =
  let m = getLinearMap f
  in Site (siteLinFromRows @b2 @p @1
         [ fromList [staticMatAt m s lB]
         | lB <- [0 .. cdim @b2 - 1], s <- [0 .. cdim @p - 1] ])

-- | Reshape @M (p²) b₁@ (standard linmap) to @M p (b₁·p)@ for the second TT-SVD cut.
reshapeResidual
  :: forall p b1
   . (KnownNat p, KnownNat b1, KnownNat (b1 * p), KnownNat (p * p))
  => M (p * p) b1 -> M p (b1 * p)
reshapeResidual g1 =
  createOrFail $
    HM.fromLists
      [ [ staticMatAt g1 (s2 + p * s3) α | α <- [0 .. b1 - 1], s2 <- [0 .. p - 1] ]
      | s3 <- [0 .. p - 1] ]
  where
    p = cdim @p
    b1 = cdim @b1

-- | Embed @C b₂ +> C p@ (storage @M p b₂@) as right boundary site @M 1 (b₂·p)@.
boundToSite
  :: forall b2 p
   . (KnownNat b2, KnownNat p, KnownNat (b2 * p))
  => M p b2 -> M 1 (b2 * p)
boundToSite m =
  createOrFail $
    HM.fromLists
      [ [ staticMatAt m s lB | lB <- [0 .. b2 - 1], s <- [0 .. p - 1] ] ]
  where
    b2 = cdim @b2
    p = cdim @p


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
     , KnownNat (b * p), KnownNat (b * p * p), p * b ~ b * p )
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
-- to the ket bond; the bra site enters via 'dagger' (the only conjugation).
--
-- Equivalent to @ket ∘ (env ⊗^ id_p) ∘ dagger bra@ (same wiring as
-- 'mpoTransferStep' without the MPO leg).
--
--   @transferStep bra ket env = ket ∘ (env ⊗^ id) ∘ dagger bra@
transferStep
  :: forall p alB arB alK arK.
     ( KnownNat p, KnownNat alB, KnownNat arB, KnownNat alK, KnownNat arK
     , KnownNat (alB * p), KnownNat (alK * p), KnownNat (p * arB)
     , p * alB ~ alB * p )
  => Site alB p arB        -- ^ bra site (conjugated internally)
  -> Site alK p arK        -- ^ ket site
  -> (C alB +> C alK)      -- ^ environment: bra bond ↦ ket bond
  -> (C arB +> C arK)
transferStep (Site bra) (Site ket) env =
  ket . (env ⊗^ idC @p) . siteDagger bra



-- | The MPS norm @√⟨ψ|ψ⟩@.
mpsNorm
  :: (KnownNat p, KnownNat b, KnownNat (b * p), KnownNat (p * b), p * b ~ b * p)
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
     OpWireNats p wl wr bl br
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
     ( OpWireNats p wl wr alK arK
     , KnownNat alB, KnownNat arB
     , KnownNat (alB * p), KnownNat (wl * alK), KnownNat (p * arB)
     , p * alB ~ alB * p )
  => Site alB p arB        -- ^ bra site (conjugated internally)
  -> OpSite wl p wr
  -> Site alK p arK        -- ^ ket site
  -> (C alB +> (C wl ⊗ C alK))
  -> (C arB +> (C wr ⊗ C arK))
mpoTransferStep (Site bra) (OpSite op) (Site ket) env =
  opWire @p op ket . (env ⊗^ idC @p) . siteDagger bra

-- | Apply one MPO site to one MPS site; the product bond is fused into the
-- typed bond @C (w·b)@ via 'fuseBond' / 'splitBond'.
applyOpSiteToSite
  :: forall wl p wr bl br.
     ( OpWireNats p wl wr bl br, KnownNat (wl * bl), KnownNat (wr * br) )
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
     , KnownNat (w * b), KnownNat (w * p), KnownNat (b * p), KnownNat (p * b)
     , KnownNat ((w * p) * p), KnownNat (w * (b * p)), KnownNat (w * (p * b))
     , KnownNat ((w * b) * p), KnownNat (p * b)
     , p * 1 ~ 1 * p, p * b ~ b * p )
  => MPO3 p w -> MPS3 p b -> MPS3 p (w * b)
mpoApplyMPS mpo mps =
  withMPO3 mpo $ \lOp cOp rOp ->
  withMPS3 mps $ \lSite cSite rSite ->
    mps3
      (applyOpSiteToSite @1 @p @w @1 @b lOp lSite)
      (applyOpSiteToSite @w @p @w @b @b cOp cSite)
      (applyOpSiteToSite @w @p @1 @b @1 rOp rSite)

-- | Left-to-right ⟨ψ|H|φ⟩ MPO–MPS transfer contraction.
foldMPOTransferInner
  :: forall p a w b l.
     ( KnownNat p, KnownNat a, KnownNat b, KnownNat w, KnownNat l
     , KnownNat (a * p), KnownNat (b * p), KnownNat (w * b), KnownNat (p * a)
     , KnownNat (w * (p * a)), KnownNat (w * (a * p)), KnownNat (w * p)
     , KnownNat (p * b), KnownNat (p * a), KnownNat (w * (b * p))
     , KnownNat ((w * b) * p), KnownNat (w * (p * b))
     , p * a ~ a * p, p * 1 ~ 1 * p, p * b ~ b * p )
  => MPS p a l -> MPO p w l -> MPS p b l -> C 1 +> (C 1 ⊗ C 1)
foldMPOTransferInner (MPS lB bulkB rB) (MPO lOp bulkOp rOp) (MPS lK bulkK rK) =
  let env0 = mpoTransferStep @p @1 @w @1 @a @1 @b lB lOp lK (lunitInv @(C 1))
      envBulk =
        foldl'
          (\env (sB, o, sK) -> mpoTransferStep @p @w @w @a @a @b @b sB o sK env)
          env0
          (zip3 (toList bulkB) (toList bulkOp) (toList bulkK))
  in mpoTransferStep @p @w @1 @a @1 @b @1 rB rOp rK envBulk

-- | ⟨ψ|H|φ⟩ via left-to-right MPO–MPS transfer contraction: start from the
-- inverse left unitor as the boundary environment, fold 'mpoTransferStep'
-- over the chain, close with the left unitor and the trace.
mpsMPOInner
  :: forall p a w b l.
     ( KnownNat p
     , KnownNat a, KnownNat b
     , KnownNat w, KnownNat l
     , OpWireNats p w w a b
     , KnownNat (a * p), KnownNat (p * a), KnownNat (w * a)
     , p * a ~ a * p, p * 1 ~ 1 * p, p * b ~ b * p )
  => MPS p a l -> MPO p w l -> MPS p b l -> Complex Double
mpsMPOInner mpsB mpo mpsK =
  trace -+$> (lunit @(C 1) . foldMPOTransferInner @p @a @w @b @l mpsB mpo mpsK)

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
     , KnownNat (p * p), KnownNat (p * p * p), KnownNat (w * p * p)
     , KnownNat (w * p), KnownNat ((w * p) * p), KnownNat (w * (p * p))
     , KnownNat (((w * p) * p) * p), KnownNat (w * (p * p)), p * p ~ p * p )
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
     , KnownNat (p * p), KnownNat (p * p * p), KnownNat (w * p * p)
     , KnownNat (w * p), KnownNat ((w * p) * p), KnownNat (w * (p * p))
     , KnownNat (((w * p) * p) * p), KnownNat (p * p), p * p ~ p * p )
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
     , KnownNat (p * p), KnownNat (p * p * p), KnownNat (w * p * p)
     , KnownNat (w * p), KnownNat ((w * p) * p), KnownNat (w * (p * p))
     , KnownNat (((w * p) * p) * p), KnownNat (p * p), p * p ~ p * p )
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
genEndo = linMapFromColumnImages <$> replicateM (cdim @n) (genC @n)

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
  :: forall a w b. (KnownNat a, KnownNat w, KnownNat b, KnownNat (w * b))
  => QC.Gen (C a +> (C w ⊗ C b))
genEnv3 =
  envLinFromTensorImages <$> replicateM (cdim @a) (genTensor @w @b)

-- | Build a site in standard linmap storage @M br (bl·p)@ from application-oracle
-- rows (@bl·p@ images in @C br@, same order as 'siteMatrix').
siteFromApplicationRows
  :: forall bl p br
   . (KnownNat bl, KnownNat p, KnownNat br, KnownNat (bl * p), KnownNat (p * br))
  => [C br] -> Site bl p br
siteFromApplicationRows rows = Site (siteLinFromRows rows)

-- | Random site with column storage matching 'applyTensorLinMap'.
genSite
  :: forall bl p br
   . (KnownNat bl, KnownNat p, KnownNat br, KnownNat (bl * p), KnownNat (p * br))
  => QC.Gen (Site bl p br)
genSite =
  siteFromApplicationRows <$> replicateM (cdim @bl * cdim @p) (genC @br)

-- | Random @MPS 2 2 2@ (physical dim 2, both bonds 2).
genMPS222 :: QC.Gen (MPS3 2 2)
genMPS222 = mps3 <$> genSite @1 @2 @2 <*> genSite @2 @2 @2 <*> genSite @2 @2 @1

-- | Random @MPS 3 3 3@ (physical dim 3, both bonds 3).
genMPS333 :: QC.Gen (MPS3 3 3)
genMPS333 = mps3 <$> genSite @1 @3 @3 <*> genSite @3 @3 @3 <*> genSite @3 @3 @1

-- | Random MPO site in the linearmap-category basis order.
genOpSite
  :: forall wl p wr
   . (KnownNat wl, KnownNat p, KnownNat wr, KnownNat (wl * p), KnownNat (wr * p))
  => QC.Gen (OpSite wl p wr)
genOpSite = do
  imgs <- replicateM (cdim @wl * cdim @p) (genTensor @wr @p)
  let flats = [ fromList (VS.toList (toArray t)) | t <- imgs ]
  pure (OpSite (tensorCodomainLinFromFlatRows @wl @p @wr flats))

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

-- | Bulk transfer on @(bond ⊗ |s⟩)@ matches 'applySite'.
prop_bulkTransferMatchesApplySite :: QC.Property
prop_bulkTransferMatchesApplySite =
  QC.forAll (genSite @2 @2 @2) $ \site ->
  QC.forAll (genC @2) $ \bond ->
  QC.forAll (QC.choose (0, 1)) $ \s ->
    (bulkTransfer site $ (bond ⊗ basis @2 s)) QC.=== applySite site bond s

-- | Left transfer on a physical basis ket matches 'applySite'.
prop_leftTransferMatchesApplySite :: QC.Property
prop_leftTransferMatchesApplySite =
  QC.forAll (genSite @1 @2 @2) $ \lSite ->
  QC.forAll (QC.choose (0, 1)) $ \s ->
    (leftTransfer lSite $ (one1 ⊗ basis @2 s)) QC.=== applySite lSite one1 s

-- | @l ⊗^ id@ agrees with applying @l@ then tensoring with the physical leg.
prop_lTensorIdMatchesManual :: QC.Property
prop_lTensorIdMatchesManual =
  QC.forAll (genSite @1 @2 @2) $ \lSite ->
  QC.forAll (QC.choose (0, 1)) $ \s1 ->
  QC.forAll (QC.choose (0, 1)) $ \s2 ->
    let a = one1 ⊗ basis @2 s1
        b = basis @2 s2
        viaTensor = (leftTransfer lSite ⊗^ idC @2) $ (a ⊗ b)
        manual = (leftTransfer lSite $ a) ⊗ b
    in viaTensor =~= manual
  where
    (=~=) :: Eq a => a -> a -> QC.Property
    x =~= y = QC.property (x == y)

-- | Left + bulk transfer composition matches 'applySite' threading.
prop_leftBulkTransferMatchesApplySite :: QC.Property
prop_leftBulkTransferMatchesApplySite =
  QC.forAll (genSite @1 @2 @2) $ \lSite ->
  QC.forAll (genSite @2 @2 @2) $ \cSite ->
  QC.forAll (QC.choose (0, 1)) $ \s1 ->
  QC.forAll (QC.choose (0, 1)) $ \s2 ->
    let lc = bulkTransfer cSite . (leftTransfer lSite ⊗^ idC @2)
        inp = (one1 ⊗ basis @2 s1) ⊗ basis @2 s2
        ref = applySite cSite (applySite lSite one1 s1) s2
    in (lc $ inp) QC.=== ref

-- | Full 'mpsChainMap' on physical basis kets matches the amplitude oracle.
prop_mpsChainMapMatchesAmplitude :: QC.Property
prop_mpsChainMapMatchesAmplitude =
  QC.forAll genMPS222 $ \mps ->
  QC.forAll (QC.choose (0, 1)) $ \s1 ->
  QC.forAll (QC.choose (0, 1)) $ \s2 ->
  QC.forAll (QC.choose (0, 1)) $ \s3 ->
    let inp = ((one1 ⊗ basis @2 s1) ⊗ basis @2 s2) ⊗ basis @2 s3
        ref =
          withMPS3 mps $ \l c r ->
            unwrap (applySite r (applySite c (applySite l one1 s1) s2) s3) VS.! 0
    in unwrap (mpsChainMap mps $ inp) VS.! 0 QC.=== ref

-- | Permuted 'mpsChainClose' flat agrees with the amplitude oracle.
prop_mpsChainCloseFlatMatchesReference :: QC.Property
prop_mpsChainCloseFlatMatchesReference =
  QC.forAll genMPS222 $ \mps ->
    flatApproxEq @8 1e-9
      (unsafeFromArray (permuteFlatLegs13 @2 (toArray (mpsChainClose mps))))
      (mpsToFlatReference mps)

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