{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
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
module TensorNetwork.MPS.Fixed3
  ( MPS (..)
  , OpSite (..)
  , MPO (..)
    -- * Map to physical space
  , applySite
  , applyOpSite
  , one1
  , mpsToTensor
  , mpsToFlat
    -- * Hilbert-space structure (Phase 2)
  , conjugateSite
  , mpsConjugate
  , transferStep
  , mpsInner
  , mpsNorm
    -- * MPOs and expectations (Phase 3)
  , mpoElement
  , mpoToMatrix
  , mpoApplyFlat
  , mpoTransferStep
  , opWire
  , applyOpSiteToSite
  , mpoApplyMPS
  , mpsMPOInner
  , identityMPO
    -- * Generators (tests)
  , genMPS222
  , genMPO222
    -- * Property tests
  , prop_applySiteMatchesCoeff
  , prop_applyOpSiteMatchesCoeff
  , prop_conjSiteMatchesCoeff
  , prop_transferStepMatchesMatrix
  , prop_mpsToFlatMatchesReference
  , prop_referenceMatchesFlat
  , prop_innerMatchesFlat
  , prop_innerMatchesReference
  , prop_innerConjugateSymmetric
  , prop_normNonNegative
  , prop_mpoTransferStepMatchesMatrix
  , prop_mpsMPOInnerMatchesReference
  , prop_mpoInnerMatchesFlat
  , prop_mpoApplyMPSMatchesFlat
  , prop_identityMPOMatchesInner
  , runMPSTests
    -- * Debug / examples
  , printSeededMPSInner
  , debugSiteLayouts
  ) where

import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗)
  , FiniteDimensional (..), SubBasis
  , LinearMap, getLinearMap
  , trace, (-+$>) )
import Math.LinearMap.Category.Instances.Deriving ()
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import TensorNetwork.MPS.Fixed3.Internal
  ( Site (..), MPS (..), OpSite (..), MPO (..), one1, cdim, basis )
import TensorNetwork.MPS.Fixed3.Reference
  ( applySite, applyOpSite, siteCoeff, opSiteCoeff, envCoeff, env3Coeff
  , mpoElement, mpoToMatrix, mpoApplyFlat
  , matrixTransferCoeff, matrixMPOTransferCoeff
  , mpsInnerReference, mpsToFlatReference, mpsMPOInnerReference )
import TensorNetwork.Categorical
  ( (⊗^), swapMap, lassocMap, rassocMap, lunit, lunitInv
  , fuseBond, splitBond, conjugateMap )
import TensorNetwork.Dagger (dagger, transposeMap)
-- Orphan instances making @C n@ (and tensors over it) linearmap-category spaces.
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList, unwrap))
import qualified Numeric.LinearAlgebra.HMatrix as HM
import GHC.TypeLits (KnownNat, type (*))
import Data.Complex (Complex ((:+)), conjugate, realPart, imagPart)
import Data.VectorSpace (InnerSpace ((<.>)), VectorSpace ((*^)), sumV)
import Control.Monad (replicateM)
import qualified Data.Vector.Storable as VS
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

instance (KnownNat bl, KnownNat p, KnownNat br) => Show (Site bl p br) where
  show _ = "Site"

instance Show (MPS p b1 b2) where
  show _ = "MPS"

instance Show (MPO p w1 w2) where
  show _ = "MPO"

instance (KnownNat wl, KnownNat p, KnownNat wr) => Show (OpSite wl p wr) where
  show _ = "OpSite"

-- | Identity on @C n@, with the dimension named explicitly.
idC :: forall n. KnownNat n => C n +> C n
idC = Cat.id

--------------------------------------------------------------------------------
-- Map to physical space
--------------------------------------------------------------------------------

-- | The whole chain as one morphism eating the boundary bond and all three
-- physical legs: @(((C 1 ⊗ p) ⊗ p) ⊗ p) +> C 1@. Pure composition.
mpsChainMap
  :: forall p b1 b2.
     ( KnownNat p, KnownNat b1, KnownNat b2 )
  => MPS p b1 b2 -> ((((C 1 ⊗ C p) ⊗ C p) ⊗ C p) +> C 1)
mpsChainMap (MPS (Site l) (Site c) (Site r)) =
  r . ((c . (l ⊗^ idC @p)) ⊗^ idC @p)

-- | The physical state in @C p ⊗ (C p ⊗ C p)@: transpose the chain morphism
-- (turning the functional into a vector, no conjugation), close the boundary
-- with the left unitor, reassociate, and apply to @1 ∈ C 1@.
mpsToTensor
  :: forall p b1 b2.
     ( KnownNat p, KnownNat b1, KnownNat b2 )
  => MPS p b1 b2 -> C p ⊗ (C p ⊗ C p)
mpsToTensor mps =
  ( rassocMap
      . ((lunit ⊗^ idC @p) ⊗^ idC @p)
      . transposeMap (mpsChainMap mps) )
    $ one1

-- | Flattened physical state @C (p³)@ in the canonical 'toArray'
-- (co-lexicographic) order — the same order
-- 'TensorNetwork.Categorical.fuseBond' realises, and the order used by the
-- flat oracles in "TensorNetwork.MPS.Fixed3.Reference".
mpsToFlat
  :: forall p b1 b2.
     ( KnownNat p, KnownNat b1, KnownNat b2
     , KnownNat (p * p), KnownNat (p * (p * p)), KnownNat (p * p * p) )
  => MPS p b1 b2 -> C (p * p * p)
mpsToFlat mps =
  unsafeFromArray (toArray (mpsToTensor mps) :: VS.Vector (Complex Double))

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
  :: (KnownNat p, KnownNat b1, KnownNat b2)
  => MPS p b1 b2 -> MPS p b1 b2
mpsConjugate (MPS l c r) =
  MPS (conjugateSite l) (conjugateSite c) (conjugateSite r)

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

-- | The MPS inner product ⟨ψ|φ⟩: three transfer steps from the identity
-- boundary environment, closed with the trace on @C 1 +> C 1@.
mpsInner
  :: forall p a1 a2.
     ( KnownNat p, KnownNat a1, KnownNat a2 )
  => MPS p a1 a2 -> MPS p a1 a2 -> Complex Double
mpsInner (MPS lB cB rB) (MPS lK cK rK) =
  trace -+$>
    ( transferStep @p rB rK $
        transferStep @p cB cK $
          transferStep @p lB lK Cat.id )

-- | The MPS norm @√⟨ψ|ψ⟩@.
mpsNorm
  :: (KnownNat p, KnownNat b1, KnownNat b2)
  => MPS p b1 b2 -> Double
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
  :: forall p w1 w2 b1 b2.
     ( KnownNat p, KnownNat w1, KnownNat w2, KnownNat b1, KnownNat b2
     , KnownNat (w1 * b1), KnownNat (w2 * b2) )
  => MPO p w1 w2 -> MPS p b1 b2 -> MPS p (w1 * b1) (w2 * b2)
mpoApplyMPS (MPO lOp cOp rOp) (MPS lSite cSite rSite) =
  MPS
    (applyOpSiteToSite @1 @p @w1 @1 @b1 lOp lSite)
    (applyOpSiteToSite @w1 @p @w2 @b1 @b2 cOp cSite)
    (applyOpSiteToSite @w2 @p @1 @b2 @1 rOp rSite)

-- | ⟨ψ|H|φ⟩ via left-to-right MPO–MPS transfer contraction: start from the
-- inverse left unitor as the boundary environment, take three
-- 'mpoTransferStep's, close with the left unitor and the trace.
mpsMPOInner
  :: forall p a1 a2 w1 w2 b1 b2.
     ( KnownNat p
     , KnownNat a1, KnownNat a2, KnownNat b1, KnownNat b2
     , KnownNat w1, KnownNat w2 )
  => MPS p a1 a2 -> MPO p w1 w2 -> MPS p b1 b2 -> Complex Double
mpsMPOInner (MPS lB cB rB) (MPO lOp cOp rOp) (MPS lK cK rK) =
  trace -+$>
    ( lunit
        . ( mpoTransferStep @p rB rOp rK $
              mpoTransferStep @p cB cOp cK $
                mpoTransferStep @p lB lOp lK (lunitInv @(C 1)) ) )

-- | The identity operator as a bond-dimension-one MPO.
identityMPO :: forall p. KnownNat p => MPO p 1 1
identityMPO =
  let identSite = OpSite (Cat.id :: (C 1 ⊗ C p) +> (C 1 ⊗ C p))
  in MPO identSite identSite identSite

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
genMPS222 :: QC.Gen (MPS 2 2 2)
genMPS222 = MPS <$> genSite @1 @2 @2 <*> genSite @2 @2 @2 <*> genSite @2 @2 @1

-- | Random MPO site in the linearmap-category basis order.
genOpSite
  :: forall wl p wr. (KnownNat wl, KnownNat p, KnownNat wr)
  => QC.Gen (OpSite wl p wr)
genOpSite = do
  imgs <- replicateM (cdim @wl * cdim @p) (genTensor @wr @p)
  let lin = fst $ recomposeLinMap (entireBasis :: SubBasis (C wl ⊗ C p)) imgs
  pure (OpSite lin)

-- | Random @MPO 2 2 2@ (physical dim 2, both operator bonds 2).
genMPO222 :: QC.Gen (MPO 2 2 2)
genMPO222 = MPO <$> genOpSite @1 @2 @2 <*> genOpSite @2 @2 @2 <*> genOpSite @2 @2 @1

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

-- | ⟨ψ|H|φ⟩ agrees with applying the flattened dense MPO to @φ@ first.
prop_mpoInnerMatchesFlat :: QC.Property
prop_mpoInnerMatchesFlat =
  QC.forAll genMPS222 $ \psi ->
  QC.forAll genMPO222 $ \h ->
  QC.forAll genMPS222 $ \phi ->
    mpsMPOInner psi h phi QC.=== (mpsToFlat psi <.> mpoApplyFlat h (mpsToFlat phi))

-- | Applying an MPO in MPS form agrees with applying the flattened dense operator.
prop_mpoApplyMPSMatchesFlat :: QC.Property
prop_mpoApplyMPSMatchesFlat =
  QC.forAll genMPO222 $ \h ->
  QC.forAll genMPS222 $ \psi ->
    mpsToFlat (mpoApplyMPS h psi) QC.=== mpoApplyFlat h (mpsToFlat psi)

-- | The identity MPO reduces the Phase-3 contraction to the Phase-2 inner product.
prop_identityMPOMatchesInner :: QC.Property
prop_identityMPOMatchesInner =
  QC.forAll genMPS222 $ \psi ->
  QC.forAll genMPS222 $ \phi ->
    mpsMPOInner psi (identityMPO @2) phi QC.=== mpsInner psi phi

-- | Run the Phase-2 property tests.
runMPSTests :: IO ()
runMPSTests = do
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