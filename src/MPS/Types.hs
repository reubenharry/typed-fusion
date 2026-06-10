{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | A finite, typed-bond, three-site matrix product state.
--
-- Design (see ROADMAP §4a — settled):
--
--   * __Site orientation: transfer / contraction.__ Each site is a linear map
--     taking @incoming-bond ⊗ physical@ to @outgoing-bond@. The boundary bonds
--     are the monoidal unit @C 1@. Bonds are typed (@KnownNat@), so a
--     bond-dimension mismatch between adjacent sites is a type error.
--
--   * Physical dimension @p@, bond dimensions @b1@ (between sites 1–2) and
--     @b2@ (between sites 2–3).
--
-- The amplitude of a configuration @(s₁, s₂, s₃)@ is
--
--   @ψ(s₁,s₂,s₃) = Σ_{l₁,l₂} L[(1,s₁),l₁] · C[(l₁,s₂),l₂] · R[(l₂,s₃),1]@
--
-- which 'mpsToFlat' evaluates by threading the bond vector through the three
-- site maps (no morphism-level tensor products or associators needed — just
-- vector tensoring '⊗' and map application '$').
module MPS.Types
  ( MPS (..)
  , OpSite (..)
  , MPO (..)
    -- * Map to physical space
  , mpsToTensor
  , mpsToFlat
  , amplitude
    -- * Hilbert-space structure (Phase 2)
  , mpsConjugate
  , mpsInner
  , mpsNorm
    -- * MPOs and expectations (Phase 3)
  , mpoElement
  , mpoToMatrix
  , mpoApplyFlat
  , mpoApplyMPS
  , mpsMPOInner
  , identityMPO
    -- * Generators (tests)
  , genMPS222
  , genMPO222
    -- * Property tests
  , prop_innerMatchesFlat
  , prop_innerConjugateSymmetric
  , prop_normNonNegative
  , prop_mpoInnerMatchesFlat
  , prop_mpoApplyMPSMatchesFlat
  , prop_identityMPOMatchesInner
  , runMPSTests
    -- * Debug / examples
  , printSeededMPSInner
  ) where

import Prelude hiding (($))
import qualified Control.Category.Constrained as Cat
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗), TensorSpace
  , FiniteDimensional (..), SubBasis
  , getAntilinearFunction, vectorConjugate, getLinearMap )
-- Orphan instances making @C n@ (and tensors over it) linearmap-category spaces.
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, M, Sized (fromList, unwrap))
import qualified Numeric.LinearAlgebra.HMatrix as HM
import GHC.TypeLits (KnownNat, Nat, natVal, type (*))
import Data.Proxy (Proxy (..))
import Data.Complex (Complex ((:+)), conjugate, realPart, imagPart)
import Data.VectorSpace (InnerSpace ((<.>)), VectorSpace ((*^)), sumV)
import Control.Monad (replicateM)
import qualified Data.Vector.Storable as VS
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

-- | One MPS site, represented as a linearmap-category tensor.
--
-- The hmatrix backend stores @(C bl ⊗ C p) +> C br@ as an @bl × (br·p)@
-- tensor. Contraction code below indexes that storage explicitly rather than
-- applying the map with @$@, because @$@ follows the backend tensor ordering,
-- while the MPS contraction convention is bond-major/physical-minor.
data Site (bl :: Nat) (p :: Nat) (br :: Nat) = Site
  { siteLin :: (C bl ⊗ C p) +> C br }

-- | A three-site MPS in transfer orientation. @p@ is the physical dimension;
-- @b1@, @b2@ are the two internal bond dimensions.
data MPS (p :: Nat) (b1 :: Nat) (b2 :: Nat) = MPS
  { siteL :: Site 1  p b1  -- ^ left:   (boundary ⊗ physical) → bond₁
  , siteC :: Site b1 p b2  -- ^ centre: (bond₁    ⊗ physical) → bond₂
  , siteR :: Site b2 p 1   -- ^ right:  (bond₂    ⊗ physical) → boundary
  }

-- | One MPO site in the same left-to-right transfer orientation as 'Site'.
-- The physical input is the ket leg, and the physical output is the bra leg.
data OpSite (wl :: Nat) (p :: Nat) (wr :: Nat) = OpSite
  { opSiteLin :: (C wl ⊗ C p) +> (C wr ⊗ C p) }

-- | A three-site matrix product operator with typed internal operator bonds.
data MPO (p :: Nat) (w1 :: Nat) (w2 :: Nat) = MPO
  { opL :: OpSite 1  p w1
  , opC :: OpSite w1 p w2
  , opR :: OpSite w2 p 1
  }

instance Show (MPS p b1 b2) where
  show _ = "MPS"

instance Show (MPO p w1 w2) where
  show _ = "MPO"

-- | The dimension of @C n@ as a value.
cdim :: forall n. KnownNat n => Int
cdim = fromIntegral (natVal (Proxy @n))


-- @AI: this should be wrapped into a HasBasis instance
-- | The @i@-th standard basis vector of @C n@.
basis :: forall n. KnownNat n => Int -> C n
basis i = fromList [ if j == i then 1 else 0 | j <- [0 .. cdim @n - 1] ]

-- | The unit vector of @C 1@.
one1 :: C 1
one1 = basis @1 0


-- | Coefficient of an MPS site tensor.
--
-- This is a narrow escape hatch around the current hmatrix backend layout for
-- nested tensor domains. Direct @$@ application of @(C bl ⊗ C p) +> C br@
-- currently mismatches the tensor-domain storage, so contraction reads exactly
-- the scalar it needs from the static matrix backing the 'LinearMap'.
siteCoeff
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br))
  => Site bl p br -> Int -> Int -> Int -> Complex Double
siteCoeff site lB s r =
  HM.atIndex (unwrap (getLinearMap (siteLin site))) (lB, r * cdim @p + s)

-- | Apply a site map to @(bond, |s⟩)@ using the established MPS convention.
applySite
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br))
  => Site bl p br -> C bl -> Int -> C br
applySite site bond s =
  fromList
    [ sum
        [ siteCoeff @bl @p @br site lB s r * (unwrap bond VS.! lB)
        | lB <- [0 .. cdim @bl - 1] ]
    | r <- [0 .. cdim @br - 1] ]

-- | Amplitude @ψ(s₁,s₂,s₃)@ of a single basis configuration, threading the
-- bond vector through the three site maps. Shared by 'mpsToTensor' and
-- 'mpsToFlat'.
amplitude
  :: forall p b1 b2.
     ( KnownNat p, KnownNat b1, KnownNat b2
     , KnownNat (p * b1), KnownNat (p * b2), KnownNat (p * 1) )
  => MPS p b1 b2 -> Int -> Int -> Int -> Complex Double
amplitude (MPS sL sC sR) s1 s2 s3 =
  let v1 = applySite @1 @p @b1 sL one1 s1
      v2 = applySite @b1 @p @b2 sC v1 s2
      r  = applySite @b2 @p @1 sR v2 s3
  in unwrap r VS.! 0

-- | Map the MPS to its physical state in @C p ⊗ (C p ⊗ C p)@ — the natural
-- "contract to physical space". (The flat @C (p³)@ form is the separate
-- convenience 'mpsToFlat'.)
mpsToTensor
  :: forall p b1 b2.
     ( KnownNat p, KnownNat b1, KnownNat b2
     , KnownNat (p * b1), KnownNat (p * b2), KnownNat (p * 1) )
  => MPS p b1 b2 -> C p ⊗ (C p ⊗ C p)
mpsToTensor mps =
  sumV
    [ amplitude mps s1 s2 s3 *^ (basis @p s1 ⊗ (basis @p s2 ⊗ basis @p s3))
    | s1 <- [0 .. p - 1], s2 <- [0 .. p - 1], s3 <- [0 .. p - 1] ]
  where p = cdim @p

-- | The same physical state, flattened to @C (p³)@ with index ordering
-- @(s₁,s₂,s₃) ↦ (s₁·p + s₂)·p + s₃@ — the same convention as
-- @Infinite.mpsToFlat@, so the two are directly comparable. Built directly from
-- the (un-conjugated) amplitudes, so it is a faithful oracle for inner products
-- (its @C n@ inner product '<.>' conjugates correctly).
mpsToFlat
  :: forall p b1 b2.
     ( KnownNat p, KnownNat b1, KnownNat b2, KnownNat (p * p * p)
     , KnownNat (p * b1), KnownNat (p * b2), KnownNat (p * 1) )
  => MPS p b1 b2 -> C (p * p * p)
mpsToFlat mps =
  fromList
    [ amplitude mps s1 s2 s3
    | s1 <- [0 .. p - 1], s2 <- [0 .. p - 1], s3 <- [0 .. p - 1] ]
  where p = cdim @p

--------------------------------------------------------------------------------
-- Phase 2: Hilbert-space structure (inner product, norm, dual)
--
-- Conjugation convention (memory `conjugation-conventions`): on @C n@ the inner
-- product '<.>' is sesquilinear (correct), but the bond contraction below is
-- written with the *bilinear* hmatrix 'H.outer'. So the conjugation that turns
-- a ket into a bra is applied *explicitly, per site*, via 'vectorConjugate'
-- (the settled design, ROADMAP §4a): 'mpsConjugate' makes the bra, and
-- 'mpsInner' then contracts it against the ket bilinearly.
--------------------------------------------------------------------------------

-- | Entry-wise complex conjugation of any linearmap-category vector (here, a
-- site map).
conjugateV :: TensorSpace v => v -> v
conjugateV = getAntilinearFunction vectorConjugate

-- | The conjugated MPS — i.e. the bra ⟨ψ|. Conjugates each site tensor
-- (per-site, explicit; see ROADMAP §4a).
mpsConjugate
  :: (KnownNat p, KnownNat b1, KnownNat b2)
  => MPS p b1 b2 -> MPS p b1 b2
mpsConjugate (MPS l c r) =
  MPS
    (Site (conjugateV (siteLin l)))
    (Site (conjugateV (siteLin c)))
    (Site (conjugateV (siteLin r)))

-- | The MPS inner product ⟨ψ|φ⟩. For the fixed 3-site chain this is the
-- explicit sum over physical indices (equivalent to transfer-matrix
-- contraction; a dedicated 'transferStep' can replace this for N-site).
mpsInner
  :: forall p a1 a2.
     ( KnownNat p
     , KnownNat a1, KnownNat a2
     , KnownNat (p * a1), KnownNat (p * a2)

     , KnownNat (p * 1) )
  => MPS p a1 a2 -> MPS p a1 a2 -> Complex Double
mpsInner psi phi =
  sum
    [ conjugate (amplitude psi s1 s2 s3) * amplitude phi s1 s2 s3
    | s1 <- [0 .. cdim @p - 1]
    , s2 <- [0 .. cdim @p - 1]
    , s3 <- [0 .. cdim @p - 1]
    ]

-- | The MPS norm @√⟨ψ|ψ⟩@.
mpsNorm
  :: ( KnownNat p, KnownNat b1, KnownNat b2
     , KnownNat (p * b1), KnownNat (p * b2), KnownNat (p * 1) )
  => MPS p b1 b2 -> Double
mpsNorm psi = sqrt (realPart (mpsInner psi psi))

--------------------------------------------------------------------------------
-- Phase 3: MPOs and expectation values
--------------------------------------------------------------------------------

-- | Coefficient of an MPO site tensor, with the same narrow backend-layout
-- escape hatch as 'siteCoeff'.
opSiteCoeff
  :: forall wl p wr.
     (KnownNat wl, KnownNat p, KnownNat wr, KnownNat (p * (wr * p)))
  => OpSite wl p wr -> Int -> Int -> Int -> Int -> Complex Double
opSiteCoeff site lW sIn r sOut =
  HM.atIndex (unwrap (getLinearMap (opSiteLin site))) (lW, (r * cdim @p + sOut) * cdim @p + sIn)

-- | Apply an MPO site and project onto a chosen output physical index, returning
-- the outgoing operator-bond vector.
applyOpSite
  :: forall wl p wr.
     (KnownNat wl, KnownNat wr, KnownNat p, KnownNat (p * (wr * p)))
  => OpSite wl p wr -> C wl -> Int -> Int -> C wr
applyOpSite site bond sIn sOut =
  fromList
    [ sum
        [ opSiteCoeff @wl @p @wr site lW sIn r sOut * (unwrap bond VS.! lW)
        | lW <- [0 .. cdim @wl - 1] ]
    | r <- [0 .. cdim @wr - 1] ]

-- | Dense operator matrix element @H[t₁,t₂,t₃; s₁,s₂,s₃]@.
mpoElement
  :: forall p w1 w2.
     ( KnownNat p, KnownNat w1, KnownNat w2
     , KnownNat (p * (w1 * p))
     , KnownNat (p * (w2 * p))
     , KnownNat (p * (1 * p)) )
  => MPO p w1 w2
  -> Int -> Int -> Int  -- ^ output/bra physical indices
  -> Int -> Int -> Int  -- ^ input/ket physical indices
  -> Complex Double
mpoElement (MPO l c r) t1 t2 t3 s1 s2 s3 =
  let v1 = applyOpSite @1 @p @w1 l one1 s1 t1
      v2 = applyOpSite @w1 @p @w2 c v1 s2 t2
      v3 = applyOpSite @w2 @p @1 r v2 s3 t3
  in unwrap v3 VS.! 0

-- | Matrix form of the 3-site MPO on flattened physical states, with row index
-- @(t₁·p + t₂)·p + t₃@ and column index @(s₁·p + s₂)·p + s₃@.
mpoToMatrix
  :: forall p w1 w2.
     ( KnownNat p, KnownNat w1, KnownNat w2, KnownNat (p * p * p)
     , KnownNat (p * (w1 * p))
     , KnownNat (p * (w2 * p))
     , KnownNat (p * (1 * p)) )
  => MPO p w1 w2 -> M (p * p * p) (p * p * p)
mpoToMatrix mpo =
  fromList
    [ mpoElement mpo t1 t2 t3 s1 s2 s3
    | t1 <- ix, t2 <- ix, t3 <- ix
    , s1 <- ix, s2 <- ix, s3 <- ix
    ]
  where
    p = cdim @p
    ix = [0 .. p - 1]

-- | Apply an MPO to a flattened physical state.
mpoApplyFlat
  :: forall p w1 w2.
     ( KnownNat p, KnownNat w1, KnownNat w2, KnownNat (p * p * p)
     , KnownNat (p * (w1 * p))
     , KnownNat (p * (w2 * p))
     , KnownNat (p * (1 * p)) )
  => MPO p w1 w2 -> C (p * p * p) -> C (p * p * p)
mpoApplyFlat mpo v =
  fromList
    [ sum
        [ mpoElement mpo t1 t2 t3 s1 s2 s3 * (unwrap v VS.! flatIndex s1 s2 s3)
        | s1 <- ix, s2 <- ix, s3 <- ix ]
    | t1 <- ix, t2 <- ix, t3 <- ix ]
  where
    p = cdim @p
    ix = [0 .. p - 1]
    flatIndex a b c = (a * p + b) * p + c

-- | Apply one MPO site to one MPS site. The resulting MPS bond is the product
-- of the MPO and MPS bonds.
applyOpSiteToSite
  :: forall wl p wr bl br.
     ( KnownNat wl, KnownNat p, KnownNat wr, KnownNat bl, KnownNat br
     , KnownNat (wl * bl), KnownNat (wr * br)
     , KnownNat (p * br), KnownNat (p * (wr * p)) )
  => OpSite wl p wr -> Site bl p br -> Site (wl * bl) p (wr * br)
applyOpSiteToSite op site =
  Site . fst $
    recomposeLinMap
      (entireBasis :: SubBasis (C (wl * bl) ⊗ C p))
      [ fromList
          [ conjugate $ sum
              [ opSiteCoeff @wl @p @wr op lW s rW t
                  * siteCoeff @bl @p @br site lB s rB
              | s <- [0 .. cdim @p - 1] ]
          | rW <- [0 .. cdim @wr - 1]
          , rB <- [0 .. cdim @br - 1]
          ]
      | lW <- [0 .. cdim @wl - 1]
      , lB <- [0 .. cdim @bl - 1]
      , t <- [0 .. cdim @p - 1]
      ]

-- | Apply an MPO to an MPS, staying in MPS form. Internal bond dimensions
-- multiply: @(wᵢ, bᵢ) ↦ wᵢ·bᵢ@.
mpoApplyMPS
  :: forall p w1 w2 b1 b2.
     ( KnownNat p, KnownNat w1, KnownNat w2, KnownNat b1, KnownNat b2
     , KnownNat (w1 * b1), KnownNat (w2 * b2)
     , KnownNat (p * b1), KnownNat (p * b2), KnownNat (p * 1)
     , KnownNat (p * (w1 * p)), KnownNat (p * (w2 * p)), KnownNat (p * (1 * p)) )
  => MPO p w1 w2 -> MPS p b1 b2 -> MPS p (w1 * b1) (w2 * b2)
mpoApplyMPS (MPO lOp cOp rOp) (MPS lSite cSite rSite) =
  MPS
    (applyOpSiteToSite @1 @p @w1 @1 @b1 lOp lSite)
    (applyOpSiteToSite @w1 @p @w2 @b1 @b2 cOp cSite)
    (applyOpSiteToSite @w2 @p @1 @b2 @1 rOp rSite)

-- | The matrix element ⟨ψ|H|φ⟩, contracting the conjugated bra amplitudes against
-- the MPO and ket amplitudes.
mpsMPOInner
  :: forall p a1 a2 w1 w2 b1 b2.
     ( KnownNat p
     , KnownNat a1, KnownNat a2, KnownNat b1, KnownNat b2
     , KnownNat w1, KnownNat w2
     , KnownNat (p * a1), KnownNat (p * a2)
     , KnownNat (p * b1), KnownNat (p * b2)
     , KnownNat (p * 1)
     , KnownNat (p * (w1 * p))
     , KnownNat (p * (w2 * p))
     , KnownNat (p * (1 * p)) )
  => MPS p a1 a2 -> MPO p w1 w2 -> MPS p b1 b2 -> Complex Double
mpsMPOInner psi mpo phi =
  sum
    [ conjugate (amplitude psi t1 t2 t3)
        * mpoElement mpo t1 t2 t3 s1 s2 s3
        * amplitude phi s1 s2 s3
    | t1 <- ix, t2 <- ix, t3 <- ix
    , s1 <- ix, s2 <- ix, s3 <- ix
    ]
  where ix = [0 .. cdim @p - 1]

-- | The identity operator as a bond-dimension-one MPO.
identityMPO :: forall p. KnownNat p => MPO p 1 1
identityMPO =
  let identSite = OpSite (Cat.id :: (C 1 ⊗ C p) +> (C 1 ⊗ C p))
  in MPO identSite identSite identSite

--------------------------------------------------------------------------------
-- Property tests (mirroring Infinite's prop_addThenFlatten style). Entries are
-- small Gaussian integers, so all amplitudes/overlaps are exact and comparable
-- with '==='.
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

-- | ⟨ψ|φ⟩ via transfer matrices agrees with the flattened-vector overlap.
prop_innerMatchesFlat :: QC.Property
prop_innerMatchesFlat =
  QC.forAll genMPS222 $ \psi ->
  QC.forAll genMPS222 $ \phi ->
    mpsInner psi phi QC.=== (mpsToFlat psi <.> mpsToFlat phi)

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

-- | Deterministically sample an @MPS 2 2 2@ and print @⟨MPS|MPS⟩@.
printSeededMPSInner :: IO ()
printSeededMPSInner = do
  let psi = unGen genMPS222 (mkQCGen 42) 30
  let mpo = unGen genMPO222 (mkQCGen 42) 30
  putStrLn ("<MPS | MPS> = " ++ show (mpsInner psi psi))
  putStrLn ("<MPS | MPO | MPS> = " ++ show (mpsMPOInner psi mpo psi))
