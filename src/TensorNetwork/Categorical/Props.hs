{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | QuickCheck properties for 'TensorNetwork.Categorical' and
-- 'TensorNetwork.Dagger', pinned against explicit coefficient oracles.
-- Entries are small Gaussian integers so all comparisons are exact ('===').
--
-- These properties are also the regression suite for the backend behaviour of
-- 'vectorConjugate' on tensor/map spaces over @C n@ (ROADMAP §4a step 5).
module TensorNetwork.Categorical.Props
  ( prop_applyMatchesImages
  , prop_applyMatchesImagesTensorCodomain
  , prop_tensorOfMapsActsFactorwise
  , prop_swapMapMatchesTranspose
  , prop_assocRoundTrip
  , prop_lassocMatchesNesting
  , prop_lunitClosesBoundary
  , prop_runitClosesBoundary
  , prop_unitRoundTrip
  , prop_conjugateMapMatchesEntrywise
  , prop_conjugateSiteMatchesCoeff
  , prop_daggerCnMatchesConjTranspose
  , prop_daggerSiteMatchesCoeff
  , runCategoricalProps
  ) where

import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗)
  , FiniteDimensional (..), SubBasis )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList, unwrap, konst))
import GHC.TypeLits (KnownNat)
import Data.Complex (Complex ((:+)), conjugate)
import Data.VectorSpace (VectorSpace ((*^)), sumV)
import Control.Monad (replicateM)
import qualified Data.Vector.Storable as VS
import qualified Test.QuickCheck as QC

import TensorNetwork.Categorical
  ( (⊗^), swapMap, lassocMap, rassocMap
  , lunit, lunitInv, runit, runitInv, conjugateMap )
import TensorNetwork.Dagger (dagger)
import TensorNetwork.MPS.Fixed3.Internal (Site (..), cdim, basis)
import TensorNetwork.MPS.Fixed3.Reference (siteCoeff)

--------------------------------------------------------------------------------
-- Generators (small Gaussian integers, exact arithmetic)
--------------------------------------------------------------------------------

smallComplex :: QC.Gen (Complex Double)
smallComplex = do
  r <- QC.elements [-2 .. 2 :: Int]
  i <- QC.elements [-2 .. 2 :: Int]
  pure (fromIntegral r :+ fromIntegral i)

genC :: forall n. KnownNat n => QC.Gen (C n)
genC = fromList <$> replicateM (cdim @n) smallComplex

-- | Random @C n +> C m@ in the canonical basis.
genMap :: forall n m. (KnownNat n, KnownNat m) => QC.Gen (C n +> C m)
genMap = do
  imgs <- replicateM (cdim @n) (genC @m)
  pure (fst (recomposeLinMap (entireBasis :: SubBasis (C n)) imgs))

-- | Random site-shaped map @(C bl ⊗ C p) +> C br@.
genSiteMap
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br)
  => QC.Gen ((C bl ⊗ C p) +> C br)
genSiteMap = do
  imgs <- replicateM (cdim @bl * cdim @p) (genC @br)
  pure (fst (recomposeLinMap (entireBasis :: SubBasis (C bl ⊗ C p)) imgs))

--------------------------------------------------------------------------------
-- Monoidal product, braiding, associators, unitors
--------------------------------------------------------------------------------

-- | Show-free exact equality (the tensor/map spaces have 'Eq' but no 'Show').
(=~=) :: Eq a => a -> a -> QC.Property
x =~= y = QC.property (x == y)
infix 4 =~=

-- | Foundational absolute oracle: a map recomposed from a list of images
-- applies basis vectors to exactly those images. Relative properties (same
-- bug on both sides) cannot catch a conjugating 'applyLinear'; this can.
prop_applyMatchesImages :: QC.Property
prop_applyMatchesImages =
  QC.forAll (replicateM 2 (genC @3)) $ \imgs ->
    let m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
    in QC.conjoin
         [ (m $ basis @2 j) QC.=== (imgs !! j) | j <- [0, 1] ]

-- | Same, with a tensor codomain (exercises the co-lexicographic layout of
-- @toArray@ \/ @unsafeFromArray@ on @C n ⊗ w@).
prop_applyMatchesImagesTensorCodomain :: QC.Property
prop_applyMatchesImagesTensorCodomain =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
          :: C 2 +> (C 3 ⊗ C 2)
    in QC.conjoin
         [ (m $ basis @2 j) =~= (imgs !! j) | j <- [0, 1] ]

-- | @(f ⊗^ g) (x ⊗ y) = f x ⊗ g y@ — the defining equation, on random
-- vectors (sufficient by bilinearity of ⊗ and linearity of the maps).
prop_tensorOfMapsActsFactorwise :: QC.Property
prop_tensorOfMapsActsFactorwise =
  QC.forAll (QC.Blind <$> genMap @2 @3) $ \(QC.Blind f) ->
  QC.forAll (QC.Blind <$> genMap @3 @2) $ \(QC.Blind g) ->
  QC.forAll (genC @2) $ \x ->
  QC.forAll (genC @3) $ \y ->
    ((f ⊗^ g) $ (x ⊗ y)) =~= ((f $ x) ⊗ (g $ y))

-- | @swapMap (x ⊗ y) = y ⊗ x@.
prop_swapMapMatchesTranspose :: QC.Property
prop_swapMapMatchesTranspose =
  QC.forAll (genC @2) $ \x ->
  QC.forAll (genC @3) $ \y ->
    (swapMap $ (x ⊗ y)) =~= (y ⊗ x)

-- | @lassocMap (x ⊗ (y ⊗ z)) = (x ⊗ y) ⊗ z@.
prop_lassocMatchesNesting :: QC.Property
prop_lassocMatchesNesting =
  QC.forAll (genC @2) $ \x ->
  QC.forAll (genC @3) $ \y ->
  QC.forAll (genC @2) $ \z ->
    (lassocMap $ (x ⊗ (y ⊗ z))) =~= ((x ⊗ y) ⊗ z)

-- | 'rassocMap' inverts 'lassocMap'.
prop_assocRoundTrip :: QC.Property
prop_assocRoundTrip =
  QC.forAll (genC @2) $ \x ->
  QC.forAll (genC @3) $ \y ->
  QC.forAll (genC @2) $ \z ->
    (rassocMap $ (lassocMap $ (x ⊗ (y ⊗ z))))
      =~= (x ⊗ (y ⊗ z))

-- | @lunit (c ⊗ v) = c₀ · v@ where @c₀@ is the single coordinate of @c : C 1@.
prop_lunitClosesBoundary :: QC.Property
prop_lunitClosesBoundary =
  QC.forAll (genC @1) $ \c ->
  QC.forAll (genC @3) $ \v ->
    (lunit $ (c ⊗ v)) QC.=== ((unwrap c VS.! 0) *^ v)

-- | @runit (v ⊗ c) = c₀ · v@.
prop_runitClosesBoundary :: QC.Property
prop_runitClosesBoundary =
  QC.forAll (genC @1) $ \c ->
  QC.forAll (genC @3) $ \v ->
    (runit $ (v ⊗ c)) QC.=== ((unwrap c VS.! 0) *^ v)

-- | The unitors invert their inverses.
prop_unitRoundTrip :: QC.Property
prop_unitRoundTrip =
  QC.forAll (genC @3) $ \v ->
    QC.conjoin
      [ (lunit $ (lunitInv $ v)) QC.=== v
      , (runit $ (runitInv $ v)) QC.=== v
      , (lunitInv $ v) =~= ((konst 1 :: C 1) ⊗ v)
      , (runitInv $ v) =~= (v ⊗ (konst 1 :: C 1))
      ]

--------------------------------------------------------------------------------
-- Conjugation and dagger (the ROADMAP §4a step-5 regression suite)
--------------------------------------------------------------------------------

-- | 'conjugateMap' on @C n +> C m@ conjugates the action on (real) basis
-- vectors entry-wise.
prop_conjugateMapMatchesEntrywise :: QC.Property
prop_conjugateMapMatchesEntrywise =
  QC.forAll (QC.Blind <$> genMap @2 @3) $ \(QC.Blind m) ->
  QC.forAll (QC.choose (0, 1)) $ \j ->
    (conjugateMap m $ basis @2 j)
      QC.=== fromList (map conjugate (VS.toList (unwrap (m $ basis @2 j))))

-- | 'conjugateMap' on a site map @(C bl ⊗ C p) +> C br@ conjugates every
-- stored coefficient — i.e. 'vectorConjugate' respects the backend layout.
prop_conjugateSiteMatchesCoeff :: QC.Property
prop_conjugateSiteMatchesCoeff =
  QC.forAll (QC.Blind <$> genSiteMap @2 @2 @2) $ \(QC.Blind m) ->
  QC.forAll (QC.choose (0, 1)) $ \l ->
  QC.forAll (QC.choose (0, 1)) $ \s ->
  QC.forAll (QC.choose (0, 1)) $ \r ->
    siteCoeff @2 @2 @2 (Site (conjugateMap m)) l s r
      QC.=== conjugate (siteCoeff @2 @2 @2 (Site m) l s r)

-- | @dagger m@ on @C n +> C m@ is the conjugate transpose:
-- @(dagger m) e_i = Σ_j conj(m_{i j}) e_j@ where @m_{i j} = (m e_j)_i@.
prop_daggerCnMatchesConjTranspose :: QC.Property
prop_daggerCnMatchesConjTranspose =
  QC.forAll (QC.Blind <$> genMap @2 @3) $ \(QC.Blind m) ->
  QC.forAll (QC.choose (0, 2)) $ \i ->
    (dagger m $ basis @3 i)
      QC.=== fromList
              [ conjugate (unwrap (m $ basis @2 j) VS.! i)
              | j <- [0 .. 1] ]

-- | Site †: @(dagger f) e_r = Σ_{l,s} conj(f[(l,s) → r]) (e_l ⊗ e_s)@.
prop_daggerSiteMatchesCoeff :: QC.Property
prop_daggerSiteMatchesCoeff =
  QC.forAll (QC.Blind <$> genSiteMap @2 @2 @2) $ \(QC.Blind f) ->
  QC.forAll (QC.choose (0, 1)) $ \r ->
    (dagger f $ basis @2 r)
      =~= sumV
              [ conjugate (siteCoeff @2 @2 @2 (Site f) l s r)
                  *^ (basis @2 l ⊗ basis @2 s)
              | l <- [0 .. 1], s <- [0 .. 1] ]

-- | Run all properties (for GHCi / the test executable).
runCategoricalProps :: IO ()
runCategoricalProps = do
  putStrLn "recomposed map applies basis to its images..."
  QC.quickCheck prop_applyMatchesImages
  putStrLn "... also with tensor codomain..."
  QC.quickCheck prop_applyMatchesImagesTensorCodomain
  putStrLn "tensorOfMaps acts factorwise..."
  QC.quickCheck prop_tensorOfMapsActsFactorwise
  putStrLn "swapMap matches transposeTensor..."
  QC.quickCheck prop_swapMapMatchesTranspose
  putStrLn "lassocMap matches nesting..."
  QC.quickCheck prop_lassocMatchesNesting
  putStrLn "associators round-trip..."
  QC.quickCheck prop_assocRoundTrip
  putStrLn "lunit closes the boundary..."
  QC.quickCheck prop_lunitClosesBoundary
  putStrLn "runit closes the boundary..."
  QC.quickCheck prop_runitClosesBoundary
  putStrLn "unitors round-trip..."
  QC.quickCheck prop_unitRoundTrip
  putStrLn "conjugateMap conjugates entrywise (C n +> C m)..."
  QC.quickCheck prop_conjugateMapMatchesEntrywise
  putStrLn "conjugateMap respects site layout (vectorConjugate regression)..."
  QC.quickCheck prop_conjugateSiteMatchesCoeff
  putStrLn "dagger is the conjugate transpose (C n +> C m)..."
  QC.quickCheck prop_daggerCnMatchesConjTranspose
  putStrLn "site dagger matches coefficient oracle..."
  QC.quickCheck prop_daggerSiteMatchesCoeff
