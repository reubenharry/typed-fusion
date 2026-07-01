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
  , prop_tensorOfMapsActsFactorwiseSiteDomain
  , prop_tensorOfMapsActsFactorwiseLeftFactored
  , prop_tensorOfMapsBasisImages
  , prop_tensorOfMapsRecomposeRoundtrip
  , prop_swapMapMatchesTranspose
  , prop_assocRoundTrip
  , prop_lassocMatchesNesting
  , prop_lunitClosesBoundary
  , prop_runitClosesBoundary
  , prop_unitRoundTrip
  , prop_conjugateMapMatchesEntrywise
  , prop_conjugateSiteMatchesCoeff
  , prop_daggerCnMatchesConjTranspose
  , prop_siteDaggerPullbackMatchesCoeff
  , prop_siteDaggerRecomposeAppliesImages
  , prop_tensorToArrayRoundtrip
  , prop_rowSliceMatchesImage
  , prop_flattenRowMatchesToRows
  , prop_inlineRowSumApply
  , prop_codomainIsStatic
  , prop_sliceVsExplicitDecode
  , prop_manualApplyMatchesImg
  , prop_manualRowMatchesImg
  , prop_applyLinearOnly
  , prop_arrApplyOnly
  , prop_dollarApplyOnly
  , prop_matvecMatchesStoredRow
  , prop_rowUnsafeFromArrayRoundtrip
  , prop_recomposeRowsMatchToArray
  , prop_applyTensorFlatMatchesRow
  , prop_recomposeDecomposeTensorCodomain
  , prop_recomposeAppliesImagesTensor22
  , prop_siteDaggerBasisMatchesPullback
  , prop_flatAdjMatchesIsoImages
  , prop_siteTensorIsoOnPullback
  , prop_composedFlatIsoApply
  , prop_siteDaggerIsoRoundtrip
  , prop_daggerSiteMatchesCoeff
  , prop_siteTensorIsoRoundtrip
  , prop_flatBasisMatchesTensor
  , prop_flatSiteApplyMatchesApplySite
  , runCategoricalProps
  ) where

import Prelude hiding (($), (.), id)
import Control.Category.Constrained (id, (.))
import Control.Arrow.Constrained (arr)
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗)
  , FiniteDimensional (..), SubBasis, decomposeLinMap
  , getLinearMap, LinearMap (..), applyLinear, getLinearFunction, (-+$>) )
import Math.VectorSpace.DimensionAware
  ( toArray, unsafeFromArray, dimensionality, DimensionalityCases(..)
  , unsafeFromArrayWithOffset, StaticDimensional )
import qualified Numeric.LinearAlgebra.HMatrix as HM
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList, unwrap, create, konst), extract)
import Data.Maybe (fromJust)
import GHC.TypeLits (KnownNat, type (*))
import Data.Complex (Complex ((:+)), conjugate)
import Data.VectorSpace (VectorSpace ((*^)), sumV)
import Control.Monad (replicateM)
import qualified Data.Vector.Storable as VS
import qualified Test.QuickCheck as QC

import TensorNetwork.Categorical
  ( (⊗^), swapMap, lassocMap, rassocMap
  , lunit, lunitInv, runit, runitInv, conjugateMap )
import TensorNetwork.Dagger (dagger, siteDagger, siteDaggerVec, siteTensorIso, siteTensorIsoInv, siteTensorIsoFlat)
import TensorNetwork.MPS.LinmapStorage
  ( linMapFromColumnImages, siteLinFromRows )
import TensorNetwork.MPS.Fixed3.Internal (Site (..), cdim, basis, one1)
import TensorNetwork.MPS.Fixed3.Reference (siteCoeff, applySite)

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

-- | Random site-shaped map @(C bl ⊗ C p) +> C br@ (column storage).
genSiteMap
  :: forall bl p br
   . (KnownNat bl, KnownNat p, KnownNat br, KnownNat (bl * p), KnownNat (p * br))
  => QC.Gen ((C bl ⊗ C p) +> C br)
genSiteMap =
  siteLinFromRows <$> replicateM (cdim @bl * cdim @p) (genC @br)

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

-- | Same law on full domain basis (not just random @x@, @y@).
prop_tensorOfMapsBasisImages :: QC.Property
prop_tensorOfMapsBasisImages =
  QC.forAll (QC.Blind <$> genMap @2 @3) $ \(QC.Blind f) ->
  QC.forAll (QC.Blind <$> genMap @3 @2) $ \(QC.Blind g) ->
    QC.conjoin
      [ ((f ⊗^ g) $ (bu ⊗ bv)) =~= ((f $ bu) ⊗ (g $ bv))
      | bu <- enumerateSubBasis (entireBasis :: SubBasis (C 2))
      , bv <- enumerateSubBasis (entireBasis :: SubBasis (C 3))
      ]

-- | 'recomposeLinMap' roundtrip on Kronecker basis images.
prop_tensorOfMapsRecomposeRoundtrip :: QC.Property
prop_tensorOfMapsRecomposeRoundtrip =
  QC.forAll (QC.Blind <$> genMap @2 @3) $ \(QC.Blind f) ->
  QC.forAll (QC.Blind <$> genMap @3 @2) $ \(QC.Blind g) ->
    let expected =
          [ (f $ bu) ⊗ (g $ bv)
          | bu <- enumerateSubBasis (entireBasis :: SubBasis (C 2))
          , bv <- enumerateSubBasis (entireBasis :: SubBasis (C 3))
          ]
        fg = fst (recomposeLinMap (entireBasis :: SubBasis (C 2 ⊗ C 3)) expected)
        (_, decomp) = decomposeLinMap fg
        got = decomp []
    in QC.conjoin (zipWith (=~=) got expected)

-- | Same law when the left domain is itself a tensor @C bl ⊗ C p@ (MPS left leg).
prop_tensorOfMapsActsFactorwiseSiteDomain :: QC.Property
prop_tensorOfMapsActsFactorwiseSiteDomain =
  QC.forAll (QC.Blind <$> genSiteMap @1 @2 @2) $ \(QC.Blind f) ->
  QC.forAll (QC.choose (0, 1)) $ \s1 ->
  QC.forAll (QC.choose (0, 1)) $ \s2 ->
    let x = one1 ⊗ basis @2 s1
        y = basis @2 s2
    in ((f ⊗^ idC2) $ (x ⊗ y)) =~= ((f $ x) ⊗ y)
  where
    idC2 :: C 2 +> C 2
    idC2 = id

-- | Same law for left sites stored as @C p +> C b@ and applied via 'lunit'
-- (the FinSupp3 / TT-SVD factorisation shape).
prop_tensorOfMapsActsFactorwiseLeftFactored :: QC.Property
prop_tensorOfMapsActsFactorwiseLeftFactored =
  QC.forAll (QC.Blind <$> genMap @2 @2) $ \(QC.Blind l) ->
  QC.forAll (QC.choose (0, 1)) $ \s1 ->
  QC.forAll (QC.choose (0, 1)) $ \s2 ->
    let f = l . lunit @(C 2)
        x = one1 ⊗ basis @2 s1
        y = basis @2 s2
    in ((f ⊗^ idC2) $ (x ⊗ y)) =~= ((f $ x) ⊗ y)
  where
    idC2 :: C 2 +> C 2
    idC2 = id

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

-- | Flat bond index @l·p + s@ maps to the tensor basis @e_l ⊗ e_s@.
prop_flatBasisMatchesTensor :: QC.Property
prop_flatBasisMatchesTensor =
  QC.forAll (QC.choose (0, 1)) $ \l ->
  QC.forAll (QC.choose (0, 1)) $ \s ->
    let flatIdx = l * cdim @2 + s
    in (toArray (siteTensorIsoInv @2 @2 $ basis @4 flatIdx)
          == (toArray (basis @2 l ⊗ basis @2 s) :: VS.Vector (Complex Double)))

-- | Flattened application agrees with 'applySite'.
prop_flatSiteApplyMatchesApplySite :: QC.Property
prop_flatSiteApplyMatchesApplySite =
  QC.forAll (QC.Blind <$> genSiteMap @2 @2 @2) $ \(QC.Blind f) ->
  QC.forAll (QC.choose (0, 1)) $ \l ->
  QC.forAll (QC.choose (0, 1)) $ \s ->
    let flatIdx = l * cdim @2 + s
    in applySite (Site f) (basis @2 l) s
         =~= (f . siteTensorIsoInv @2 @2 $ basis @4 flatIdx)

-- | Flatten / unflatten round-trip on physical basis kets.
prop_siteTensorIsoRoundtrip :: QC.Property
prop_siteTensorIsoRoundtrip =
  QC.forAll (QC.choose (0, 1)) $ \l ->
  QC.forAll (QC.choose (0, 1)) $ \s ->
    (toArray (siteTensorIsoInv @2 @2 $ (siteTensorIso @2 @2 $ (basis @2 l ⊗ basis @2 s)))
       == (toArray (basis @2 l ⊗ basis @2 s) :: VS.Vector (Complex Double)))

-- | Pullback image before 'recomposeLinMap' matches the coefficient oracle.
prop_siteDaggerPullbackMatchesCoeff :: QC.Property
prop_siteDaggerPullbackMatchesCoeff =
  QC.forAll (QC.Blind <$> genSiteMap @2 @2 @2) $ \(QC.Blind f) ->
  QC.forAll (QC.choose (0, 1)) $ \r ->
    let bl = 2 :: Int
        p = 2 :: Int
        pullbackAt =
          sumV
            [ conjugate (unwrap (f $ (basis @2 l ⊗ basis @2 s)) VS.! r)
                *^ (basis @2 l ⊗ basis @2 s)
            | l <- [0 .. bl - 1], s <- [0 .. p - 1]
            ]
    in pullbackAt
         =~= sumV
               [ conjugate (siteCoeff @2 @2 @2 (Site f) l s r)
                   *^ (basis @2 l ⊗ basis @2 s)
               | l <- [0 .. 1], s <- [0 .. 1] ]

-- | 'siteDagger' on a bond basis vector matches the closed pullback sum.
prop_siteDaggerBasisMatchesPullback :: QC.Property
prop_siteDaggerBasisMatchesPullback =
  QC.forAll (QC.Blind <$> genSiteMap @2 @2 @2) $ \(QC.Blind f) ->
  QC.forAll (QC.choose (0, 1)) $ \r ->
    let bl = 2 :: Int
        p = 2 :: Int
        pullbackAt =
          sumV
            [ conjugate (unwrap (f $ (basis @2 l ⊗ basis @2 s)) VS.! r)
                *^ (basis @2 l ⊗ basis @2 s)
            | l <- [0 .. bl - 1], s <- [0 .. p - 1]
            ]
    in (siteDagger f $ basis @2 r) =~= pullbackAt

-- | @toArray@ / @fromArray@ roundtrip on @C a ⊗ C b@.
prop_tensorToArrayRoundtrip :: QC.Property
prop_tensorToArrayRoundtrip =
  QC.forAll (genC @3) $ \x ->
  QC.forAll (genC @2) $ \y ->
    let t = x ⊗ y
    in QC.property $
         let ar = toArray t
         in VS.toList ar
              == VS.toList (toArray (unsafeFromArray @(C 3 ⊗ C 2) ar))

-- | Row-slice decode matches the supplied tensor images.
prop_rowSliceMatchesImage :: QC.Property
prop_rowSliceMatchesImage =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
        linMap = getLinearMap m
    in QC.conjoin
         [ unsafeFromArray @(C 3 ⊗ C 2) (HM.fromList (HM.toList (HM.toColumns (extract linMap) !! j)))
             =~= (imgs !! j)
         | j <- [0, 1] ]

-- | @flatten (m ¿ [i])@ agrees with @toColumns m !! i@.
prop_flattenRowMatchesToRows :: QC.Property
prop_flattenRowMatchesToRows =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
        linMap = getLinearMap m
    in QC.conjoin
         [ HM.toList (HM.flatten (extract linMap HM.? [j]))
             QC.=== HM.toList (HM.toColumns (extract linMap) !! j)
         | j <- [0, 1] ]

-- | Inline row-sum apply matches per-row decode.
prop_inlineRowSumApply :: QC.Property
prop_inlineRowSumApply =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
        linMap = getLinearMap m
        manual j =
          unsafeFromArray @(C 3 ⊗ C 2)
            (HM.fromList (HM.toList (HM.toColumns (extract linMap) !! j)))
        inlineApply v =
          sumV
            [ (unwrap v VS.! i)
                *^ unsafeFromArray @(C 3 ⊗ C 2)
                     (HM.fromList (HM.toList (HM.toColumns (extract linMap) !! i)))
            | i <- [0, 1]
            ]
    in QC.conjoin
         [ inlineApply (basis @2 j) =~= manual j | j <- [0, 1] ]

-- | Branches of 'prop_applyLinearMatchesMatvec' for locating failures.
prop_codomainIsStatic :: QC.Property
prop_codomainIsStatic =
  case dimensionality @(C 3 ⊗ C 2) of
    StaticDimensionalCase -> QC.property True
    FlexibleDimensionalCase -> QC.property False

-- | Polymorphic 'unsafeFromArraySliceW' agrees with explicit @(C 3 ⊗ C 2)@ decode.
prop_sliceVsExplicitDecode :: QC.Property
prop_sliceVsExplicitDecode =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
        linMap = getLinearMap m
    in QC.conjoin
         [ let rowList = HM.toList (HM.toColumns (extract linMap) !! j)
               row = HM.fromList rowList
               explicit = unsafeFromArray @(C 3 ⊗ C 2) row
               slice = unsafeFromArrayWithOffset 0 (VS.fromList rowList)
           in (explicit =~= (imgs !! j)) QC..&&. (slice =~= explicit)
         | j <- [0, 1] ]

prop_manualApplyMatchesImg :: QC.Property
prop_manualApplyMatchesImg =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
        linMap = getLinearMap m
        rowImg j =
          unsafeFromArray @(C 3 ⊗ C 2)
            (HM.fromList (HM.toList (HM.toColumns (extract linMap) !! j)))
        manualApply v =
          sumV [ (unwrap v VS.! i) *^ rowImg i | i <- [0, 1] ]
    in QC.conjoin
         [ manualApply (basis @2 j) =~= (imgs !! j) | j <- [0, 1] ]

prop_manualRowMatchesImg :: QC.Property
prop_manualRowMatchesImg =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
        linMap = getLinearMap m
        manual j =
          unsafeFromArray @(C 3 ⊗ C 2)
            (HM.fromList (HM.toList (HM.toColumns (extract linMap) !! j)))
    in QC.conjoin [ manual j =~= (imgs !! j) | j <- [0, 1] ]

prop_applyLinearOnly :: QC.Property
prop_applyLinearOnly =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
           :: C 2 +> (C 3 ⊗ C 2)
    in QC.conjoin
         [ (getLinearFunction (applyLinear -+$> m) (basis @2 j)) =~= (imgs !! j)
         | j <- [0, 1] ]

prop_arrApplyOnly :: QC.Property
prop_arrApplyOnly =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
           :: C 2 +> (C 3 ⊗ C 2)
    in QC.conjoin [ (arr m (basis @2 j)) =~= (imgs !! j) | j <- [0, 1] ]

prop_dollarApplyOnly :: QC.Property
prop_dollarApplyOnly =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
           :: C 2 +> (C 3 ⊗ C 2)
    in QC.conjoin [ (m $ basis @2 j) =~= (imgs !! j) | j <- [0, 1] ]

-- | @arr@ / @getLinearFunction (applyLinear m)@ agree with flat matvec path.
prop_applyLinearMatchesMatvec :: QC.Property
prop_applyLinearMatchesMatvec =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
           :: C 2 +> (C 3 ⊗ C 2)
        linMap = getLinearMap m
        manual j =
          unsafeFromArray @(C 3 ⊗ C 2)
            (HM.fromList (HM.toList (HM.toColumns (extract linMap) !! j)))
        inlineApply v =
          sumV
            [ (unwrap v VS.! i)
                *^ unsafeFromArray @(C 3 ⊗ C 2)
                     (HM.fromList (HM.toList (HM.toColumns (extract linMap) !! i)))
            | i <- [0, 1]
            ]
    in QC.conjoin
         $ concat
             [ [ VS.toList (toArray (arr m (basis @2 j)))
                   QC.=== VS.toList (toArray (manual j))
               , VS.toList (toArray (getLinearFunction (applyLinear -+$> m) (basis @2 j)))
                   QC.=== VS.toList (toArray (manual j))
               , VS.toList (toArray (m $ basis @2 j))
                   QC.=== VS.toList (toArray (manual j))
               , VS.toList (toArray (inlineApply (basis @2 j)))
                   QC.=== VS.toList (toArray (manual j))
               ]
             | j <- [0, 1]
             ]

-- | @#>@ on storage matches the stored column (no conjugation).
prop_matvecMatchesStoredRow :: QC.Property
prop_matvecMatchesStoredRow =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
        linMap = getLinearMap m
    in QC.conjoin
         [ let col = HM.toList (HM.toColumns (extract linMap) !! j)
               flat = HM.toList (extract linMap HM.#> extract (basis @2 j))
           in flat QC.=== col
         | j <- [0, 1] ]

-- | Flat row from storage roundtrips through @unsafeFromArray@ on the codomain.
prop_rowUnsafeFromArrayRoundtrip :: QC.Property
prop_rowUnsafeFromArrayRoundtrip =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
        linMap = getLinearMap m
    in QC.conjoin
         [ let row = HM.toList (HM.toColumns (extract linMap) !! j)
           in VS.toList (toArray (unsafeFromArray @(C 3 ⊗ C 2) (HM.fromList row)))
                QC.=== row
         | j <- [0, 1] ]

-- | Matrix rows after recompose match @toArray@ of the supplied images.
prop_recomposeRowsMatchToArray :: QC.Property
prop_recomposeRowsMatchToArray =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
        linMap = getLinearMap m
        rowFlat j = HM.toList (HM.toColumns (extract linMap) !! j)
    in QC.conjoin
         [ rowFlat j QC.=== VS.toList (toArray (imgs !! j)) | j <- [0, 1] ]

-- | Applied flat coefficients match stored row ('applyLinear' diagnostic).
prop_applyTensorFlatMatchesRow :: QC.Property
prop_applyTensorFlatMatchesRow =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
    in QC.conjoin
         [ VS.toList (toArray (m $ basis @2 j))
             QC.=== VS.toList (toArray (imgs !! j))
         | j <- [0, 1] ]

-- | Decompose after recompose recovers tensor-codomain images.
prop_recomposeDecomposeTensorCodomain :: QC.Property
prop_recomposeDecomposeTensorCodomain =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
        (_, decomp) = decomposeLinMap m
        got = decomp []
    in QC.conjoin (zipWith (=~=) got imgs)

-- | 'siteDagger' applies pullback images (column storage, no 'recomposeLinMap').
prop_siteDaggerRecomposeAppliesImages :: QC.Property
prop_siteDaggerRecomposeAppliesImages =
  QC.forAll (QC.Blind <$> genSiteMap @2 @2 @2) $ \(QC.Blind f) ->
    QC.conjoin
      [ (siteDagger f $ basis @2 r) =~= siteDaggerVec f (basis @2 r)
      | r <- [0, 1] ]

-- | Same with @C 2 +> (C 3 ⊗ C 2)@ control (known-good codomain shape).
prop_recomposeAppliesImagesTensor22 :: QC.Property
prop_recomposeAppliesImagesTensor22 =
  QC.forAll (replicateM 2 (genC @3)) $ \xs ->
  QC.forAll (replicateM 2 (genC @2)) $ \ys ->
    let imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
        m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
          :: C 2 +> (C 3 ⊗ C 2)
    in QC.conjoin [ (m $ basis @2 j) =~= (imgs !! j) | j <- [0, 1] ]

-- | Flat @C br +> C (bl·p)@ step of 'siteDagger' applies stored iso-flat images.
prop_flatAdjMatchesIsoImages :: QC.Property
prop_flatAdjMatchesIsoImages =
  QC.forAll (QC.Blind <$> genSiteMap @2 @2 @2) $ \(QC.Blind f) ->
    let br = 2 :: Int
        cBasis i = basis @2 i
        flatImgs =
          [ siteTensorIsoFlat @2 @2 (siteDaggerVec f (cBasis r)) | r <- [0, 1] ]
        flatAdj =
          linMapFromColumnImages @2 @4 flatImgs
    in QC.conjoin
         [ (flatAdj $ cBasis r) QC.=== (flatImgs !! r) | r <- [0, 1] ]

-- | Iso round-trip on pullback tensors (not only basis kets).
prop_siteTensorIsoOnPullback :: QC.Property
prop_siteTensorIsoOnPullback =
  QC.forAll (QC.Blind <$> genSiteMap @2 @2 @2) $ \(QC.Blind f) ->
  QC.forAll (QC.choose (0, 1)) $ \r ->
    let t = siteDaggerVec f (basis @2 r)
    in (siteTensorIsoInv @2 @2 $ (siteTensorIso @2 @2 $ t)) =~= t

-- | Composed iso∘flat applies as one morphism (may differ from two-step).
prop_composedFlatIsoApply :: QC.Property
prop_composedFlatIsoApply =
  QC.forAll (QC.Blind <$> genSiteMap @2 @2 @2) $ \(QC.Blind f) ->
  QC.forAll (QC.choose (0, 1)) $ \r ->
    let br = 2 :: Int
        cBasis i = basis @2 i
        flatImgs =
          [ siteTensorIsoFlat @2 @2 (siteDaggerVec f (cBasis i)) | i <- [0, 1] ]
        flatAdj =
          linMapFromColumnImages @2 @4 flatImgs
        composed = siteTensorIsoInv @2 @2 . flatAdj
        stepped = siteTensorIsoInv @2 @2 $ (flatAdj $ cBasis r)
    in (composed $ cBasis r) =~= stepped

-- | Full 'siteDagger' applies after iso unflatten.
prop_siteDaggerIsoRoundtrip :: QC.Property
prop_siteDaggerIsoRoundtrip =
  QC.forAll (QC.Blind <$> genSiteMap @2 @2 @2) $ \(QC.Blind f) ->
  QC.forAll (QC.choose (0, 1)) $ \r ->
    (siteDagger f $ basis @2 r)
      =~= siteDaggerVec f (basis @2 r)

-- | Site †: @(siteDagger f) e_r = Σ_{l,s} conj(f[(l,s) → r]) (e_l ⊗ e_s)@.
prop_daggerSiteMatchesCoeff :: QC.Property
prop_daggerSiteMatchesCoeff =
  QC.forAll (QC.Blind <$> genSiteMap @2 @2 @2) $ \(QC.Blind f) ->
  QC.forAll (QC.choose (0, 1)) $ \r ->
    (siteDagger f $ basis @2 r)
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
