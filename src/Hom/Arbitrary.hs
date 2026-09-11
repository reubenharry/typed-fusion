{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | QuickCheck generators for unfused 'ToVObj' and fused 'FTreeV'.
--
-- @C n@ and 'FTreeV' have ordinary 'Arbitrary' instances. 'ToVObj' is a type
-- family (and @⊗@ is too), so unfused trees use 'ArbitraryObj' \/ 'AsObj'
-- instead of @Arbitrary (ToVObj g a)@.
module Hom.Arbitrary
  ( Arbitrary (..)
  , genComplexBounded
  , ArbitraryObj (..)
  , AsObj (..)
  , genSU2Element
  ) where

import Control.Applicative (liftA2)
import Control.Monad (replicateM)
import Data.Complex (Complex (..))
import Data.Maybe (fromJust, fromMaybe)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (AdditiveGroup ((^+^)))
import qualified Data.Vector.Storable as VS
import Fusion.Obj (Obj (Irrep, (:⊗:), (:⊕:)))
import GHC.TypeLits (KnownNat, natVal)
import Hom.Core (KnownToVObj)
import Hom.Expr (FTrees)
import Hom.FTreeV (FTreeV (..))
import Hom.Singletons (KnownFTree, KnownRoot)
import Hom.TypeLevel (IrrepDim, Root, ToVObj, ToVTree)
import Math.LinearMap.Category (TensorSpace, type (⊗), (⊗))
import Numeric.LinearAlgebra.Static (C, Sized (create, extract))
import Symmetry.Group (Group (..), Irreps)
import Symmetry.SU2 (SU2Element, su2FromQuaternion)
import Symmetry.Utils (KnownZ)
import Test.QuickCheck (Arbitrary (..), Gen, choose, chooseInt, shrinkList, suchThat)

-- | Bounded complex coords (avoids QuickCheck's huge \/ NaN 'Double's).
genComplexBounded :: Gen (Complex Double)
genComplexBounded = liftA2 (:+) (choose (-1, 1)) (choose (-1, 1))

-- | Uniform-ish draw on @S³ ≅ SU(2)@ via a non-zero quaternion.
genSU2Element :: Gen SU2Element
genSU2Element = do
  (w, x, y, z) <-
    suchThat
      ((,,,) <$> choose (-1, 1) <*> choose (-1, 1) <*> choose (-1, 1) <*> choose (-1, 1))
      (\(w, x, y, z) -> w * w + x * x + y * y + z * z > 1e-8)
  pure (fromJust (su2FromQuaternion w x y z))

instance Arbitrary SU2Element where
  arbitrary = genSU2Element
  shrink _ = []

--------------------------------------------------------------------------------
-- Static irrep carriers
--------------------------------------------------------------------------------

instance KnownNat n => Arbitrary (C n) where
  arbitrary = do
    let n = fromIntegral (natVal (Proxy @n))
    xs <- replicateM n genComplexBounded
    pure $
      fromMaybe (error "Hom.Arbitrary: C n create failed")
        (create (VS.fromList xs))
  shrink v =
    [ fromMaybe v (create (VS.fromList ys))
    | ys <- shrinkList (\_ -> []) (VS.toList (extract v))
    ]

--------------------------------------------------------------------------------
-- Unfused Obj trees (ToVObj is a type family — use ArbitraryObj / AsObj)
--------------------------------------------------------------------------------

-- | Generate a random vector in 'ToVObj' @g a@.
class KnownToVObj g a => ArbitraryObj (g :: Group) (a :: Obj (Irreps g)) where
  arbitraryObj :: Gen (ToVObj g a)
  shrinkObj :: ToVObj g a -> [ToVObj g a]
  shrinkObj _ = []

-- | Newtype so @arbitrary @(AsObj g a)@ works at call sites.
newtype AsObj (g :: Group) (a :: Obj (Irreps g)) = AsObj
  { getObj :: ToVObj g a
  }

instance ArbitraryObj g a => Arbitrary (AsObj g a) where
  arbitrary = AsObj <$> arbitraryObj @g @a
  shrink (AsObj v) = AsObj <$> shrinkObj @g @a v

-- SU(2) ----------------------------------------------------------------------

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  ArbitraryObj SU2 ('Irrep j)
  where
  arbitraryObj = arbitrary @(C (IrrepDim j))
  shrinkObj = shrink @(C (IrrepDim j))

instance
  ( ArbitraryObj SU2 a
  , ArbitraryObj SU2 b
  , TensorSpace (ToVObj SU2 a)
  , TensorSpace (ToVObj SU2 b)
  , AdditiveGroup (ToVObj SU2 a ⊗ ToVObj SU2 b)
  ) =>
  ArbitraryObj SU2 (a :⊗: b)
  where
  arbitraryObj = do
    k <- chooseInt (1, 4)
    terms <-
      replicateM k $
        liftA2 (⊗) (arbitraryObj @SU2 @a) (arbitraryObj @SU2 @b)
    pure (foldl1 (^+^) terms)

instance
  ( ArbitraryObj SU2 a
  , ArbitraryObj SU2 b
  ) =>
  ArbitraryObj SU2 (a :⊕: b)
  where
  arbitraryObj = liftA2 (,) (arbitraryObj @SU2 @a) (arbitraryObj @SU2 @b)
  shrinkObj (x, y) =
    [ (x', y') | x' <- shrinkObj @SU2 @a x, y' <- shrinkObj @SU2 @b y ]

-- U(1) -----------------------------------------------------------------------

instance KnownZ j => ArbitraryObj U1 ('Irrep j) where
  arbitraryObj = arbitrary @(C 1)
  shrinkObj = shrink @(C 1)

instance
  ( ArbitraryObj U1 a
  , ArbitraryObj U1 b
  , TensorSpace (ToVObj U1 a)
  , TensorSpace (ToVObj U1 b)
  , AdditiveGroup (ToVObj U1 a ⊗ ToVObj U1 b)
  ) =>
  ArbitraryObj U1 (a :⊗: b)
  where
  arbitraryObj = do
    k <- chooseInt (1, 4)
    terms <-
      replicateM k $
        liftA2 (⊗) (arbitraryObj @U1 @a) (arbitraryObj @U1 @b)
    pure (foldl1 (^+^) terms)

instance
  ( ArbitraryObj U1 a
  , ArbitraryObj U1 b
  ) =>
  ArbitraryObj U1 (a :⊕: b)
  where
  arbitraryObj = liftA2 (,) (arbitraryObj @U1 @a) (arbitraryObj @U1 @b)
  shrinkObj (x, y) =
    [ (x', y') | x' <- shrinkObj @U1 @a x, y' <- shrinkObj @U1 @b y ]

--------------------------------------------------------------------------------
-- Fused genealogy spines
--------------------------------------------------------------------------------

instance Arbitrary (FTreeV ('[] :: FTrees lab)) where
  arbitrary = pure FNil
  shrink _ = []

instance
  ( KnownFTree t
  , KnownRoot (Root t)
  , Arbitrary (ToVTree t)
  , Arbitrary (FTreeV rest)
  ) =>
  Arbitrary (FTreeV (t ': rest))
  where
  arbitrary = liftA2 FCons arbitrary arbitrary
  shrink (FCons v rest) =
    [ FCons v' rest' | v' <- shrink v, rest' <- shrink rest ]
