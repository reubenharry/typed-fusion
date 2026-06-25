{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | U(1) forgetful functor with an unfused tensor-product object.
--
-- Objects are either a reduced rep spine @'Rep r@ or an unfused product
-- @'Prod r q@ (the external tensor product, not regrouped by total charge).
-- Morphisms are intertwiners on reduced reps, plus 'Fuse' from a product to
-- its fused spine @'TensorU1 r q@.
--
-- The forgetful functor maps
--
-- @
--   'Prod r q'  |->  C (RepDim r) ⊗ C (RepDim q)
--   'Rep r'     |->  C (RepDim r)
-- @
--
-- so @fmap fuse@ has type @(C 1 ⊗ C 1) -+> C 1@ for two charge-@1@ irreps.
module Symmetry.FunctorU1
  ( U1Obj (..)
  , U1Mor (..)
  , U1Rep
  , TensorU1
  , RepDim
  , IsIrrep1
  , fuse
  , Forget
  , ForgetTag (..)
  , fuseLinear
  , demoFmapFuse
  ) where

import Prelude hiding ((.), id, Functor (..), ($))
import Control.Arrow.Constrained (($))
import Control.Category.Constrained (Category (..))
import Control.Functor.Constrained (Functor (..))
import Data.Coerce (coerce)
import Data.Complex (Complex)
import Unsafe.Coerce (unsafeCoerce)
import Data.Kind (Type)
import Data.Singletons (sing)
import GHC.TypeLits (KnownNat, Nat)
import Math.LinearMap.Category
  ( type (⊗), LinearFunction (..), TensorSpace (..)
  , AdditiveGroup (..), VectorSpace (..), InnerSpace (..)
  , DimensionAware (..), Semimanifold (..), PseudoAffine (..) )
import Math.LinearMap.Asserted (getLinearFunction, linearFunction, type (-+>))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.VectorSpace.DimensionAware
  (Dimensional (..), unsafeFromArrayWithOffset, unsafeWriteArrayWithOffset)
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C)
import Symmetry.FunctorExperiment
  ( Intertwiner (..), compose, mkIdHom, intertwinerLinear
  , U1RepList, ApplyIntertwiner (..), ToC (..), RepDim, U1Rep
  , BuildIdHom, HomSectorList
  )
import Symmetry.Group (Group (U1))
import Symmetry.RepSingleton (KnownRep)
import Symmetry.Utils (Z (..), Add, Append, Scale)
import TensorNetwork.Categorical (lunit)

-- | A single charge with multiplicity @1@.
type family IsIrrep1 (r :: U1Rep) :: Bool where
  IsIrrep1 ('(z, 1) ': '[]) = 'True
  IsIrrep1 _                 = 'False

-- | Recover @RepDim ~ 1@ from @IsIrrep1 r ~ 'True@.
type family RepDimOfIrrep1 (ok :: Bool) :: Nat where
  RepDimOfIrrep1 'True  = 1
  RepDimOfIrrep1 'False = 0

-- | Fused dimension when both factors are single-sector irreps.
type family FusedIrrep1Dim (ok1 :: Bool) (ok2 :: Bool) :: Nat where
  FusedIrrep1Dim 'True 'True = 1
type family TensorU1 (r :: U1Rep) (q :: U1Rep) :: U1Rep where
  TensorU1 '[] _ = '[]
  TensorU1 ('(i, m) ': rs) q =
    Append (TensorU1One '(i, m) q) (TensorU1 rs q)

type family TensorU1One (x :: (Z, Nat)) (q :: U1Rep) :: U1Rep where
  TensorU1One _ '[] = '[]
  TensorU1One '(i, m) ('(j, n) ': qs) =
    '(Add i j, Scale m n) ': TensorU1One '(i, m) qs

-- | Object of the U(1) rep category: reduced spine or unfused product.
data U1Obj where
  Rep  :: U1Rep -> U1Obj
  Prod :: U1Rep -> U1Rep -> U1Obj

-- | Morphisms: intertwiners on reduced reps, and fusion from a product.
data U1Mor (a :: U1Obj) (b :: U1Obj) where
  RepInter
    :: Intertwiner r q
    -> U1Mor ('Rep r) ('Rep q)
  Fuse
    :: U1Mor ('Prod r q) ('Rep (TensorU1 r q))

-- | Canonical fusion @r ⊗ q -> TensorU1 r q@ (U(1), single-sector factors).
fuse
  :: forall r q.
     ( IsIrrep1 r ~ 'True, IsIrrep1 q ~ 'True
     , U1RepList r, U1RepList q
     , KnownNat (RepDim r), KnownNat (RepDim q)
     , KnownNat (RepDim (TensorU1 r q))
     )
  => U1Mor ('Prod r q) ('Rep (TensorU1 r q))
fuse = Fuse

-- | Image of the forgetful functor.
type family Forget (o :: U1Obj) :: Type where
  Forget ('Rep r)     = C (RepDim r)
  Forget ('Prod r q) = C (RepDim r) ⊗ C (RepDim q)

-- | Tagged wrapper so @'ForgetTag'@ can index the constrained functor.
newtype ForgetTag (o :: U1Obj) = ForgetTag { unForgetTag :: Forget o }

-- | Fusion on underlying spaces (@C 1 ⊗ C 1 -> C 1@ for single-sector factors).
fuseLinear
  :: forall r q.
     ( IsIrrep1 r ~ 'True, IsIrrep1 q ~ 'True
     , RepDim r ~ RepDimOfIrrep1 (IsIrrep1 r)
     , RepDim q ~ RepDimOfIrrep1 (IsIrrep1 q)
     , RepDim (TensorU1 r q) ~ FusedIrrep1Dim (IsIrrep1 r) (IsIrrep1 q)
     , KnownNat (RepDim r), KnownNat (RepDim q)
     , KnownNat (RepDim (TensorU1 r q))
     )
  => LinearFunction (Complex Double) (ForgetTag ('Prod r q)) (ForgetTag ('Rep (TensorU1 r q)))
fuseLinear =
  linearFunction $ \(ForgetTag t) ->
    ForgetTag (lunit $ (coerce t :: C 1 ⊗ C 1))

type Pos1 = '[ '( 'Pos 1, 1)]

-- | @fmap fuse@ at the concrete type @(C 1 ⊗ C 1) -+> C 1@.
demoFmapFuse :: (C 1 ⊗ C 1) -+> C 1
demoFmapFuse =
  linearFunction $ \t ->
    unForgetTag (getLinearFunction (fmap (fuse @Pos1 @Pos1)) (ForgetTag t))

-- | Compile an intertwiner on flat @C (RepDim r)@ storage.
repInterLinear
  :: forall r q.
     ( KnownNat (RepDim r), KnownNat (RepDim q)
     , U1RepList r, U1RepList q, ApplyIntertwiner r q
     , KnownRep U1 r, KnownRep U1 q
     )
  => Intertwiner r q
  -> LinearFunction (Complex Double) (ForgetTag ('Rep r)) (ForgetTag ('Rep q))
repInterLinear mor =
  linearFunction $ \(ForgetTag v) ->
    ForgetTag (unToC (getLinearFunction (intertwinerLinear mor) (ToC v)))

unToC :: ToC r -> C (RepDim r)
unToC (ToC v) = v

--------------------------------------------------------------------------------
-- @TensorSpace@ for @ForgetTag@ (mirrors @FunctorExperiment.ToC@)
--------------------------------------------------------------------------------

instance KnownNat (RepDim r) => AdditiveGroup (ForgetTag ('Rep r)) where
  ForgetTag a ^+^ ForgetTag b = ForgetTag (a ^+^ b)
  zeroV = ForgetTag zeroV
  negateV (ForgetTag v) = ForgetTag (negateV v)

instance KnownNat (RepDim r) => VectorSpace (ForgetTag ('Rep r)) where
  type Scalar (ForgetTag ('Rep r)) = Complex Double
  μ *^ ForgetTag v = ForgetTag (μ *^ v)

instance KnownNat (RepDim r) => InnerSpace (ForgetTag ('Rep r)) where
  ForgetTag v <.> ForgetTag w = v <.> w

instance KnownNat (RepDim r) => DimensionAware (ForgetTag ('Rep r)) where
  type StaticDimension (ForgetTag ('Rep r)) = StaticDimension (C (RepDim r))
  dimensionalityWitness = undefined

instance (KnownNat (RepDim r), n ~ RepDim r) => n `Dimensional` ForgetTag ('Rep r) where
  knownDimensionalitySing = sing
  unsafeFromArrayWithOffset i ar =
    ForgetTag (unsafeFromArrayWithOffset i ar)
  unsafeWriteArrayWithOffset ar i (ForgetTag v) =
    unsafeWriteArrayWithOffset ar i v

instance KnownNat (RepDim r) => Semimanifold (ForgetTag ('Rep r)) where
  type Needle (ForgetTag ('Rep r)) = C (RepDim r)
  ForgetTag _ .+~^ _ = undefined

instance KnownNat (RepDim r) => PseudoAffine (ForgetTag ('Rep r)) where
  ForgetTag _ .-~! ForgetTag _ = undefined
  ForgetTag _ .-~. ForgetTag _ = undefined

instance KnownNat (RepDim r) => TensorSpace (ForgetTag ('Rep r)) where
  type TensorProduct (ForgetTag ('Rep r)) w = TensorProduct (C (RepDim r)) w
  scalarSpaceWitness = undefined
  linearManifoldWitness = undefined
  zeroTensor = undefined
  toFlatTensor = undefined
  fromFlatTensor = undefined
  addTensors = undefined
  subtractTensors = undefined
  scaleTensor = undefined
  negateTensor = undefined
  tensorProduct = undefined
  transposeTensor = undefined
  fmapTensor = undefined
  fzipTensorWith = undefined
  tensorUnsafeFromArrayWithOffset = undefined
  tensorUnsafeWriteArrayWithOffset = undefined
  coerceFmapTensorProduct = undefined
  wellDefinedVector (ForgetTag v) = ForgetTag <$> wellDefinedVector v
  wellDefinedTensor = undefined
  vectorConjugate = undefined

instance
  ( KnownNat (RepDim r), KnownNat (RepDim q)
  ) => AdditiveGroup (ForgetTag ('Prod r q)) where
  ForgetTag a ^+^ ForgetTag b = ForgetTag (a ^+^ b)
  zeroV = ForgetTag zeroV
  negateV (ForgetTag v) = ForgetTag (negateV v)

instance
  ( KnownNat (RepDim r), KnownNat (RepDim q)
  ) => VectorSpace (ForgetTag ('Prod r q)) where
  type Scalar (ForgetTag ('Prod r q)) = Complex Double
  μ *^ ForgetTag v = ForgetTag (μ *^ v)

instance
  ( KnownNat (RepDim r), KnownNat (RepDim q)
  ) => InnerSpace (ForgetTag ('Prod r q)) where
  ForgetTag v <.> ForgetTag w = v <.> w

instance
  ( KnownNat (RepDim r), KnownNat (RepDim q)
  ) => DimensionAware (ForgetTag ('Prod r q)) where
  type StaticDimension (ForgetTag ('Prod r q)) =
    StaticDimension (C (RepDim r) ⊗ C (RepDim q))
  dimensionalityWitness = undefined

instance
  ( KnownNat (RepDim r), KnownNat (RepDim q)
  ) => Semimanifold (ForgetTag ('Prod r q)) where
  type Needle (ForgetTag ('Prod r q)) = C (RepDim r) ⊗ C (RepDim q)
  ForgetTag _ .+~^ _ = undefined

instance
  ( KnownNat (RepDim r), KnownNat (RepDim q)
  ) => PseudoAffine (ForgetTag ('Prod r q)) where
  ForgetTag _ .-~! ForgetTag _ = undefined
  ForgetTag _ .-~. ForgetTag _ = undefined

instance
  ( KnownNat (RepDim r), KnownNat (RepDim q)
  ) => TensorSpace (ForgetTag ('Prod r q)) where
  type TensorProduct (ForgetTag ('Prod r q)) w =
    TensorProduct (C (RepDim r) ⊗ C (RepDim q)) w
  scalarSpaceWitness = undefined
  linearManifoldWitness = undefined
  zeroTensor = undefined
  toFlatTensor = undefined
  fromFlatTensor = undefined
  addTensors = undefined
  subtractTensors = undefined
  scaleTensor = undefined
  negateTensor = undefined
  tensorProduct = undefined
  transposeTensor = undefined
  fmapTensor = undefined
  fzipTensorWith = undefined
  tensorUnsafeFromArrayWithOffset = undefined
  tensorUnsafeWriteArrayWithOffset = undefined
  coerceFmapTensorProduct = undefined
  wellDefinedVector (ForgetTag v) = ForgetTag <$> wellDefinedVector v
  wellDefinedTensor = undefined
  vectorConjugate = undefined

--------------------------------------------------------------------------------
-- Category + functor
--------------------------------------------------------------------------------

instance Category U1Mor where
  type Object U1Mor ('Rep r) =
    ( U1RepList r, KnownNat (RepDim r)
    , BuildIdHom (HomSectorList r r), KnownRep U1 r
    )
  type Object U1Mor ('Prod r q) =
    ( IsIrrep1 r ~ 'True, IsIrrep1 q ~ 'True
    , RepDim r ~ RepDimOfIrrep1 (IsIrrep1 r)
    , RepDim q ~ RepDimOfIrrep1 (IsIrrep1 q)
    , RepDim (TensorU1 r q) ~ FusedIrrep1Dim (IsIrrep1 r) (IsIrrep1 q)
    , U1RepList r, U1RepList q
    , KnownNat (RepDim r), KnownNat (RepDim q)
    , KnownNat (RepDim (TensorU1 r q))
    )

  id :: forall a. Object U1Mor a => U1Mor a a
  id = unsafeCoerce (RepInter mkIdHom :: U1Mor ('Rep Pos1) ('Rep Pos1))

  RepInter g . RepInter f = RepInter (g `compose` f)

-- | Forgetful functor @Rep_{U(1)} -> Vect@.
--
-- On @'Prod r q@, @fmap 'Fuse'@ is the Kronecker-to-fused change of basis; for
-- two @C 1@ irreps that is @(C 1 ⊗ C 1) -+> C 1@ on the underlying spaces.
instance Functor ForgetTag U1Mor (LinearFunction (Complex Double)) where
  fmap (RepInter mor) = repInterLinear mor
  fmap Fuse          = fuseLinear
