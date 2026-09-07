{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Term-level symbolic SU(2): cups, Hom, Mac Lane compose.
--
-- Singletons: 'Experiments.Symbolic.Singletons'.
-- 'RepV' / fuse: 'Experiments.Symbolic.RepV'.
-- F-moves / fuseMap: 'Experiments.Symbolic.FMove'.
-- Concrete spines + smokes: 'Experiments.Symbolic.Smoke'.
--
-- Layers: 'Obj' → 'HomUnfused' (Kronecker); 'Obj' → 'HomFused' via
-- 'ObjSpineSU2' / 'ObjRep' with genealogy 'RepV' / 'FuseRep' morphisms;
-- 'HomInter' = trivial sector of fused Hom (same compose via embed/filter).
-- Cups: genealogy 'cup' / 'capUnfusedObj'.
module Experiments.Symbolic.Core where

import Data.Complex (Complex ((:+)), conjugate, magnitude, realPart)
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.VectorSpace (AdditiveGroup (zeroV, (^-^)), InnerSpace ((<.>)), Scalar, VectorSpace ((*^)))
import GHC.TypeLits (KnownNat, Nat, sameNat, type (+))
import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..))
import Experiments.Categorical.Associative (Associative (..))
import Experiments.Categorical.Bifunctor (Bifunctor (..), PFunctor (..), QFunctor (..))
import Experiments.Categorical.Braided (Braided (..))
import Experiments.Categorical.Monoidal (Monoidal (..))
import Experiments.Fusion.Obj (Obj)
import qualified Experiments.Fusion.Obj as FObj
import Experiments.Symbolic.Aliases
import Experiments.Symbolic.Expr
import Experiments.Symbolic.FMove
import Experiments.Symbolic.RepV
import Experiments.Symbolic.Singletons
import Experiments.Symbolic.TypeLevel
import Math.LinearMap.Asserted (getLinearFunction)
import Math.LinearMap.Category
  ( DualVector
  , TensorSpace
  , (-+$>)
  , idTensor
  , pattern LinearFunction
  , trace
  , type (+>)
  , type (⊗)
  , (⊗), Tensor (..)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Class (LinearSpace, asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
import Numeric.LinearAlgebra.Static (C, konst)
import TensorNetwork.Categorical
  ( fuseBond
  , lassocMap
  , rassocMap
  , runit
  , splitBond
  , swapMap
  , (⊗^)
  )

import Prelude hiding (id, (.), ($))

--------------------------------------------------------------------------------
-- Unit packaging + fused cups
--------------------------------------------------------------------------------

-- | Unit amplitude as @ToVObj ('Atom 0)@ packing (@C 1 ⊗ C 1@).
unitToVFromScalar :: Complex Double -> C 1 ⊗ C 1
unitToVFromScalar = Tensor . konst

-- | Read the amplitude from @C 1 ⊗ C 1@ by pairing against the unit packing.
unitToVScalar :: (C 1 ⊗ C 1) -> Complex Double
unitToVScalar u = unitToVFromScalar 1 <.> u

--------------------------------------------------------------------------------
-- Unfused composition (compact closed on Obj / HomUnfused)
--
--   compose f g = unitor ∘ (cup ⊗ id) ∘ assoc ∘ (f ⊗ g)
--
-- Hom elements are Dual-left @Dual(ToVObj a) ⊗ ToVObj b@. Unitors below are
-- shared with the Monoidal instance; Obj cups use 'ToVObj'.
--------------------------------------------------------------------------------

-- | Unfused morphisms @a → b@: Dual-left packing on tree spaces
-- @Dual(ToVObj a) ⊗ ToVObj b@ (@'Tensor@ = Kronecker).
newtype HomUnfused (a :: Obj Nat) (b :: Obj Nat) = HomUnfused
  { unHomUnfused :: DualVector (ToVObj a) ⊗ ToVObj b }

-- | Fused morphisms @a → b@: 'Obj' trees, payload is genealogy 'RepV' of
-- 'FuseRep (ObjRep a) (ObjRep b)' after 'ObjSpineSU2' (SU(2) dual≅primal;
-- left child plays dual). Compose via 'composeHomTrees' on those leaf reps.
newtype HomFused (a :: Obj Nat) (b :: Obj Nat) = HomFused
  { unHomFused :: RepV (FuseRep (ObjRep a) (ObjRep b)) }

-- | Intertwiners @a → b@: trivial total-charge sector of fused Hom
-- (@'FilterTrivial' of 'FuseRep (ObjRep a) (ObjRep b)'@). Compose reuses
-- 'composeHomTrees' via 'embedTrivialRepV' \/ 'filterTrivialRepV'.
newtype HomInter (a :: Obj Nat) (b :: Obj Nat) = HomInter
  { unHomInter :: RepV (FilterTrivial (FuseRep (ObjRep a) (ObjRep b))) }

-- | Left unitor for the Unit sector packaging @'(C 1 ⊗ C 1) ⊗ v → v@.
unitLunit
  :: forall v
   . ( LinearSpace v
     , Scalar v ~ Complex Double
     , TensorSpace v
     )
  => ((C 1 ⊗ C 1) ⊗ v) +> v
unitLunit =
  runit
    . swapMap
    . (fuseBond @1 @1 ⊗^ id)

-- | Inverse of 'unitLunit': @v → (C 1 ⊗ C 1) ⊗ v@.
unitLcounit
  :: forall v
   . ( LinearSpace v
     , Scalar v ~ Complex Double
     , TensorSpace v
     )
  => v +> ((C 1 ⊗ C 1) ⊗ v)
unitLcounit =
  (splitBond @1 @1 ⊗^ id)
    . swapMap
    . arr (LinearFunction (\x -> x ⊗ (konst 1 :: C 1)))

-- | Right unitor for the Unit sector packaging @'v ⊗ (C 1 ⊗ C 1) → v@.
unitRunit
  :: forall v
   . ( LinearSpace v
     , Scalar v ~ Complex Double
     , TensorSpace v
     )
  => (v ⊗ (C 1 ⊗ C 1)) +> v
unitRunit =
  runit
    . (id ⊗^ fuseBond @1 @1)

-- | Inverse of 'unitRunit': @v → v ⊗ (C 1 ⊗ C 1)@.
unitRcounit
  :: forall v
   . ( LinearSpace v
     , Scalar v ~ Complex Double
     , TensorSpace v
     )
  => v +> (v ⊗ (C 1 ⊗ C 1))
unitRcounit =
  (id ⊗^ splitBond @1 @1)
    . arr (LinearFunction (\x -> x ⊗ (konst 1 :: C 1)))

--------------------------------------------------------------------------------
-- True unfused Hom on Obj trees (ToVObj / Dual-left Hom)
--------------------------------------------------------------------------------

-- | Object spaces for 'HomUnfused': 'ToVObj' is a nested Kronecker / pair space.
class
  ( LinearSpace (ToVObj a)
  , LinearSpace (DualVector (ToVObj a))
  , Scalar (ToVObj a) ~ Complex Double
  , Scalar (DualVector (ToVObj a)) ~ Complex Double
  , TensorSpace (ToVObj a)
  , TensorSpace (DualVector (ToVObj a))
  , TensorSpace ((ToVObj a ⊗ DualVector (ToVObj a)))
  , TensorSpace (ToVObj ('FObj.Atom 0))
  ) =>
  KnownToVObj (a :: Obj Nat)

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  KnownToVObj ('FObj.Atom j)

instance (KnownToVObj a, KnownToVObj b) => KnownToVObj ('FObj.Tensor a b)

instance (KnownToVObj a, KnownToVObj b) => KnownToVObj ('FObj.Sum a b)

-- | Unfused evaluation @ε : a ⊗ a* → 𝟙@ on tree spaces.
cupUnfusedObj
  :: forall a
   . KnownToVObj a
  => (ToVObj a ⊗ DualVector (ToVObj a))
  -> ToVObj ('FObj.Atom 0)
cupUnfusedObj t =
  unitToVFromScalar
    ( getLinearFunction
        trace
        (fromTensor -+$=> (swapMap $ t))
    )

-- | Unfused coevaluation @η : 𝟙 → a ⊗ a*@.
capUnfusedObj
  :: forall a
   . KnownToVObj a
  => ToVObj ('FObj.Atom 0)
  -> (ToVObj a ⊗ DualVector (ToVObj a))
capUnfusedObj u = unitToVScalar u *^ idTensor @(ToVObj a)

-- | Identity Hom element on an Obj tree.
idMorObj
  :: forall a
   . KnownToVObj a
  => (DualVector (ToVObj a) ⊗ ToVObj a)
idMorObj = swapMap $ capUnfusedObj @a (unitToVFromScalar 1)

-- | Pack a linear map as Dual-left Hom.
linToHomObj
  :: forall a b
   . ( KnownToVObj a
     , KnownToVObj b
     )
  => (ToVObj a +> ToVObj b)
  -> (DualVector (ToVObj a) ⊗ ToVObj b)
linToHomObj f = asTensor -+$=> f

tensorComposeObj
  :: forall a b c
   . ( TensorSpace ((DualVector (ToVObj a) ⊗ ToVObj b))
     , TensorSpace ((DualVector (ToVObj b) ⊗ ToVObj c))
     , Scalar ((DualVector (ToVObj a) ⊗ ToVObj b)) ~ Complex Double
     , Scalar ((DualVector (ToVObj b) ⊗ ToVObj c)) ~ Complex Double
     )
  => (DualVector (ToVObj a) ⊗ ToVObj b)
  -> (DualVector (ToVObj b) ⊗ ToVObj c)
  -> (DualVector (ToVObj a) ⊗ ToVObj b) ⊗ (DualVector (ToVObj b) ⊗ ToVObj c)
tensorComposeObj = (⊗)

assocComposeObj
  :: forall a b c
   . ( KnownToVObj a
     , KnownToVObj b
     , KnownToVObj c
     )
  => (DualVector (ToVObj a) ⊗ ToVObj b) ⊗ (DualVector (ToVObj b) ⊗ ToVObj c)
  -> DualVector (ToVObj a) ⊗ ((ToVObj b ⊗ DualVector (ToVObj b)) ⊗ ToVObj c)
assocComposeObj t =
  (id ⊗^ lassocMap @(ToVObj b) @(DualVector (ToVObj b)) @(ToVObj c))
    $ ( rassocMap
          @(DualVector (ToVObj a))
          @(ToVObj b)
          @(DualVector (ToVObj b) ⊗ ToVObj c)
          $ t
      )

cupTensorIdComposeObj
  :: forall a b c
   . ( KnownToVObj a
     , KnownToVObj b
     , KnownToVObj c
     )
  => DualVector (ToVObj a) ⊗ ((ToVObj b ⊗ DualVector (ToVObj b)) ⊗ ToVObj c)
  -> DualVector (ToVObj a) ⊗ (ToVObj ('FObj.Atom 0) ⊗ ToVObj c)
cupTensorIdComposeObj t =
  (id ⊗^ (arr (LinearFunction (cupUnfusedObj @b)) ⊗^ id)) $ t

unitorComposeObj
  :: forall a c
   . ( KnownToVObj a
     , KnownToVObj c
     )
  => DualVector (ToVObj a) ⊗ (ToVObj ('FObj.Atom 0) ⊗ ToVObj c)
  -> (DualVector (ToVObj a) ⊗ ToVObj c)
unitorComposeObj t =
  (id ⊗^ unitLunit @(ToVObj c)) $ t

-- | Unfused Hom composition on Obj trees:
-- @unitor ∘ (cup ⊗ id) ∘ assoc ∘ (f ⊗ g)@.
composeMorObj
  :: forall a b c
   . ( KnownToVObj a
     , KnownToVObj b
     , KnownToVObj c
     , TensorSpace ((DualVector (ToVObj a) ⊗ ToVObj b))
     , TensorSpace ((DualVector (ToVObj b) ⊗ ToVObj c))
     , Scalar ((DualVector (ToVObj a) ⊗ ToVObj b)) ~ Complex Double
     , Scalar ((DualVector (ToVObj b) ⊗ ToVObj c)) ~ Complex Double
     )
  => (DualVector (ToVObj a) ⊗ ToVObj b)
  -> (DualVector (ToVObj b) ⊗ ToVObj c)
  -> (DualVector (ToVObj a) ⊗ ToVObj c)
composeMorObj f g =
  unitorComposeObj @a @c
    ( cupTensorIdComposeObj @a @b @c
        ( assocComposeObj @a @b @c
            (tensorComposeObj @a @b @c f g)
        )
    )

--------------------------------------------------------------------------------
-- Category \/ monoidal structure: HomUnfused (complete)
--------------------------------------------------------------------------------

instance Category HomUnfused where
  type Object HomUnfused a = KnownToVObj a

  id :: forall a. Object HomUnfused a => HomUnfused a a
  id = HomUnfused (idMorObj @a)

  (.)
    :: forall a b c
     . (Object HomUnfused a, Object HomUnfused b, Object HomUnfused c)
    => HomUnfused b c
    -> HomUnfused a b
    -> HomUnfused a c
  HomUnfused g . HomUnfused f =
    HomUnfused (composeMorObj @a @b @c f g)

instance PFunctor FObj.Tensor HomUnfused HomUnfused where
  first
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (FObj.Tensor a c)
       , Object HomUnfused (FObj.Tensor b c)
       )
    => HomUnfused a b
    -> HomUnfused (FObj.Tensor a c) (FObj.Tensor b c)
  first (HomUnfused f) =
    HomUnfused $
      linToHomObj @(FObj.Tensor a c) @(FObj.Tensor b c)
        ((fromTensor -+$=> f) ⊗^ id)

instance QFunctor FObj.Tensor HomUnfused HomUnfused where
  second
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (FObj.Tensor c a)
       , Object HomUnfused (FObj.Tensor c b)
       )
    => HomUnfused a b
    -> HomUnfused (FObj.Tensor c a) (FObj.Tensor c b)
  second (HomUnfused g) =
    HomUnfused $
      linToHomObj @(FObj.Tensor c a) @(FObj.Tensor c b)
        (id ⊗^ (fromTensor -+$=> g))

-- | @bimap f g@ is the Kronecker product of the underlying linear maps,
-- packed Dual-left: @(unpack f) ⊗^ (unpack g)@.
instance Bifunctor FObj.Tensor HomUnfused HomUnfused HomUnfused where
  bimap
    :: forall a b c d
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused d
       , Object HomUnfused (FObj.Tensor a c)
       , Object HomUnfused (FObj.Tensor b d)
       )
    => HomUnfused a b
    -> HomUnfused c d
    -> HomUnfused (FObj.Tensor a c) (FObj.Tensor b d)
  bimap (HomUnfused f) (HomUnfused g) =
    HomUnfused $
      linToHomObj @(FObj.Tensor a c) @(FObj.Tensor b d)
        ((fromTensor -+$=> f) ⊗^ (fromTensor -+$=> g))

-- | Object associator is linearmap @α@ (Kronecker reassociation), packed as Hom.
instance Associative HomUnfused FObj.Tensor where
  associate
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (FObj.Tensor a b)
       , Object HomUnfused (FObj.Tensor b c)
       , Object HomUnfused (FObj.Tensor (FObj.Tensor a b) c)
       , Object HomUnfused (FObj.Tensor a (FObj.Tensor b c))
       )
    => HomUnfused (FObj.Tensor (FObj.Tensor a b) c) (FObj.Tensor a (FObj.Tensor b c))
  associate =
    HomUnfused
      ( linToHomObj
          @(FObj.Tensor (FObj.Tensor a b) c)
          @(FObj.Tensor a (FObj.Tensor b c))
          (rassocMap @(ToVObj a) @(ToVObj b) @(ToVObj c))
      )

  disassociate
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (FObj.Tensor a b)
       , Object HomUnfused (FObj.Tensor b c)
       , Object HomUnfused (FObj.Tensor (FObj.Tensor a b) c)
       , Object HomUnfused (FObj.Tensor a (FObj.Tensor b c))
       )
    => HomUnfused (FObj.Tensor a (FObj.Tensor b c)) (FObj.Tensor (FObj.Tensor a b) c)
  disassociate =
    HomUnfused
      ( linToHomObj
          @(FObj.Tensor a (FObj.Tensor b c))
          @(FObj.Tensor (FObj.Tensor a b) c)
          (lassocMap @(ToVObj a) @(ToVObj b) @(ToVObj c))
      )

instance Monoidal HomUnfused FObj.Tensor where
  type Id HomUnfused FObj.Tensor = 'FObj.Atom 0

  idl
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('FObj.Atom 0)
       , Object HomUnfused (FObj.Tensor ('FObj.Atom 0) a)
       )
    => HomUnfused (FObj.Tensor ('FObj.Atom 0) a) a
  idl =
    HomUnfused
      (linToHomObj @(FObj.Tensor ('FObj.Atom 0) a) @a (unitLunit @(ToVObj a)))

  idr
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('FObj.Atom 0)
       , Object HomUnfused (FObj.Tensor a ('FObj.Atom 0))
       )
    => HomUnfused (FObj.Tensor a ('FObj.Atom 0)) a
  idr =
    HomUnfused
      (linToHomObj @(FObj.Tensor a ('FObj.Atom 0)) @a (unitRunit @(ToVObj a)))

  coidl
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('FObj.Atom 0)
       , Object HomUnfused (FObj.Tensor ('FObj.Atom 0) a)
       )
    => HomUnfused a (FObj.Tensor ('FObj.Atom 0) a)
  coidl =
    HomUnfused
      (linToHomObj @a @(FObj.Tensor ('FObj.Atom 0) a) (unitLcounit @(ToVObj a)))

  coidr
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('FObj.Atom 0)
       , Object HomUnfused (FObj.Tensor a ('FObj.Atom 0))
       )
    => HomUnfused a (FObj.Tensor a ('FObj.Atom 0))
  coidr =
    HomUnfused
      (linToHomObj @a @(FObj.Tensor a ('FObj.Atom 0)) (unitRcounit @(ToVObj a)))

instance Braided HomUnfused FObj.Tensor where
  braid = undefined

-- | Object constraint for fused Hom: 'Obj' with a known identity on 'ObjRep'.
class KnownHomFused (a :: Obj Nat) where
  idHomFusedVal :: RepV (FuseRep (ObjRep a) (ObjRep a))

-- | Identity endomorphism on a leaf: singlet (@root = 0@) channel = 1, else 0.
idHomLeaf
  :: forall j
   . ( KnownNat j
     , KnownRep (FuseRep '[ 'Leaf j] '[ 'Leaf j])
     )
  => RepV (FuseRep '[ 'Leaf j] '[ 'Leaf j])
idHomLeaf = go (repSing @(FuseRep '[ 'Leaf j] '[ 'Leaf j]))
  where
    go :: forall ts. SRep ts -> RepV ts
    go SRepNil = RNil
    go (SRepCons (t :: SIrrepTree u) rest) =
      case t of
        SNode @d _l _r ->
          case sameNat (Proxy @d) (Proxy @0) of
            Just Refl -> RCons @u (konst 1) (go rest)
            Nothing -> RCons @u zeroV (go rest)
        SLeaf {} ->
          error "idHomLeaf: expected Hom Node channels"

-- | Simple atom: identity via 'idHomLeaf' (@ObjSpineSU2 ('Atom j) ~ '[ '(j,1)]@).
instance
  ( KnownNat j
  , KnownRep (FuseRep '[ 'Leaf j] '[ 'Leaf j])
  , ObjSpineSU2 ('FObj.Atom j) ~ '[ '(j, 1)]
  , ObjRep ('FObj.Atom j) ~ '[ 'Leaf j]
  ) =>
  KnownHomFused ('FObj.Atom j)
  where
  idHomFusedVal = idHomLeaf @j

idHom11 :: RepV Hom11
idHom11 = idHomLeaf @1

idHom22 :: RepV Hom22
idHom22 = idHomLeaf @2

-- Category \/ monoidal structure: HomUnfused (complete). HomFused Category lives
-- with the tree compose ladder (see 'composeHomFused').

--------------------------------------------------------------------------------
-- Fused Hom compose: five Mac Lane morphisms (genealogy Hom; left ≅ dual)
--
--   f ⊗ g
--     ─ F ─►     a* ⊗ (b ⊗ (b* ⊗ c))
--     ─ id⊗F ─►  a* ⊗ ((b ⊗ b*) ⊗ c)
--     ─ id⊗(ε⊗id) ─►  a* ⊗ (Unit ⊗ c)
--     ─ id⊗λ ─►  a* ⊗ c
--------------------------------------------------------------------------------

-- | Step 1: @f ⊗ g@.
tensorHom
  :: forall a b c
   . ( KnownRep (FuseRep a b)
     , KnownRep (FuseRep b c)
     , FuseRepTermC (FuseRep a b) (FuseRep b c)
     )
  => RepV (FuseRep a b)
  -> RepV (FuseRep b c)
  -> RepV (FuseRep (FuseRep a b) (FuseRep b c))
tensorHom = fuseRepTerm @(FuseRep a b) @(FuseRep b c)

-- | Step 2: outer F — @(a*⊗b) ⊗ (b*⊗c) → a* ⊗ (b ⊗ (b*⊗c))@.
--
-- Discharged by 'CanFmoveOuterHom' (leaf instance → 'fmoveOuterHomLeaves').
-- ('fmoveInnerHom' is the subsequent @id ⊗ F@ via 'fuseMapRight' 'fmoveInvTrees'.)

-- | Step 3: @id ⊗ F@ — @a* ⊗ (b ⊗ (b*⊗c)) → a* ⊗ ((b ⊗ b*) ⊗ c)@.
--
-- Right factor: @FuseRep b (FuseRep b c) → FuseRep (FuseRep b b) c@ via 'fmoveInvTrees'.
fmoveInnerHom
  :: forall a b c
   . ( KnownRep a
     , KnownRep (FuseRep b (FuseRep b c))
     , KnownRep (FuseRep (FuseRep b b) c)
     , KnownRep (FuseRep a (FuseRep b (FuseRep b c)))
     , KnownRep (FuseRep a (FuseRep (FuseRep b b) c))
     , CanFmoveTrees b b c
     )
  => RepV (FuseRep a (FuseRep b (FuseRep b c)))
  -> RepV (FuseRep a (FuseRep (FuseRep b b) c))
fmoveInnerHom =
  fuseMapRight
    @a
    @(FuseRep b (FuseRep b c))
    @(FuseRep (FuseRep b b) c)
    (fmoveInvTrees @b @b @c)

-- | Step 4: @id ⊗ (cup ⊗ id)@ — Unit remains in the type.
cupTensorIdHom
  :: forall a b c
   . ( KnownRep a
     , KnownRep b
     , KnownRep c
     , KnownRep (FuseRep b b)
     , KnownRep Unit
     , KnownRep (FuseRep (FuseRep b b) c)
     , KnownRep (FuseRep Unit c)
     , KnownRep (FuseRep a (FuseRep (FuseRep b b) c))
     , KnownRep (FuseRep a (FuseRep Unit c))
     , KnownRep (FuseRep b b)
     )
  => RepV (FuseRep a (FuseRep (FuseRep b b) c))
  -> RepV (FuseRep a (FuseRep Unit c))
cupTensorIdHom =
  fuseMapRight
    @a
    @(FuseRep (FuseRep b b) c)
    @(FuseRep Unit c)
    ( fuseMapLeft
        @(FuseRep b b)
        @Unit
        @c
        (cup @b)
    )

-- | Evaluation @ε : b ⊗ b* → 𝟙@ on genealogy Hom (@FuseRep b b@, dual≅primal).
-- Singlet channels scaled by FS·dim of the cupped root; others drop.
cup
  :: forall b
   . KnownRep (FuseRep b b)
  => RepV (FuseRep b b)
  -> RepV Unit
cup bb =
  RCons @('Leaf 0) (konst (cupHomTreesScalar @(FuseRep b b) bb)) RNil
  where
    -- Singlet walk via 'SRep': @sameNat@ refines @j ~ 0@ so payloads stay @C 1@.
    cupHomTreesScalar
      :: forall ts
       . KnownRep ts
      => RepV ts
      -> Complex Double
    cupHomTreesScalar = go (repSing @ts)
      where
        go :: forall ts'. SRep ts' -> RepV ts' -> Complex Double
        go SRepNil RNil = 0
        go (SRepCons t rest) (RCons v rs) =
          case t of
            SLeaf @j ->
              case sameNat (Proxy @j) (Proxy @0) of
                Just Refl -> (konst 1 <.> v) + go rest rs
                Nothing -> go rest rs
            SNode @j l _r ->
              case sameNat (Proxy @j) (Proxy @0) of
                Just Refl ->
                  su2CupFactor (rootLab l) * (konst 1 <.> v) + go rest rs
                Nothing -> go rest rs

    -- Frobenius–Schur cup factor @FS(j)·dim(j)@ (@tj = 2j@).
    su2CupFactor :: Int -> Complex Double
    su2CupFactor tj =
      let fs = if even tj then 1 else -1
          dim = fromIntegral (tj + 1) :: Double
       in (fs * dim) :+ 0

-- | Step 5: @id ⊗ λ@ — @a* ⊗ (Unit ⊗ c) → a* ⊗ c@ (not type-level absorption).
unitorHom
  :: forall a c
   . ( KnownRep a
     , KnownRep c
     , KnownRep (FuseRep Unit c)
     , KnownRep (FuseRep a (FuseRep Unit c))
     , KnownRep (FuseRep a c)
     , UnitorCodomain (FuseRep Unit c) ~ c
     )
  => RepV (FuseRep a (FuseRep Unit c))
  -> RepV (FuseRep a c)
unitorHom =
  fuseMapRight @a @(FuseRep Unit c) @c (unitor @c)

-- | Left unitor on fusion trees: @Unit ⊗ c → c@ (drop @'Leaf 0@ left child).
--
-- For each @t@ in @c@, @FuseTrees ('Leaf 0) t = '[ 'Node (Root t) ('Leaf 0) t ]@
-- (SU(2): @0 ⊗ j = j@); payloads are already the root irrep of @t@.
unitor
  :: forall c
   . ( KnownRep (FuseRep Unit c)
     , UnitorCodomain (FuseRep Unit c) ~ c
     )
  => RepV (FuseRep Unit c)
  -> RepV c
unitor = go (repSing @(FuseRep Unit c))
  where
    -- @sameNat@ refines left child to @'Leaf 0@; 'UnitorCodomain' drops it.
    go
      :: forall uc
       . SRep uc
      -> RepV uc
      -> RepV (UnitorCodomain uc)
    go SRepNil RNil = RNil
    go (SRepCons t rest) (RCons v rs) =
      case t of
        SNode @j l r ->
          case l of
            SLeaf @zj ->
              case sameNat (Proxy @zj) (Proxy @0) of
                Just Refl ->
                  case r of
                    SLeaf @rj ->
                      case sameNat (Proxy @rj) (Proxy @j) of
                        Just Refl ->
                          RCons @('Leaf rj) v (go rest rs)
                        Nothing ->
                          error "unitor: root mismatch after 0⊗t"
                    SNode @rj @rl @rr _l _r ->
                      case sameNat (Proxy @rj) (Proxy @j) of
                        Just Refl ->
                          RCons @('Node rj rl rr) v (go rest rs)
                        Nothing ->
                          error "unitor: root mismatch after 0⊗t"
                Nothing ->
                  error "unitor: expected left child 'Leaf 0"
            SNode {} ->
              error "unitor: expected left child 'Leaf 0"
        SLeaf {} ->
          error "unitor: expected Node from FuseRep Unit"

-- | Fused Hom compose as the five Mac Lane morphisms.
composeHomTrees
  :: forall a b c
   . ( KnownRep (FuseRep a b)
     , KnownRep (FuseRep b c)
     , FuseRepTermC (FuseRep a b) (FuseRep b c)
     , KnownRep a
     , KnownRep b
     , KnownRep c
     , KnownRep (FuseRep b b)
     , KnownRep Unit
     , KnownRep (FuseRep b (FuseRep b c))
     , KnownRep (FuseRep (FuseRep b b) c)
     , KnownRep (FuseRep Unit c)
     , KnownRep (FuseRep a (FuseRep b (FuseRep b c)))
     , KnownRep (FuseRep a (FuseRep (FuseRep b b) c))
     , KnownRep (FuseRep a (FuseRep Unit c))
     , KnownRep (FuseRep a c)
     , CanFmoveOuterHom a b c
     , CanFmoveTrees b b c
     , UnitorCodomain (FuseRep Unit c) ~ c
     )
  => RepV (FuseRep a b)
  -> RepV (FuseRep b c)
  -> RepV (FuseRep a c)
composeHomTrees f g =
  unitorHom @a @c
    ( cupTensorIdHom @a @b @c
        ( fmoveInnerHom @a @b @c
            ( fmoveOuterHom @a @b @c
                (tensorHom @a @b @c f g)
            )
        )
    )

--------------------------------------------------------------------------------
-- HomFused: RepV-backed fused Hom
--------------------------------------------------------------------------------

-- | 'HomFused' compose via the five Mac Lane morphisms ('composeHomTrees')
-- on 'ObjRep'-expanded leaf reps.
composeHomFused
  :: forall a b c
   . ( KnownRep (FuseRep (ObjRep a) (ObjRep b))
     , KnownRep (FuseRep (ObjRep b) (ObjRep c))
     , FuseRepTermC (FuseRep (ObjRep a) (ObjRep b)) (FuseRep (ObjRep b) (ObjRep c))
     , KnownRep (ObjRep a)
     , KnownRep (ObjRep b)
     , KnownRep (ObjRep c)
     , KnownRep (FuseRep (ObjRep b) (ObjRep b))
     , KnownRep Unit
     , KnownRep (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c)))
     , KnownRep (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c))
     , KnownRep (FuseRep Unit (ObjRep c))
     , KnownRep (FuseRep (ObjRep a) (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c))))
     , KnownRep (FuseRep (ObjRep a) (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c)))
     , KnownRep (FuseRep (ObjRep a) (FuseRep Unit (ObjRep c)))
     , KnownRep (FuseRep (ObjRep a) (ObjRep c))
     , CanFmoveOuterHom (ObjRep a) (ObjRep b) (ObjRep c)
     , CanFmoveTrees (ObjRep b) (ObjRep b) (ObjRep c)
     , UnitorCodomain (FuseRep Unit (ObjRep c)) ~ ObjRep c
     )
  => HomFused b c
  -> HomFused a b
  -> HomFused a c
composeHomFused (HomFused g) (HomFused f) =
  HomFused (composeHomTrees @(ObjRep a) @(ObjRep b) @(ObjRep c) f g)

instance Category HomFused where
  type Object HomFused a = KnownHomFused a

  id :: forall a. Object HomFused a => HomFused a a
  id = HomFused (idHomFusedVal @a)

  -- @(.)@ needs the five Mac Lane steps on @a,b,c@, which 'Object' alone does
  -- not imply. Use 'composeHomFused'.
  (.) = undefined

--------------------------------------------------------------------------------
-- HomInter: trivial sector of fused Hom (same Mac Lane compose)
--------------------------------------------------------------------------------

-- | Identity intertwiner: trivial channels of 'idHomFusedVal'.
idHomInterVal
  :: forall a
   . ( KnownHomFused a
     , KnownRep (FuseRep (ObjRep a) (ObjRep a))
     , FilterTrivialC (FuseRep (ObjRep a) (ObjRep a))
     )
  => RepV (FilterTrivial (FuseRep (ObjRep a) (ObjRep a)))
idHomInterVal =
  filterTrivialRepV @(FuseRep (ObjRep a) (ObjRep a)) (idHomFusedVal @a)

-- | 'HomInter' compose: embed → 'composeHomTrees' → filter (same as 'HomFused').
composeHomInter
  :: forall a b c
   . ( KnownRep (FuseRep (ObjRep a) (ObjRep b))
     , KnownRep (FuseRep (ObjRep b) (ObjRep c))
     , KnownRep (FuseRep (ObjRep a) (ObjRep c))
     , FilterTrivialC (FuseRep (ObjRep a) (ObjRep b))
     , FilterTrivialC (FuseRep (ObjRep b) (ObjRep c))
     , FilterTrivialC (FuseRep (ObjRep a) (ObjRep c))
     , FuseRepTermC
         (FuseRep (ObjRep a) (ObjRep b))
         (FuseRep (ObjRep b) (ObjRep c))
     , KnownRep (ObjRep a)
     , KnownRep (ObjRep b)
     , KnownRep (ObjRep c)
     , KnownRep (FuseRep (ObjRep b) (ObjRep b))
     , KnownRep Unit
     , KnownRep (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c)))
     , KnownRep (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c))
     , KnownRep (FuseRep Unit (ObjRep c))
     , KnownRep
         ( FuseRep
             (ObjRep a)
             (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c)))
         )
     , KnownRep
         ( FuseRep
             (ObjRep a)
             (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c))
         )
     , KnownRep (FuseRep (ObjRep a) (FuseRep Unit (ObjRep c)))
     , CanFmoveOuterHom (ObjRep a) (ObjRep b) (ObjRep c)
     , CanFmoveTrees (ObjRep b) (ObjRep b) (ObjRep c)
     , UnitorCodomain (FuseRep Unit (ObjRep c)) ~ ObjRep c
     )
  => HomInter b c
  -> HomInter a b
  -> HomInter a c
composeHomInter (HomInter g) (HomInter f) =
  HomInter $
    filterTrivialRepV @(FuseRep (ObjRep a) (ObjRep c)) $
      composeHomTrees @(ObjRep a) @(ObjRep b) @(ObjRep c)
        (embedTrivialRepV @(FuseRep (ObjRep a) (ObjRep b)) f)
        (embedTrivialRepV @(FuseRep (ObjRep b) (ObjRep c)) g)

instance Category HomInter where
  type Object HomInter a =
    ( KnownHomFused a
    , KnownRep (FuseRep (ObjRep a) (ObjRep a))
    , FilterTrivialC (FuseRep (ObjRep a) (ObjRep a))
    )

  id :: forall a. Object HomInter a => HomInter a a
  id = HomInter (idHomInterVal @a)

  -- Same as 'HomFused': use 'composeHomInter' (needs Mac Lane constraints).
  (.) = undefined

