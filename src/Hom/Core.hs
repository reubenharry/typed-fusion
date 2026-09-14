{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
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
{- HLINT ignore "Eta reduce" -}

-- | Term-level symbolic Hom(g): cups, Hom, Mac Lane compose (SU(2) first).
--
-- Singletons: 'Hom.Singletons'.
-- 'FTreeV' / fuse: 'Hom.FTreeV'.
-- F-moves / idLeft / idRight: 'Hom.FMove'.
-- Concrete spines + smokes: 'Hom.Smoke'.
--
-- Layers: 'Obj' → 'HomUnfused' (Kronecker); 'Obj' → 'HomFused' via
-- 'ObjFTrees' / 'DualObj' with genealogy 'FTreeV' / 'FuseFTrees' morphisms;
-- 'HomInter' = trivial sector of fused Hom (same compose via embed/filter).
-- Cups: genealogy 'cup' / 'capUnfusedObj'.
module Hom.Core where

import Data.Kind (Type)
import Data.Complex (Complex ((:+)), conjugate, magnitude, realPart)
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.VectorSpace (InnerSpace ((<.>)), Scalar, VectorSpace ((*^)))
import GHC.TypeLits (KnownNat, Nat, sameNat)
import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..))
import Categorical.Associative (Associative (..))
import Categorical.Bifunctor (Bifunctor (..), PFunctor (..), QFunctor (..))
import Categorical.Braided (Braided (..))
import Categorical.Monoidal (Monoidal (..))
import Fusion.Obj (DualObj, Obj (Irrep, (:⊗:), (:⊕:)))
import Fusion.Data (FusionData (..))
import Fusion.SU2 (SU2Th)
import Fusion.U1 (U1Th)
import Symmetry.Group (Group (..), Irreps)
import Symmetry.Utils (Z (Zero))
import Hom.Expr
import Hom.FMove
import Hom.FTreeV
import Hom.Singletons
import Hom.TypeLevel
import Math.LinearMap.Asserted (getLinearFunction)
import Math.LinearMap.Category
  ( DualVector
  , TensorSpace
  , idTensor
  , pattern LinearFunction
  , trace
  , type (+>)
  , type (⊗)
  , (⊗)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Class (LinearSpace, asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
import Numeric.LinearAlgebra.Static (C, konst)
import Categorical.Linear
  ( lunit
  , lunitInv
  , lassocMap
  , rassocMap
  , runit
  , runitInv
  , swapMap
  , (⊗^)
  )

import Prelude hiding (id, (.), ($))

--------------------------------------------------------------------------------
-- Unit packaging + fused cups
--------------------------------------------------------------------------------

-- | Read the amplitude from @C 1@ by pairing against @1@.
unitToVScalar :: C 1 -> Complex Double
unitToVScalar = (konst 1 <.>)

--------------------------------------------------------------------------------
-- Unfused composition (compact closed on Obj / HomUnfused)
--
--   compose f g = unitor ∘ (cup ⊗ id) ∘ assoc ∘ (f ⊗ g)
--
-- Hom elements are Dual-left @Dual(ToVObj SU2 a) ⊗ ToVObj SU2 b@. Unitors below are
-- shared with the Monoidal instance; Obj cups use 'ToVObj'.
--------------------------------------------------------------------------------

-- | Unfused morphisms @a → b@: Dual-left packing on tree spaces
-- @Dual(ToVObj g a) ⊗ ToVObj g b@ (linearmap Kronecker packing).
newtype HomUnfused (g :: Group) (a :: Obj (Irreps g)) (b :: Obj (Irreps g)) = HomUnfused
  { unHomUnfused :: DualVector (ToVObj g a) ⊗ ToVObj g b }

-- | Fused morphisms @a → b@: genealogy 'FTreeV' of
-- @FuseFTrees (ObjFTrees g (DualObj (TheoryOf g) a)) (ObjFTrees g b)@.
-- SU(2): 'DualLab' is id on labels (tensor dual still reverses factors).
newtype HomFused (g :: Group) (a :: Obj (Irreps g)) (b :: Obj (Irreps g)) = HomFused
  { unHomFused :: HomFusedRep g a b }

-- | Intertwiners @a → b@: trivial sector of fused Hom.
newtype HomInter (g :: Group) (a :: Obj (Irreps g)) (b :: Obj (Irreps g)) = HomInter
  { unHomInter :: HomInterRep g a b }

-- | Payload of 'HomFused' (closed per group).
type family HomFusedRep (g :: Group) (a :: Obj (Irreps g)) (b :: Obj (Irreps g)) :: Type where
  HomFusedRep SU2 a b =
    FTreeV
      ( FuseFTrees
          (ObjFTrees SU2 (DualObj SU2Th a))
          (ObjFTrees SU2 b)
      )
  HomFusedRep U1 a b =
    FTreeV
      ( FuseFTreesU1
          (ObjFTrees U1 (DualObj U1Th a))
          (ObjFTrees U1 b)
      )

type family HomInterRep (g :: Group) (a :: Obj (Irreps g)) (b :: Obj (Irreps g)) :: Type where
  HomInterRep SU2 a b =
    FTreeV
      ( FilterTrivial
          ( FuseFTrees
              (ObjFTrees SU2 (DualObj SU2Th a))
              (ObjFTrees SU2 b)
          )
      )
  HomInterRep U1 a b =
    FTreeV
      ( FilterTrivial
          ( FuseFTreesU1
              (ObjFTrees U1 (DualObj U1Th a))
              (ObjFTrees U1 b)
          )
      )

-- | Dual-left leaf spine for fused Hom domain (@DualObj a@ after skeletal fuse).
type DualObjFTrees (g :: Group) (a :: Obj (Irreps g)) =
  ObjFTrees g (DualObj (TheoryOf g) a)

--------------------------------------------------------------------------------
-- True unfused Hom on Obj trees (ToVObj SU2 / Dual-left Hom)
--------------------------------------------------------------------------------

-- | Object spaces for 'HomUnfused': 'ToVObj' is a nested Kronecker / pair space.
--
-- Empty methods: this is a constraint bundle. The three instances induct over
-- 'Obj' so callers can write @KnownToVObj SU2 a@ instead of repeating the
-- 'LinearSpace' \/ 'TensorSpace' \/ scalar equalities for every tree shape.
-- (A 'ConstraintKinds' synonym cannot carry those inductive instances.)
class
  ( LinearSpace (ToVObj g a)
  , LinearSpace (DualVector (ToVObj g a))
  , Scalar (ToVObj g a) ~ Complex Double
  , Scalar (DualVector (ToVObj g a)) ~ Complex Double
  , TensorSpace (ToVObj g a)
  , TensorSpace (DualVector (ToVObj g a))
  , TensorSpace (ToVObj g a ⊗ DualVector (ToVObj g a))
  , TensorSpace (DualVector (ToVObj g a) ⊗ ToVObj g a)
  , TensorSpace (ToVObj g ('Irrep (UnitLabG g)))
  ) =>
  KnownToVObj (g :: Group) (a :: Obj (Irreps g))

-- | Monoidal unit label for the group.
type family UnitLabG (g :: Group) :: Irreps g where
  UnitLabG SU2 = 0
  UnitLabG U1 = 'Zero

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  KnownToVObj SU2 ('Irrep j)

instance (KnownToVObj SU2 a, KnownToVObj SU2 b) => KnownToVObj SU2 (a :⊗: b)

instance (KnownToVObj SU2 a, KnownToVObj SU2 b) => KnownToVObj SU2 (a :⊕: b)

instance KnownToVObj U1 ('Irrep j)

instance (KnownToVObj U1 a, KnownToVObj U1 b) => KnownToVObj U1 (a :⊗: b)

instance (KnownToVObj U1 a, KnownToVObj U1 b) => KnownToVObj U1 (a :⊕: b)

-- | Unfused evaluation @ε : a ⊗ a* → 𝟙@ (right dual).
cupUnfusedObj
  :: forall g a
   . ( KnownToVObj g a
     , ToVObj g ('Irrep (UnitLabG g)) ~ C 1
     )
  => (ToVObj g a ⊗ DualVector (ToVObj g a))
  -> ToVObj g ('Irrep (UnitLabG g))
cupUnfusedObj t =
  konst
    ( getLinearFunction
        trace
        (fromTensor -+$=> (swapMap $ t))
    )

-- | Unfused coevaluation @η : 𝟙 → a* ⊗ a@ (right dual; Hom packing).
capUnfusedObj
  :: forall g a
   . ( KnownToVObj g a
     , ToVObj g ('Irrep (UnitLabG g)) ~ C 1
     )
  => ToVObj g ('Irrep (UnitLabG g))
  -> (DualVector (ToVObj g a) ⊗ ToVObj g a)
capUnfusedObj u = unitToVScalar u *^ (swapMap $ idTensor @(ToVObj g a))

-- | Unfused Hom composition: apply Mac Lane ladder once to @f ⊗ g@.
-- @λ ∘ (ε⊗id) ∘ α@.
composeMorObj
  :: forall g a b c
   . ( KnownToVObj g a
     , KnownToVObj g b
     , KnownToVObj g c
     , ToVObj g ('Irrep (UnitLabG g)) ~ C 1
     , TensorSpace ((DualVector (ToVObj g a) ⊗ ToVObj g b))
     , TensorSpace ((DualVector (ToVObj g b) ⊗ ToVObj g c))
     , Scalar ((DualVector (ToVObj g a) ⊗ ToVObj g b)) ~ Complex Double
     , Scalar ((DualVector (ToVObj g b) ⊗ ToVObj g c)) ~ Complex Double
     )
  => (DualVector (ToVObj g a) ⊗ ToVObj g b)
  -> (DualVector (ToVObj g b) ⊗ ToVObj g c)
  -> (DualVector (ToVObj g a) ⊗ ToVObj g c)
composeMorObj f g =
  ( (id ⊗^ lunit @(ToVObj g c))
      . (id ⊗^ (arr (LinearFunction (cupUnfusedObj @g @b)) ⊗^ id))
      . (id ⊗^ lassocMap @(ToVObj g b) @(DualVector (ToVObj g b)) @(ToVObj g c))
      . rassocMap
          @(DualVector (ToVObj g a))
          @(ToVObj g b)
          @(DualVector (ToVObj g b) ⊗ ToVObj g c)
  )
    $ (f ⊗ g)

-- | SU(2) specializations used by Examples smokes (assoc / cup⊗id / unitor steps).
cupTensorIdComposeObj
  :: forall a b c
   . ( KnownToVObj SU2 a
     , KnownToVObj SU2 b
     , KnownToVObj SU2 c
     )
  => DualVector (ToVObj SU2 a) ⊗ ((ToVObj SU2 b ⊗ DualVector (ToVObj SU2 b)) ⊗ ToVObj SU2 c)
  -> DualVector (ToVObj SU2 a) ⊗ (ToVObj SU2 ('Irrep 0) ⊗ ToVObj SU2 c)
cupTensorIdComposeObj t =
  (id ⊗^ (arr (LinearFunction (cupUnfusedObj @SU2 @b)) ⊗^ id)) $ t

unitorComposeObj
  :: forall a c
   . ( KnownToVObj SU2 a
     , KnownToVObj SU2 c
     )
  => DualVector (ToVObj SU2 a) ⊗ (ToVObj SU2 ('Irrep 0) ⊗ ToVObj SU2 c)
  -> (DualVector (ToVObj SU2 a) ⊗ ToVObj SU2 c)
unitorComposeObj t =
  (id ⊗^ lunit @(ToVObj SU2 c)) $ t

--------------------------------------------------------------------------------
-- Category \/ monoidal structure: HomUnfused SU2 (complete)
--------------------------------------------------------------------------------

instance Category (HomUnfused SU2) where
  type Object (HomUnfused SU2) a = KnownToVObj SU2 a

  id :: forall a. Object (HomUnfused SU2) a => HomUnfused SU2 a a
  id = HomUnfused (capUnfusedObj @SU2 @a (konst 1))

  (.)
    :: forall a b c
     . (Object (HomUnfused SU2) a, Object (HomUnfused SU2) b, Object (HomUnfused SU2) c)
    => HomUnfused SU2 b c
    -> HomUnfused SU2 a b
    -> HomUnfused SU2 a c
  HomUnfused g . HomUnfused f =
    HomUnfused (composeMorObj @SU2 @a @b @c f g)

instance PFunctor (:⊗:) (HomUnfused SU2) (HomUnfused SU2) where
  first
    :: forall a b c
     . ( Object (HomUnfused SU2) a
       , Object (HomUnfused SU2) b
       , Object (HomUnfused SU2) c
       , Object (HomUnfused SU2) (a :⊗: c)
       , Object (HomUnfused SU2) (b :⊗: c)
       )
    => HomUnfused SU2 a b
    -> HomUnfused SU2 (a :⊗: c) (b :⊗: c)
  first (HomUnfused f) =
    let m :: ToVObj SU2 (a :⊗: c) +> ToVObj SU2 (b :⊗: c)
        m = (fromTensor -+$=> f) ⊗^ id
     in HomUnfused (asTensor -+$=> m)

instance QFunctor (:⊗:) (HomUnfused SU2) (HomUnfused SU2) where
  second
    :: forall a b c
     . ( Object (HomUnfused SU2) a
       , Object (HomUnfused SU2) b
       , Object (HomUnfused SU2) c
       , Object (HomUnfused SU2) (c :⊗: a)
       , Object (HomUnfused SU2) (c :⊗: b)
       )
    => HomUnfused SU2 a b
    -> HomUnfused SU2 (c :⊗: a) (c :⊗: b)
  second (HomUnfused g) =
    let m :: ToVObj SU2 (c :⊗: a) +> ToVObj SU2 (c :⊗: b)
        m = id ⊗^ (fromTensor -+$=> g)
     in HomUnfused (asTensor -+$=> m)

-- | @bimap f g@ is the Kronecker product of the underlying linear maps,
-- packed Dual-left: @(unpack f) ⊗^ (unpack g)@.
instance Bifunctor (:⊗:) (HomUnfused SU2) (HomUnfused SU2) (HomUnfused SU2) where
  bimap
    :: forall a b c d
     . ( Object (HomUnfused SU2) a
       , Object (HomUnfused SU2) b
       , Object (HomUnfused SU2) c
       , Object (HomUnfused SU2) d
       , Object (HomUnfused SU2) (a :⊗: c)
       , Object (HomUnfused SU2) (b :⊗: d)
       )
    => HomUnfused SU2 a b
    -> HomUnfused SU2 c d
    -> HomUnfused SU2 (a :⊗: c) (b :⊗: d)
  bimap (HomUnfused f) (HomUnfused g) =
    let m :: ToVObj SU2 (a :⊗: c) +> ToVObj SU2 (b :⊗: d)
        m = (fromTensor -+$=> f) ⊗^ (fromTensor -+$=> g)
     in HomUnfused (asTensor -+$=> m)

-- | Object associator is linearmap @α@ (Kronecker reassociation), packed as Hom.
instance Associative (HomUnfused SU2) (:⊗:) where
  associate
    :: forall a b c
     . ( Object (HomUnfused SU2) a
       , Object (HomUnfused SU2) b
       , Object (HomUnfused SU2) c
       , Object (HomUnfused SU2) (a :⊗: b)
       , Object (HomUnfused SU2) (b :⊗: c)
       , Object (HomUnfused SU2) ((a :⊗: b) :⊗: c)
       , Object (HomUnfused SU2) (a :⊗: (b :⊗: c))
       )
    => HomUnfused SU2 ((a :⊗: b) :⊗: c) (a :⊗: (b :⊗: c))
  associate =
    HomUnfused
      ( asTensor -+$=>
          (rassocMap @(ToVObj SU2 a) @(ToVObj SU2 b) @(ToVObj SU2 c))
      )

  disassociate
    :: forall a b c
     . ( Object (HomUnfused SU2) a
       , Object (HomUnfused SU2) b
       , Object (HomUnfused SU2) c
       , Object (HomUnfused SU2) (a :⊗: b)
       , Object (HomUnfused SU2) (b :⊗: c)
       , Object (HomUnfused SU2) ((a :⊗: b) :⊗: c)
       , Object (HomUnfused SU2) (a :⊗: (b :⊗: c))
       )
    => HomUnfused SU2 (a :⊗: (b :⊗: c)) ((a :⊗: b) :⊗: c)
  disassociate =
    HomUnfused
      ( asTensor -+$=>
          (lassocMap @(ToVObj SU2 a) @(ToVObj SU2 b) @(ToVObj SU2 c))
      )

instance Monoidal (HomUnfused SU2) (:⊗:) where
  type Id (HomUnfused SU2) (:⊗:) = 'Irrep 0

  idl
    :: forall a
     . ( Object (HomUnfused SU2) a
       , Object (HomUnfused SU2) ('Irrep 0)
       , Object (HomUnfused SU2) ('Irrep 0 :⊗: a)
       )
    => HomUnfused SU2 ('Irrep 0 :⊗: a) a
  idl =
    HomUnfused (asTensor -+$=> (lunit @(ToVObj SU2 a)))

  idr
    :: forall a
     . ( Object (HomUnfused SU2) a
       , Object (HomUnfused SU2) ('Irrep 0)
       , Object (HomUnfused SU2) (a :⊗: 'Irrep 0)
       )
    => HomUnfused SU2 (a :⊗: 'Irrep 0) a
  idr =
    HomUnfused (asTensor -+$=> (runit @(ToVObj SU2 a)))

  coidl
    :: forall a
     . ( Object (HomUnfused SU2) a
       , Object (HomUnfused SU2) ('Irrep 0)
       , Object (HomUnfused SU2) ('Irrep 0 :⊗: a)
       )
    => HomUnfused SU2 a ('Irrep 0 :⊗: a)
  coidl =
    HomUnfused (asTensor -+$=> (lunitInv @(ToVObj SU2 a)))

  coidr
    :: forall a
     . ( Object (HomUnfused SU2) a
       , Object (HomUnfused SU2) ('Irrep 0)
       , Object (HomUnfused SU2) (a :⊗: 'Irrep 0)
       )
    => HomUnfused SU2 a (a :⊗: 'Irrep 0)
  coidr =
    HomUnfused (asTensor -+$=> (runitInv @(ToVObj SU2 a)))

instance Braided (HomUnfused SU2) (:⊗:) where
  braid
    :: forall a b
     . ( Object (HomUnfused SU2) a
       , Object (HomUnfused SU2) b
       , Object (HomUnfused SU2) (a :⊗: b)
       , Object (HomUnfused SU2) (b :⊗: a)
       )
    => HomUnfused SU2 (a :⊗: b) (b :⊗: a)
  braid =
    let m :: ToVObj SU2 (a :⊗: b) +> ToVObj SU2 (b :⊗: a)
        m = swapMap @(ToVObj SU2 a) @(ToVObj SU2 b)
     in HomUnfused (asTensor -+$=> m)

--------------------------------------------------------------------------------
-- HomUnfused U1 (Category + monoidal; carriers are C 1)
--------------------------------------------------------------------------------

instance Category (HomUnfused U1) where
  type Object (HomUnfused U1) a = KnownToVObj U1 a

  id :: forall a. Object (HomUnfused U1) a => HomUnfused U1 a a
  id = HomUnfused (capUnfusedObj @U1 @a (konst 1))

  (.)
    :: forall a b c
     . (Object (HomUnfused U1) a, Object (HomUnfused U1) b, Object (HomUnfused U1) c)
    => HomUnfused U1 b c
    -> HomUnfused U1 a b
    -> HomUnfused U1 a c
  HomUnfused g . HomUnfused f =
    HomUnfused (composeMorObj @U1 @a @b @c f g)

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

-- | Step 1: @f ⊗ g@ is 'fuseFTreesTerm' (inlined at 'composeHomTrees').
-- Step 2: outer F — @(a*⊗b) ⊗ (b*⊗c) → a* ⊗ (b ⊗ (b*⊗c))@ via 'fmoveOuterHom'.
-- ('fmoveInnerHom' is the subsequent @id ⊗ F@ via 'idRight' 'fmoveInvTrees'.)

-- | Step 3: @id ⊗ F@ — @a* ⊗ (b ⊗ (b*⊗c)) → a* ⊗ ((b ⊗ b*) ⊗ c)@.
--
-- Right factor: @FuseFTrees b (FuseFTrees b c) → FuseFTrees (FuseFTrees b b) c@ via 'fmoveInvTrees'.
fmoveInnerHom
  :: forall a b c
   . ( KnownFTrees a
     , KnownFTrees (FuseFTrees b (FuseFTrees b c))
     , KnownFTrees (FuseFTrees (FuseFTrees b b) c)
     , KnownFTrees (FuseFTrees a (FuseFTrees b (FuseFTrees b c)))
     , KnownFTrees (FuseFTrees a (FuseFTrees (FuseFTrees b b) c))
     )
  => FTreeV (FuseFTrees a (FuseFTrees b (FuseFTrees b c)))
  -> FTreeV (FuseFTrees a (FuseFTrees (FuseFTrees b b) c))
fmoveInnerHom =
  idRight
    @a
    @(FuseFTrees b (FuseFTrees b c))
    @(FuseFTrees (FuseFTrees b b) c)
    (fmoveInvTrees @b @b @c)

-- | Evaluation @ε : b ⊗ b* → 𝟙@ on genealogy Hom (@FuseFTrees b b@, dual≅primal).
--
-- Interim: singlet walk on 'SFTrees' (scale by 'cupCoeff' @SU2Th@). True η/ε
-- morphisms once typed per-channel F replaces Fusion.SU2 flats (blocker: channel
-- morphisms on @C (d+1)@).
cup
  :: forall b
   . KnownFTrees (FuseFTrees b b)
  => FTreeV (FuseFTrees b b)
  -> FTreeV Unit
cup bb =
  FCons @('IrrepTree 0) (konst (cupHomTreesScalar @(FuseFTrees b b) bb)) FNil
  where
    -- Singlet walk via 'SFTrees': @sameNat@ refines @j ~ 0@ so payloads stay @C 1@.
    cupHomTreesScalar
      :: forall (ts :: FTrees Nat)
       . KnownFTrees ts
      => FTreeV ts
      -> Complex Double
    cupHomTreesScalar = go (fTreesSing @_ @ts)
      where
        go :: forall (ts' :: FTrees Nat). SFTrees ts' -> FTreeV ts' -> Complex Double
        go SFTreesNil FNil = 0
        go (SFTreesCons t rest) (FCons v rs) =
          case t of
            SIrrepTree @_ @j ->
              case sameNat (Proxy @j) (Proxy @0) of
                Just Refl -> (konst 1 <.> v) + go rest rs
                Nothing -> go rest rs
            SFrom @_ @j l _r ->
              case sameNat (Proxy @j) (Proxy @0) of
                Just Refl ->
                  cupCoeff (Proxy @SU2Th) (rootLab l) * (konst 1 <.> v) + go rest rs
                Nothing -> go rest rs

-- | Stub: CompactClosed-shaped counit @ε : a ⊗ Dual a → 𝟙@ as a 'HomFused' morphism
-- (Fib 'cupObj' / 'Categorical.CompactClosed.counit' shape). Contrast spine-applied
-- 'cup' (@FTreeV (FuseFTrees b b) → FTreeV Unit@). Body TBD — type sketch only.
cup'
  :: forall a
   . ( Object (HomFused SU2) a
     , Object (HomFused SU2) (DualObj SU2Th a)
     , Object (HomFused SU2) (a :⊗: DualObj SU2Th a)
     , Object (HomFused SU2) ('Irrep 0)
     )
  => HomFused SU2 (a :⊗: DualObj SU2Th a) ('Irrep 0)
cup' = undefined

-- | Step 5: @id ⊗ λ@ — @a* ⊗ (Unit ⊗ c) → a* ⊗ c@ (not type-level absorption).
unitorHom
  :: forall a c
   . ( KnownFTrees a
     , KnownFTrees c
     , KnownFTrees (FuseFTrees Unit c)
     , KnownFTrees (FuseFTrees a (FuseFTrees Unit c))
     , KnownFTrees (FuseFTrees a c)
     , UnitorCodomain (FuseFTrees Unit c) ~ c
     )
  => FTreeV (FuseFTrees a (FuseFTrees Unit c))
  -> FTreeV (FuseFTrees a c)
unitorHom =
  idRight @a @(FuseFTrees Unit c) @c (unitor @c)

-- | Left unitor on fusion trees: @Unit ⊗ c → c@ (drop @'IrrepTree 0@ left child).
--
-- For each @t@ in @c@, @FuseTrees ('IrrepTree 0) t = '[ 'From (Root t) '( 'IrrepTree 0, t) ]@
-- (SU(2): @0 ⊗ j = j@); payloads are already the root irrep of @t@.
unitor
  :: forall c
   . ( KnownFTrees (FuseFTrees Unit c)
     , UnitorCodomain (FuseFTrees Unit c) ~ c
     )
  => FTreeV (FuseFTrees Unit c)
  -> FTreeV c
unitor = go (fTreesSing @_ @(FuseFTrees Unit c))
  where
    -- @sameNat@ refines left child to @'IrrepTree 0@; 'UnitorCodomain' drops it.
    go
      :: forall (uc :: FTrees Nat)
       . SFTrees uc
      -> FTreeV uc
      -> FTreeV (UnitorCodomain uc)
    go SFTreesNil FNil = FNil
    go (SFTreesCons t rest) (FCons v rs) =
      case t of
        SFrom @_ @j l r ->
          case l of
            SIrrepTree @_ @zj ->
              case sameNat (Proxy @zj) (Proxy @0) of
                Just Refl ->
                  case r of
                    SIrrepTree @_ @rj ->
                      case sameNat (Proxy @rj) (Proxy @j) of
                        Just Refl ->
                          FCons @('IrrepTree rj) v (go rest rs)
                        Nothing ->
                          error "unitor: root mismatch after 0⊗t"
                    SFrom @_ @rj (rlSing :: SFTree rl) (rrSing :: SFTree rr) ->
                      case sameNat (Proxy @rj) (Proxy @j) of
                        Just Refl ->
                          FCons @('From rj '(rl, rr)) v (go rest rs)
                        Nothing ->
                          error "unitor: root mismatch after 0⊗t"
                Nothing ->
                  error "unitor: expected left child 'IrrepTree 0"
            SFrom {} ->
              error "unitor: expected left child 'IrrepTree 0"
        SIrrepTree {} ->
          error "unitor: expected From from FuseFTrees Unit"

-- | Fused Hom compose as the five Mac Lane morphisms.
composeHomTrees
  :: forall a b c
   . ( KnownHomTrees a b
     , KnownHomTrees b c
     , KnownHomTrees a c
     , KnownHomTrees (FuseFTrees a b) (FuseFTrees b c)
     , KnownFTrees (FuseFTrees b b)
     , KnownFTrees (FuseFTrees b (FuseFTrees b c))
     , KnownFTrees (FuseFTrees (FuseFTrees b b) c)
     , KnownFTrees (FuseFTrees Unit c)
     , KnownFTrees (FuseFTrees a (FuseFTrees b (FuseFTrees b c)))
     , KnownFTrees (FuseFTrees a (FuseFTrees (FuseFTrees b b) c))
     , KnownFTrees (FuseFTrees a (FuseFTrees Unit c))
     , UnitorCodomain (FuseFTrees Unit c) ~ c
     )
  => FTreeV (FuseFTrees a b)
  -> FTreeV (FuseFTrees b c)
  -> FTreeV (FuseFTrees a c)
composeHomTrees f g =
  unitorHom @a @c
    ( idRight @a @(FuseFTrees (FuseFTrees b b) c) @(FuseFTrees Unit c)
        (idLeft @(FuseFTrees b b) @Unit @c (cup @b))
        ( fmoveInnerHom @a @b @c
            ( fmoveOuterHom @a @b @c
                (fuseFTreesTerm @(FuseFTrees a b) @(FuseFTrees b c) f g)
            )
        )
    )

--------------------------------------------------------------------------------
-- HomFused: FTreeV-backed fused Hom
--------------------------------------------------------------------------------

-- | 'HomFused' compose via the five Mac Lane morphisms ('composeHomTrees')
-- on 'ObjFTrees'-expanded leaf reps.
composeHomFused
  :: forall a b c
   . ( DualObjFTrees SU2 b ~ ObjFTrees SU2 b
     , KnownHomTrees (DualObjFTrees SU2 a) (ObjFTrees SU2 b)
     , KnownHomTrees (ObjFTrees SU2 b) (ObjFTrees SU2 c)
     , KnownHomTrees (DualObjFTrees SU2 a) (ObjFTrees SU2 c)
     , KnownHomTrees
         (FuseFTrees (DualObjFTrees SU2 a) (ObjFTrees SU2 b))
         (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 c))
     , KnownFTrees (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 b))
     , KnownFTrees (FuseFTrees (ObjFTrees SU2 b) (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 c)))
     , KnownFTrees (FuseFTrees (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 b)) (ObjFTrees SU2 c))
     , KnownFTrees (FuseFTrees Unit (ObjFTrees SU2 c))
     , KnownFTrees (FuseFTrees (DualObjFTrees SU2 a) (FuseFTrees (ObjFTrees SU2 b) (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 c))))
     , KnownFTrees (FuseFTrees (DualObjFTrees SU2 a) (FuseFTrees (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 b)) (ObjFTrees SU2 c)))
     , KnownFTrees (FuseFTrees (DualObjFTrees SU2 a) (FuseFTrees Unit (ObjFTrees SU2 c)))
     , UnitorCodomain (FuseFTrees Unit (ObjFTrees SU2 c)) ~ ObjFTrees SU2 c
     )
  => HomFused SU2 b c
  -> HomFused SU2 a b
  -> HomFused SU2 a c
composeHomFused (HomFused g) (HomFused f) =
  HomFused
    ( composeHomTrees
        @(DualObjFTrees SU2 a)
        @(ObjFTrees SU2 b)
        @(ObjFTrees SU2 c)
        f
        g
    )

instance Category (HomFused SU2) where
  type Object (HomFused SU2) a =
    ( DualObjFTrees SU2 a ~ ObjFTrees SU2 a
    , KnownFTrees (ObjFTrees SU2 a)
    , FuseFTreesIdC (ObjFTrees SU2 a) (ObjFTrees SU2 a)
    )

  id :: forall a. Object (HomFused SU2) a => HomFused SU2 a a
  id = HomFused (idHomFTrees @(ObjFTrees SU2 a))

  -- @(.)@ needs the five Mac Lane steps on @a,b,c@, which 'Object' alone does
  -- not imply (constraints are triple-indexed). Named ladder: 'composeHomFused'.
  (.) = undefined

--------------------------------------------------------------------------------
-- HomInter: trivial sector of fused Hom (same Mac Lane compose)
--------------------------------------------------------------------------------

-- | Identity intertwiner: trivial channels of @'idHomFTrees' (ObjFTrees SU2 a)@.
idHomInterVal
  :: forall a
   . ( DualObjFTrees SU2 a ~ ObjFTrees SU2 a
     , KnownFTrees (ObjFTrees SU2 a)
     , FuseFTreesIdC (ObjFTrees SU2 a) (ObjFTrees SU2 a)
     , KnownFTrees (FuseFTrees (ObjFTrees SU2 a) (ObjFTrees SU2 a))
     )
  => FTreeV (FilterTrivial (FuseFTrees (ObjFTrees SU2 a) (ObjFTrees SU2 a)))
idHomInterVal =
  filterTrivialFTreeV @(FuseFTrees (ObjFTrees SU2 a) (ObjFTrees SU2 a)) (idHomFTrees @(ObjFTrees SU2 a))

-- | 'HomInter' compose: embed → 'composeHomTrees' → filter (same as 'HomFused').
composeHomInter
  :: forall a b c
   . ( DualObjFTrees SU2 b ~ ObjFTrees SU2 b
     , KnownHomTrees (DualObjFTrees SU2 a) (ObjFTrees SU2 b)
     , KnownHomTrees (ObjFTrees SU2 b) (ObjFTrees SU2 c)
     , KnownHomTrees (DualObjFTrees SU2 a) (ObjFTrees SU2 c)
     , KnownHomTrees
         (FuseFTrees (DualObjFTrees SU2 a) (ObjFTrees SU2 b))
         (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 c))
     , KnownFTrees (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 b))
     , KnownFTrees (FuseFTrees (ObjFTrees SU2 b) (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 c)))
     , KnownFTrees (FuseFTrees (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 b)) (ObjFTrees SU2 c))
     , KnownFTrees (FuseFTrees Unit (ObjFTrees SU2 c))
     , KnownFTrees
         ( FuseFTrees
             (DualObjFTrees SU2 a)
             (FuseFTrees (ObjFTrees SU2 b) (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 c)))
         )
     , KnownFTrees
         ( FuseFTrees
             (DualObjFTrees SU2 a)
             (FuseFTrees (FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 b)) (ObjFTrees SU2 c))
         )
     , KnownFTrees (FuseFTrees (DualObjFTrees SU2 a) (FuseFTrees Unit (ObjFTrees SU2 c)))
     , UnitorCodomain (FuseFTrees Unit (ObjFTrees SU2 c)) ~ ObjFTrees SU2 c
     )
  => HomInter SU2 b c
  -> HomInter SU2 a b
  -> HomInter SU2 a c
composeHomInter (HomInter g) (HomInter f) =
  HomInter $
    filterTrivialFTreeV @(FuseFTrees (DualObjFTrees SU2 a) (ObjFTrees SU2 c)) $
      composeHomTrees @(DualObjFTrees SU2 a) @(ObjFTrees SU2 b) @(ObjFTrees SU2 c)
        (embedTrivialFTreeV @(FuseFTrees (DualObjFTrees SU2 a) (ObjFTrees SU2 b)) f)
        (embedTrivialFTreeV @(FuseFTrees (ObjFTrees SU2 b) (ObjFTrees SU2 c)) g)

instance Category (HomInter SU2) where
  type Object (HomInter SU2) a =
    ( DualObjFTrees SU2 a ~ ObjFTrees SU2 a
    , KnownFTrees (ObjFTrees SU2 a)
    , FuseFTreesIdC (ObjFTrees SU2 a) (ObjFTrees SU2 a)
    , KnownFTrees (FuseFTrees (ObjFTrees SU2 a) (ObjFTrees SU2 a))
    )

  id :: forall a. Object (HomInter SU2) a => HomInter SU2 a a
  id = HomInter (idHomInterVal @a)

  -- Same as 'HomFused': use 'composeHomInter' (needs Mac Lane constraints).
  (.) = undefined

