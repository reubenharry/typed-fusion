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
{- HLINT ignore "Eta reduce" -}

-- | Term-level symbolic SU(2): cups, Hom, Mac Lane compose.
--
-- Singletons: 'Hom.Singletons'.
-- 'RepV' / fuse: 'Hom.RepV'.
-- F-moves / fuseMap: 'Hom.FMove'.
-- Concrete spines + smokes: 'Hom.Smoke'.
--
-- Layers: 'Obj' → 'HomUnfused' (Kronecker); 'Obj' → 'HomFused' via
-- 'ObjSpineSU2' / 'ObjRep' with genealogy 'RepV' / 'FuseRep' morphisms;
-- 'HomInter' = trivial sector of fused Hom (same compose via embed/filter).
-- Cups: genealogy 'cup' / 'capUnfusedObj'.
module Hom.Core where

import Data.Complex (Complex ((:+)), conjugate, magnitude, realPart)
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.VectorSpace (InnerSpace ((<.>)), Scalar, VectorSpace ((*^)))
import GHC.TypeLits (KnownNat, Nat, sameNat, type (+))
import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..))
import Categorical.Associative (Associative (..))
import Categorical.Bifunctor (Bifunctor (..), PFunctor (..), QFunctor (..))
import Categorical.Braided (Braided (..))
import Categorical.Monoidal (Monoidal (..))
import Fusion.Obj (Obj (Atom, (:⊗:), (:⊕:)))
import Hom.Expr
import Hom.FMove
import Hom.RepV
import Hom.Singletons
import Hom.TypeLevel
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
-- Hom elements are Dual-left @Dual(ToVObj a) ⊗ ToVObj b@. Unitors below are
-- shared with the Monoidal instance; Obj cups use 'ToVObj'.
--------------------------------------------------------------------------------

-- | Unfused morphisms @a → b@: Dual-left packing on tree spaces
-- @Dual(ToVObj a) ⊗ ToVObj b@ (linearmap Kronecker packing).
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

--------------------------------------------------------------------------------
-- True unfused Hom on Obj trees (ToVObj / Dual-left Hom)
--------------------------------------------------------------------------------

-- | Object spaces for 'HomUnfused': 'ToVObj' is a nested Kronecker / pair space.
--
-- Empty methods: this is a constraint bundle. The three instances induct over
-- 'Obj' so callers can write @KnownToVObj a@ instead of repeating the
-- 'LinearSpace' \/ 'TensorSpace' \/ scalar equalities for every tree shape.
-- (A 'ConstraintKinds' synonym cannot carry those inductive instances.)
class
  ( LinearSpace (ToVObj a)
  , LinearSpace (DualVector (ToVObj a))
  , Scalar (ToVObj a) ~ Complex Double
  , Scalar (DualVector (ToVObj a)) ~ Complex Double
  , TensorSpace (ToVObj a)
  , TensorSpace (DualVector (ToVObj a))
  , TensorSpace (ToVObj a ⊗ DualVector (ToVObj a))
  , TensorSpace (DualVector (ToVObj a) ⊗ ToVObj a)
  , TensorSpace (ToVObj ('Atom 0))
  ) =>
  KnownToVObj (a :: Obj Nat)

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  KnownToVObj ('Atom j)

instance (KnownToVObj a, KnownToVObj b) => KnownToVObj (a :⊗: b)

instance (KnownToVObj a, KnownToVObj b) => KnownToVObj (a :⊕: b)

-- | Unfused evaluation @ε : a ⊗ a* → 𝟙@ (right dual).
cupUnfusedObj
  :: forall a
   . KnownToVObj a
  => (ToVObj a ⊗ DualVector (ToVObj a))
  -> ToVObj ('Atom 0)
cupUnfusedObj t =
  konst
    ( getLinearFunction
        trace
        (fromTensor -+$=> (swapMap $ t))
    )

-- | Unfused coevaluation @η : 𝟙 → a* ⊗ a@ (right dual; Hom packing).
capUnfusedObj
  :: forall a
   . KnownToVObj a
  => ToVObj ('Atom 0)
  -> (DualVector (ToVObj a) ⊗ ToVObj a)
capUnfusedObj u = unitToVScalar u *^ (swapMap $ idTensor @(ToVObj a))

assocComposeObj
  :: forall a b c
   . ( KnownToVObj a
     , KnownToVObj b
     , KnownToVObj c
     )
  => (DualVector (ToVObj a) ⊗ ToVObj b) ⊗ (DualVector (ToVObj b) ⊗ ToVObj c)
  -> DualVector (ToVObj a) ⊗ ((ToVObj b ⊗ DualVector (ToVObj b)) ⊗ ToVObj c)
assocComposeObj t =
  ( (id ⊗^ lassocMap @(ToVObj b) @(DualVector (ToVObj b)) @(ToVObj c))
      . rassocMap
          @(DualVector (ToVObj a))
          @(ToVObj b)
          @(DualVector (ToVObj b) ⊗ ToVObj c)
  )
    $ t

cupTensorIdComposeObj
  :: forall a b c
   . ( KnownToVObj a
     , KnownToVObj b
     , KnownToVObj c
     )
  => DualVector (ToVObj a) ⊗ ((ToVObj b ⊗ DualVector (ToVObj b)) ⊗ ToVObj c)
  -> DualVector (ToVObj a) ⊗ (ToVObj ('Atom 0) ⊗ ToVObj c)
cupTensorIdComposeObj t =
  (id ⊗^ (arr (LinearFunction (cupUnfusedObj @b)) ⊗^ id)) $ t

unitorComposeObj
  :: forall a c
   . ( KnownToVObj a
     , KnownToVObj c
     )
  => DualVector (ToVObj a) ⊗ (ToVObj ('Atom 0) ⊗ ToVObj c)
  -> (DualVector (ToVObj a) ⊗ ToVObj c)
unitorComposeObj t =
  (id ⊗^ lunit @(ToVObj c)) $ t

-- | Unfused Hom composition: apply Mac Lane ladder once to @f ⊗ g@.
-- @λ ∘ (ε⊗id) ∘ α@.
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
  ( (id ⊗^ lunit @(ToVObj c))
      . (id ⊗^ (arr (LinearFunction (cupUnfusedObj @b)) ⊗^ id))
      . (id ⊗^ lassocMap @(ToVObj b) @(DualVector (ToVObj b)) @(ToVObj c))
      . rassocMap
          @(DualVector (ToVObj a))
          @(ToVObj b)
          @(DualVector (ToVObj b) ⊗ ToVObj c)
  )
    $ (f ⊗ g)

--------------------------------------------------------------------------------
-- Category \/ monoidal structure: HomUnfused (complete)
--------------------------------------------------------------------------------

instance Category HomUnfused where
  type Object HomUnfused a = KnownToVObj a

  id :: forall a. Object HomUnfused a => HomUnfused a a
  id = HomUnfused (capUnfusedObj @a (konst 1))

  (.)
    :: forall a b c
     . (Object HomUnfused a, Object HomUnfused b, Object HomUnfused c)
    => HomUnfused b c
    -> HomUnfused a b
    -> HomUnfused a c
  HomUnfused g . HomUnfused f =
    HomUnfused (composeMorObj @a @b @c f g)

instance PFunctor (:⊗:) HomUnfused HomUnfused where
  first
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (a :⊗: c)
       , Object HomUnfused (b :⊗: c)
       )
    => HomUnfused a b
    -> HomUnfused (a :⊗: c) (b :⊗: c)
  first (HomUnfused f) =
    let m :: ToVObj (a :⊗: c) +> ToVObj (b :⊗: c)
        m = (fromTensor -+$=> f) ⊗^ id
     in HomUnfused (asTensor -+$=> m)

instance QFunctor (:⊗:) HomUnfused HomUnfused where
  second
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (c :⊗: a)
       , Object HomUnfused (c :⊗: b)
       )
    => HomUnfused a b
    -> HomUnfused (c :⊗: a) (c :⊗: b)
  second (HomUnfused g) =
    let m :: ToVObj (c :⊗: a) +> ToVObj (c :⊗: b)
        m = id ⊗^ (fromTensor -+$=> g)
     in HomUnfused (asTensor -+$=> m)

-- | @bimap f g@ is the Kronecker product of the underlying linear maps,
-- packed Dual-left: @(unpack f) ⊗^ (unpack g)@.
instance Bifunctor (:⊗:) HomUnfused HomUnfused HomUnfused where
  bimap
    :: forall a b c d
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused d
       , Object HomUnfused (a :⊗: c)
       , Object HomUnfused (b :⊗: d)
       )
    => HomUnfused a b
    -> HomUnfused c d
    -> HomUnfused (a :⊗: c) (b :⊗: d)
  bimap (HomUnfused f) (HomUnfused g) =
    let m :: ToVObj (a :⊗: c) +> ToVObj (b :⊗: d)
        m = (fromTensor -+$=> f) ⊗^ (fromTensor -+$=> g)
     in HomUnfused (asTensor -+$=> m)

-- | Object associator is linearmap @α@ (Kronecker reassociation), packed as Hom.
instance Associative HomUnfused (:⊗:) where
  associate
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (a :⊗: b)
       , Object HomUnfused (b :⊗: c)
       , Object HomUnfused ((a :⊗: b) :⊗: c)
       , Object HomUnfused (a :⊗: (b :⊗: c))
       )
    => HomUnfused ((a :⊗: b) :⊗: c) (a :⊗: (b :⊗: c))
  associate =
    HomUnfused
      ( asTensor -+$=>
          (rassocMap @(ToVObj a) @(ToVObj b) @(ToVObj c))
      )

  disassociate
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (a :⊗: b)
       , Object HomUnfused (b :⊗: c)
       , Object HomUnfused ((a :⊗: b) :⊗: c)
       , Object HomUnfused (a :⊗: (b :⊗: c))
       )
    => HomUnfused (a :⊗: (b :⊗: c)) ((a :⊗: b) :⊗: c)
  disassociate =
    HomUnfused
      ( asTensor -+$=>
          (lassocMap @(ToVObj a) @(ToVObj b) @(ToVObj c))
      )

instance Monoidal HomUnfused (:⊗:) where
  type Id HomUnfused (:⊗:) = 'Atom 0

  idl
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('Atom 0)
       , Object HomUnfused ('Atom 0 :⊗: a)
       )
    => HomUnfused ('Atom 0 :⊗: a) a
  idl =
    HomUnfused (asTensor -+$=> (lunit @(ToVObj a)))

  idr
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('Atom 0)
       , Object HomUnfused (a :⊗: 'Atom 0)
       )
    => HomUnfused (a :⊗: 'Atom 0) a
  idr =
    HomUnfused (asTensor -+$=> (runit @(ToVObj a)))

  coidl
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('Atom 0)
       , Object HomUnfused ('Atom 0 :⊗: a)
       )
    => HomUnfused a ('Atom 0 :⊗: a)
  coidl =
    HomUnfused (asTensor -+$=> (lunitInv @(ToVObj a)))

  coidr
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('Atom 0)
       , Object HomUnfused (a :⊗: 'Atom 0)
       )
    => HomUnfused a (a :⊗: 'Atom 0)
  coidr =
    HomUnfused (asTensor -+$=> (runitInv @(ToVObj a)))

instance Braided HomUnfused (:⊗:) where
  braid
    :: forall a b
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused (a :⊗: b)
       , Object HomUnfused (b :⊗: a)
       )
    => HomUnfused (a :⊗: b) (b :⊗: a)
  braid =
    let m :: ToVObj (a :⊗: b) +> ToVObj (b :⊗: a)
        m = swapMap @(ToVObj a) @(ToVObj b)
     in HomUnfused (asTensor -+$=> m)

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

-- | Step 1: @f ⊗ g@ is 'fuseRepTerm' (inlined at 'composeHomTrees').
-- Step 2: outer F — @(a*⊗b) ⊗ (b*⊗c) → a* ⊗ (b ⊗ (b*⊗c))@.
--
-- Discharged by 'CanFmoveOuterHom' (leaf instance → 'fmoveOuterHomLeaves').
-- ('fmoveInnerHom' is the subsequent @id ⊗ F@ via 'fuseMapRight' 'fmoveInvTrees'.)

-- | Step 3: @id ⊗ F@ — @a* ⊗ (b ⊗ (b*⊗c)) → a* ⊗ ((b ⊗ b*) ⊗ c)@.
--
-- Right factor: @FuseRep b (FuseRep b c) → FuseRep (FuseRep b b) c@ via 'fmoveInvTrees'.
fmoveInnerHom
  :: forall a b c
   . ( KnownFTrees a
     , KnownFTrees (FuseRep b (FuseRep b c))
     , KnownFTrees (FuseRep (FuseRep b b) c)
     , KnownFTrees (FuseRep a (FuseRep b (FuseRep b c)))
     , KnownFTrees (FuseRep a (FuseRep (FuseRep b b) c))
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
   . ( KnownFTrees a
     , KnownFTrees b
     , KnownFTrees c
     , KnownFTrees (FuseRep b b)
     , KnownFTrees Unit
     , KnownFTrees (FuseRep (FuseRep b b) c)
     , KnownFTrees (FuseRep Unit c)
     , KnownFTrees (FuseRep a (FuseRep (FuseRep b b) c))
     , KnownFTrees (FuseRep a (FuseRep Unit c))
     , KnownFTrees (FuseRep b b)
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
--
-- Interim: singlet walk on 'SFTrees' (scale by FS·dim). True η/ε morphisms once
-- typed per-channel F replaces Fusion.SU2 flats (blocker: channel morphisms on
-- @C (d+1)@).
cup
  :: forall b
   . KnownFTrees (FuseRep b b)
  => RepV (FuseRep b b)
  -> RepV Unit
cup bb =
  RCons @('I 0) (konst (cupHomTreesScalar @(FuseRep b b) bb)) RNil
  where
    -- Singlet walk via 'SFTrees': @sameNat@ refines @j ~ 0@ so payloads stay @C 1@.
    cupHomTreesScalar
      :: forall ts
       . KnownFTrees ts
      => RepV ts
      -> Complex Double
    cupHomTreesScalar = go (fTreesSing @ts)
      where
        go :: forall ts'. SFTrees ts' -> RepV ts' -> Complex Double
        go SFTreesNil RNil = 0
        go (SFTreesCons t rest) (RCons v rs) =
          case t of
            SI @j ->
              case sameNat (Proxy @j) (Proxy @0) of
                Just Refl -> (konst 1 <.> v) + go rest rs
                Nothing -> go rest rs
            SFrom @j l _r ->
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
   . ( KnownFTrees a
     , KnownFTrees c
     , KnownFTrees (FuseRep Unit c)
     , KnownFTrees (FuseRep a (FuseRep Unit c))
     , KnownFTrees (FuseRep a c)
     , UnitorCodomain (FuseRep Unit c) ~ c
     )
  => RepV (FuseRep a (FuseRep Unit c))
  -> RepV (FuseRep a c)
unitorHom =
  fuseMapRight @a @(FuseRep Unit c) @c (unitor @c)

-- | Left unitor on fusion trees: @Unit ⊗ c → c@ (drop @'I 0@ left child).
--
-- For each @t@ in @c@, @FuseTrees ('I 0) t = '[ 'From (Root t) '( 'I 0, t) ]@
-- (SU(2): @0 ⊗ j = j@); payloads are already the root irrep of @t@.
unitor
  :: forall c
   . ( KnownFTrees (FuseRep Unit c)
     , UnitorCodomain (FuseRep Unit c) ~ c
     )
  => RepV (FuseRep Unit c)
  -> RepV c
unitor = go (fTreesSing @(FuseRep Unit c))
  where
    -- @sameNat@ refines left child to @'I 0@; 'UnitorCodomain' drops it.
    go
      :: forall uc
       . SFTrees uc
      -> RepV uc
      -> RepV (UnitorCodomain uc)
    go SFTreesNil RNil = RNil
    go (SFTreesCons t rest) (RCons v rs) =
      case t of
        SFrom @j l r ->
          case l of
            SI @zj ->
              case sameNat (Proxy @zj) (Proxy @0) of
                Just Refl ->
                  case r of
                    SI @rj ->
                      case sameNat (Proxy @rj) (Proxy @j) of
                        Just Refl ->
                          RCons @('I rj) v (go rest rs)
                        Nothing ->
                          error "unitor: root mismatch after 0⊗t"
                    SFrom @rj @rl @rr _l _r ->
                      case sameNat (Proxy @rj) (Proxy @j) of
                        Just Refl ->
                          RCons @('From rj '(rl, rr)) v (go rest rs)
                        Nothing ->
                          error "unitor: root mismatch after 0⊗t"
                Nothing ->
                  error "unitor: expected left child 'I 0"
            SFrom {} ->
              error "unitor: expected left child 'I 0"
        SI {} ->
          error "unitor: expected From from FuseRep Unit"

-- | Fused Hom compose as the five Mac Lane morphisms.
composeHomTrees
  :: forall a b c
   . ( KnownFTrees (FuseRep a b)
     , KnownFTrees (FuseRep b c)
     , FuseRepTermC (FuseRep a b) (FuseRep b c)
     , KnownFTrees a
     , KnownFTrees b
     , KnownFTrees c
     , KnownFTrees (FuseRep b b)
     , KnownFTrees Unit
     , KnownFTrees (FuseRep b (FuseRep b c))
     , KnownFTrees (FuseRep (FuseRep b b) c)
     , KnownFTrees (FuseRep Unit c)
     , KnownFTrees (FuseRep a (FuseRep b (FuseRep b c)))
     , KnownFTrees (FuseRep a (FuseRep (FuseRep b b) c))
     , KnownFTrees (FuseRep a (FuseRep Unit c))
     , KnownFTrees (FuseRep a c)
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
                (fuseRepTerm @(FuseRep a b) @(FuseRep b c) f g)
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
   . ( KnownFTrees (FuseRep (ObjRep a) (ObjRep b))
     , KnownFTrees (FuseRep (ObjRep b) (ObjRep c))
     , FuseRepTermC (FuseRep (ObjRep a) (ObjRep b)) (FuseRep (ObjRep b) (ObjRep c))
     , KnownFTrees (ObjRep a)
     , KnownFTrees (ObjRep b)
     , KnownFTrees (ObjRep c)
     , KnownFTrees (FuseRep (ObjRep b) (ObjRep b))
     , KnownFTrees Unit
     , KnownFTrees (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c)))
     , KnownFTrees (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c))
     , KnownFTrees (FuseRep Unit (ObjRep c))
     , KnownFTrees (FuseRep (ObjRep a) (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c))))
     , KnownFTrees (FuseRep (ObjRep a) (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c)))
     , KnownFTrees (FuseRep (ObjRep a) (FuseRep Unit (ObjRep c)))
     , KnownFTrees (FuseRep (ObjRep a) (ObjRep c))
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
  type Object HomFused a =
    ( KnownFTrees (ObjRep a)
    , FuseRepIdC (ObjRep a) (ObjRep a)
    )

  id :: forall a. Object HomFused a => HomFused a a
  id = HomFused (idHomFTrees @(ObjRep a))

  -- @(.)@ needs the five Mac Lane steps on @a,b,c@, which 'Object' alone does
  -- not imply (constraints are triple-indexed). Named ladder: 'composeHomFused'.
  (.) = undefined

--------------------------------------------------------------------------------
-- HomInter: trivial sector of fused Hom (same Mac Lane compose)
--------------------------------------------------------------------------------

-- | Identity intertwiner: trivial channels of @'idHomFTrees' (ObjRep a)@.
idHomInterVal
  :: forall a
   . ( KnownFTrees (ObjRep a)
     , FuseRepIdC (ObjRep a) (ObjRep a)
     , KnownFTrees (FuseRep (ObjRep a) (ObjRep a))
     , FilterTrivialC (FuseRep (ObjRep a) (ObjRep a))
     )
  => RepV (FilterTrivial (FuseRep (ObjRep a) (ObjRep a)))
idHomInterVal =
  filterTrivialRepV @(FuseRep (ObjRep a) (ObjRep a)) (idHomFTrees @(ObjRep a))

-- | 'HomInter' compose: embed → 'composeHomTrees' → filter (same as 'HomFused').
composeHomInter
  :: forall a b c
   . ( KnownFTrees (FuseRep (ObjRep a) (ObjRep b))
     , KnownFTrees (FuseRep (ObjRep b) (ObjRep c))
     , KnownFTrees (FuseRep (ObjRep a) (ObjRep c))
     , FilterTrivialC (FuseRep (ObjRep a) (ObjRep b))
     , FilterTrivialC (FuseRep (ObjRep b) (ObjRep c))
     , FilterTrivialC (FuseRep (ObjRep a) (ObjRep c))
     , FuseRepTermC
         (FuseRep (ObjRep a) (ObjRep b))
         (FuseRep (ObjRep b) (ObjRep c))
     , KnownFTrees (ObjRep a)
     , KnownFTrees (ObjRep b)
     , KnownFTrees (ObjRep c)
     , KnownFTrees (FuseRep (ObjRep b) (ObjRep b))
     , KnownFTrees Unit
     , KnownFTrees (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c)))
     , KnownFTrees (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c))
     , KnownFTrees (FuseRep Unit (ObjRep c))
     , KnownFTrees
         ( FuseRep
             (ObjRep a)
             (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c)))
         )
     , KnownFTrees
         ( FuseRep
             (ObjRep a)
             (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c))
         )
     , KnownFTrees (FuseRep (ObjRep a) (FuseRep Unit (ObjRep c)))
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
    ( KnownFTrees (ObjRep a)
    , FuseRepIdC (ObjRep a) (ObjRep a)
    , KnownFTrees (FuseRep (ObjRep a) (ObjRep a))
    , FilterTrivialC (FuseRep (ObjRep a) (ObjRep a))
    )

  id :: forall a. Object HomInter a => HomInter a a
  id = HomInter (idHomInterVal @a)

  -- Same as 'HomFused': use 'composeHomInter' (needs Mac Lane constraints).
  (.) = undefined

