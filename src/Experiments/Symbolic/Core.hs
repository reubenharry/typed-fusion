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

-- | Term-level symbolic SU(2): singletons, 'RepV', cups, Hom.
--
-- Type kinds and families live in 'Experiments.Symbolic.Expr' /
-- 'Experiments.Symbolic.TypeLevel'. Examples: 'Experiments.SymbolicExamples'.
--
-- Layers: 'Obj' → 'HomUnfused' (Kronecker); genealogy 'Rep'/'RepV' →
-- 'HomFused' via 'fuseTrees' / 'composeHomTrees' (five Mac Lane steps).
-- Cups: 'cupFused' / 'capFused' on singlet trees.
module Experiments.Symbolic.Core where

import Data.Complex (Complex ((:+)), conjugate, magnitude, realPart)
import Data.Coerce (coerce)
import Data.Kind (Constraint)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.VectorSpace (AdditiveGroup (zeroV, (^-^)), InnerSpace ((<.>)), Scalar, VectorSpace ((*^)))
import qualified Data.Vector.Storable as VS
import GHC.TypeLits (KnownNat, Nat, natVal, sameNat, type (+))
import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..))
import Experiments.Categorical.Associative (Associative (..))
import Experiments.Categorical.Bifunctor (Bifunctor (..), PFunctor (..), QFunctor (..))
import Experiments.Categorical.Braided (Braided (..))
import Experiments.Categorical.Monoidal (Monoidal (..))
import Experiments.Fusion.Obj (Obj)
import qualified Experiments.Fusion.Obj as FObj
import Experiments.Fusion.SU2
  ( allowedE
  , allowedF
  , fmoveAtomsFlat
  , leftSectors
  , packAtomsFlat
  , rightSectors
  , unpackAtomsFlat
  )
import Experiments.SU2 (TensorIrrepRepSU2)
import Experiments.Symbolic.Expr
import Experiments.Symbolic.TypeLevel
import Math.LinearMap.Asserted (getLinearFunction)
import Math.LinearMap.Category
  ( DualVector
  , HilbertSpace
  , TensorSpace
  , (-+$>)
  , fromLinearForm
  , idTensor
  , pattern LinearFunction
  , trace
  , type (+>)
  , type (⊗)
  , (⊗)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Class (LinearSpace, asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, konst)
import Symmetry.Utils (Append)
import Symmetry.CG.SU2
  ( fuseCGChannel
  , fuseMapLeftFlatSectors
  , fuseMapRightFlatSectors
  )
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

-- | Singleton for an irrep label (@2j@ as 'Nat').
data SIrrep (j :: Nat) where
  SAtomI
    :: forall j
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SIrrep j

--------------------------------------------------------------------------------
-- Fusion-tree singletons ('Irrep' / 'Rep')
--------------------------------------------------------------------------------

-- | Singleton for a genealogy-preserving 'Irrep' tree.
data SIrrepTree (t :: Irrep) where
  SLeaf
    :: forall j
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SIrrepTree ('Leaf j)
  SNode
    :: forall j l r
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SIrrepTree l
    -> SIrrepTree r
    -> SIrrepTree ('Node j l r)

-- | Materialize 'SIrrepTree' for a statically known tree.
class KnownIrrep (t :: Irrep) where
  irrepSing :: SIrrepTree t

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  KnownIrrep ('Leaf j)
  where
  irrepSing = SLeaf @j

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  , KnownIrrep l
  , KnownIrrep r
  ) =>
  KnownIrrep ('Node j l r)
  where
  irrepSing = SNode @j (irrepSing @l) (irrepSing @r)

-- | Singleton spine for 'Rep'.
data SRep (ts :: Rep) where
  SRepNil :: SRep '[]
  SRepCons
    :: forall t rest
     . SIrrepTree t
    -> SRep rest
    -> SRep (t ': rest)

-- | Materialize 'SRep' for a statically known tree list.
class KnownRep (ts :: Rep) where
  repSing :: SRep ts

instance KnownRep '[] where
  repSing = SRepNil

instance
  ( KnownIrrep t
  , KnownRep rest
  ) =>
  KnownRep (t ': rest)
  where
  repSing = SRepCons (irrepSing @t) (repSing @rest)

--------------------------------------------------------------------------------
-- Term-level fusion trees ('RepV')
--------------------------------------------------------------------------------

-- | Spine of root vectors, indexed by type-level 'Rep'.
data RepV (ts :: Rep) where
  RNil :: RepV '[]
  RCons
    :: forall t rest
     . ToVTree t
    -> RepV rest
    -> RepV (t ': rest)

-- | Forgetful map: nonempty 'RepV' → 'ToVRep'.
repVToV :: forall ts. KnownRep ts => RepV ts -> ToVRep ts
repVToV = go (repSing @ts)
  where
    go :: forall ts'. SRep ts' -> RepV ts' -> ToVRep ts'
    go (SRepCons _ SRepNil) (RCons v RNil) = v
    go (SRepCons _ sRest@(SRepCons {})) (RCons v rest) =
      (v, go sRest rest)
    go _ _ = error "repVToV: expected nonempty KnownRep"

-- | Inverse of 'repVToV'.
vToRepV :: forall ts. KnownRep ts => ToVRep ts -> RepV ts
vToRepV = go (repSing @ts)
  where
    go :: forall ts'. SRep ts' -> ToVRep ts' -> RepV ts'
    go (SRepCons (_ :: SIrrepTree t) SRepNil) v =
      RCons @t v RNil
    go (SRepCons (_ :: SIrrepTree t) sRest@(SRepCons {})) (v, rest) =
      RCons @t v (go sRest rest)
    go _ _ = error "vToRepV: expected nonempty KnownRep"

-- | Append two tree spines.
appendRepV
  :: RepV ts1
  -> RepV ts2
  -> RepV (Append ts1 ts2)
appendRepV RNil r2 = r2
appendRepV (RCons v rest) r2 =
  RCons v (appendRepV rest r2)

-- | Walk CG channels for a pair of trees → 'RepV' of @'Node@ outcomes.
class FuseTreesGo (t1 :: Irrep) (t2 :: Irrep) (cg :: [(Nat, Nat)]) where
  fuseTreesGo
    :: C (IrrepDim (Root t1)) ⊗ C (IrrepDim (Root t2))
    -> RepV (NodesFromCG t1 t2 cg)

instance FuseTreesGo t1 t2 '[] where
  fuseTreesGo _ = RNil

instance
  ( FuseTreesGo t1 t2 rest
  , KnownNat j
  , KnownNat (Root t1)
  , KnownNat (Root t2)
  , KnownNat (IrrepDim (Root t1))
  , KnownNat (IrrepDim (Root t2))
  , KnownNat (IrrepDim j)
  ) =>
  FuseTreesGo t1 t2 ('(j, m) ': rest)
  where
  fuseTreesGo v =
    RCons @('Node j t1 t2)
      (fuseCGChannel @(Root t1) @(Root t2) @j $ v)
      (fuseTreesGo @t1 @t2 @rest v)

-- | CG-fuse two fusion trees into the channel list 'FuseTrees'.
fuseTrees
  :: forall t1 t2
   . ( KnownIrrep t1
     , KnownIrrep t2
     , FuseTreesGo t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))
     )
  => ToVTree t1 ⊗ ToVTree t2
  -> RepV (FuseTrees t1 t2)
fuseTrees =
  fuseTreesGo @t1 @t2 @(TensorIrrepRepSU2 (Root t1) (Root t2))

-- | Constraints for walking 'FuseRep' at the term level.
type family FuseRepTermC (rs :: Rep) (qs :: Rep) :: Constraint where
  FuseRepTermC '[] _ = ()
  FuseRepTermC (t1 ': rest) qs =
    ( FuseRepOneTermC t1 qs
    , FuseRepTermC rest qs
    )

type family FuseRepOneTermC (t1 :: Irrep) (qs :: Rep) :: Constraint where
  FuseRepOneTermC _ '[] = ()
  FuseRepOneTermC t1 (t2 ': rest) =
    ( KnownIrrep t1
    , KnownIrrep t2
    , KnownNat (Root t1)
    , KnownNat (Root t2)
    , KnownNat (IrrepDim (Root t1))
    , KnownNat (IrrepDim (Root t2))
    , TensorSpace (C (IrrepDim (Root t1)))
    , TensorSpace (C (IrrepDim (Root t2)))
    , Scalar (C (IrrepDim (Root t1))) ~ Complex Double
    , Scalar (C (IrrepDim (Root t2))) ~ Complex Double
    , FuseTreesGo t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))
    , FuseRepOneTermC t1 rest
    )

fuseRepOneTerm
  :: forall t1 qs
   . FuseRepOneTermC t1 qs
  => ToVTree t1
  -> SRep qs
  -> RepV qs
  -> RepV (FuseRepOne t1 qs)
fuseRepOneTerm _ SRepNil RNil = RNil
fuseRepOneTerm v1 (SRepCons (_ :: SIrrepTree t2) qRest) (RCons v2 rest) =
  appendRepV
    (fuseTrees @t1 @t2 (v1 ⊗ v2))
    (fuseRepOneTerm @t1 v1 qRest rest)

-- | Cartesian fuse of two 'RepV' spines (matches 'FuseRep').
fuseRepTerm
  :: forall rs qs
   . ( KnownRep rs
     , KnownRep qs
     , FuseRepTermC rs qs
     )
  => RepV rs
  -> RepV qs
  -> RepV (FuseRep rs qs)
fuseRepTerm rs qs =
  fuseRepTermGo (repSing @rs) rs (repSing @qs) qs

fuseRepTermGo
  :: forall rs qs
   . FuseRepTermC rs qs
  => SRep rs
  -> RepV rs
  -> SRep qs
  -> RepV qs
  -> RepV (FuseRep rs qs)
fuseRepTermGo SRepNil RNil _ _ = RNil
fuseRepTermGo
  (SRepCons (_ :: SIrrepTree t1) rRest)
  (RCons v1 rRestV)
  qSing
  q =
  appendRepV
    (fuseRepOneTerm @t1 v1 qSing q)
    (fuseRepTermGo rRest rRestV qSing q)

--------------------------------------------------------------------------------
-- Unit scalar packaging + atom dual / fused cups on singlet trees
--------------------------------------------------------------------------------

-- | Unit amplitude as @ToVObj ('Atom 0)@ packing (@C 1 ⊗ C 1@).
unitToVFromScalar :: Complex Double -> C 1 ⊗ C 1
unitToVFromScalar s = unsafeFromArray (VS.fromList [s])

-- | Read the amplitude from @C 1 ⊗ C 1@.
unitToVScalar :: (C 1 ⊗ C 1) -> Complex Double
unitToVScalar u = VS.head (toArray u)

-- | Condon–Shortley dual on one irrep buffer: @|k⟩ ↦ (-1)^k |tj−k⟩@
-- (@tm = tj − 2k@, highest weight first; @(-1)^{j−m} = (-1)^k@).
csIrrepLinear
  :: forall j
   . ( KnownNat j
     , KnownNat (IrrepDim j)
     )
  => C (IrrepDim j)
  -> C (IrrepDim j)
csIrrepLinear v =
  let tj = fromIntegral (natVal (Proxy @j)) :: Int
      d = tj + 1
      vin = toArray v
   in unsafeFromArray $
        VS.generate d $ \kRev ->
          let k = tj - kRev
              phase = if even k then 1 else -1
           in (phase :+ 0) * (vin VS.! k)

csIrrepMap
  :: forall j
   . ( KnownNat j
     , KnownNat (IrrepDim j)
     )
  => C (IrrepDim j) +> C (IrrepDim j)
csIrrepMap = arr (LinearFunction (csIrrepLinear @j))

-- | Dual of an atom payload (@C m ⊗ C (j+1)@).
dualAtomAtomM
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , InnerSpace (C m ⊗ C (IrrepDim j))
     , Scalar (C m ⊗ C (IrrepDim j)) ~ Complex Double
     )
  => (C m ⊗ C (IrrepDim j))
  -> DualVector (C m ⊗ C (IrrepDim j))
dualAtomAtomM v =
  fromLinearForm $
    arr (LinearFunction (\w -> w <.> ((id ⊗^ csIrrepMap @j) $ v)))

-- | Inverse of 'dualAtomAtomM', then CS + @√(j+1)@ for cup coherence.
undualAtomAtomM
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , HilbertSpace (C m)
     , HilbertSpace (C (IrrepDim j))
     )
  => DualVector (C m ⊗ C (IrrepDim j))
  -> (C m ⊗ C (IrrepDim j))
undualAtomAtomM φ =
  let tDual =
        asTensor -+$=> φ
          :: DualVector (C m) ⊗ DualVector (C (IrrepDim j))
      riesz =
        ( arr (LinearFunction (coerce :: DualVector (C m) -> C m))
            ⊗^ arr (LinearFunction (coerce :: DualVector (C (IrrepDim j)) -> C (IrrepDim j)))
        )
          $ tDual
      dim = fromIntegral (natVal (Proxy @(IrrepDim j))) :: Double
      scale = sqrt dim :+ 0
   in scale *^ ((id ⊗^ csIrrepMap @j) $ riesz)

-- | Contract a singlet-root tree spine to a scalar.
class CupTrivial (ts :: Rep) where
  cupTrivial :: RepV ts -> Complex Double

instance CupTrivial '[] where
  cupTrivial RNil = 0

instance
  ( CupTrivial rest
  , LinearSpace (C 1)
  , Scalar (C 1) ~ Complex Double
  , InnerSpace (C 1)
  ) =>
  CupTrivial ('Leaf 0 ': rest)
  where
  cupTrivial (RCons v rest) =
    (konst 1 <.> v) + cupTrivial rest

instance
  ( CupTrivial rest
  , LinearSpace (C 1)
  , Scalar (C 1) ~ Complex Double
  , InnerSpace (C 1)
  ) =>
  CupTrivial ('Node 0 l r ': rest)
  where
  cupTrivial (RCons v rest) =
    (konst 1 <.> v) + cupTrivial rest

-- | Drop non-singlet-root trees (term-level 'FilterTrivial').
class FilterTrivialTerm (ts :: Rep) where
  filterTrivialTerm :: RepV ts -> RepV (FilterTrivial ts)

instance FilterTrivialTerm '[] where
  filterTrivialTerm RNil = RNil

instance {-# OVERLAPPING #-}
  ( FilterTrivialTerm rest
  , LinearSpace (C 1)
  , Scalar (C 1) ~ Complex Double
  ) =>
  FilterTrivialTerm ('Leaf 0 ': rest)
  where
  filterTrivialTerm (RCons v rest) =
    RCons @('Leaf 0) v (filterTrivialTerm rest)

instance {-# OVERLAPPING #-}
  ( FilterTrivialTerm rest
  , LinearSpace (C 1)
  , Scalar (C 1) ~ Complex Double
  ) =>
  FilterTrivialTerm ('Node 0 l r ': rest)
  where
  filterTrivialTerm (RCons v rest) =
    RCons @('Node 0 l r) v (filterTrivialTerm rest)

instance {-# OVERLAPPABLE #-}
  ( FilterTrivialTerm rest
  , FilterTrivial (t ': rest) ~ FilterTrivial rest
  ) =>
  FilterTrivialTerm (t ': rest)
  where
  filterTrivialTerm (RCons _ rest) = filterTrivialTerm rest

-- | Fused evaluation on singlet trees of @FuseRep a a@.
cupFused
  :: forall a
   . ( FilterTrivialTerm (FuseRep a a)
     , CupTrivial (FilterTrivial (FuseRep a a))
     )
  => RepV (FuseRep a a)
  -> Complex Double
cupFused = cupTrivial . filterTrivialTerm @(FuseRep a a)

-- | Fused coevaluation: scale the identity singlet(s) of @a@.
capFused
  :: forall a
   . ( KnownHomFused a
     , FilterTrivialTerm (FuseRep a a)
     , KnownRep (FilterTrivial (FuseRep a a))
     , LinearSpace (ToVRep (FilterTrivial (FuseRep a a)))
     , Scalar (ToVRep (FilterTrivial (FuseRep a a))) ~ Complex Double
     )
  => Complex Double
  -> RepV (FilterTrivial (FuseRep a a))
capFused s =
  scaleRepV
    @(FilterTrivial (FuseRep a a))
    s
    (filterTrivialTerm @(FuseRep a a) (idHomFusedVal @a))

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

-- | Fused morphisms @a → b@: genealogy-preserving 'RepV' of 'FuseRep'
-- (SU(2) dual≅primal; left child plays dual). Compose via 'composeHomTrees'.
newtype HomFused (a :: Rep) (b :: Rep) = HomFused
  { unHomFused :: RepV (FuseRep a b) }

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

-- | Object constraint for fused Hom: leaf spines with a known identity.
class KnownHomFused (a :: Rep) where
  idHomFusedVal :: RepV (FuseRep a a)

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

-- | Any single leaf: identity via 'idHomLeaf'.
instance
  ( KnownNat j
  , KnownRep (FuseRep '[ 'Leaf j] '[ 'Leaf j])
  ) =>
  KnownHomFused '[ 'Leaf j]
  where
  idHomFusedVal = idHomLeaf @j

-- Category \/ monoidal structure: HomUnfused (complete). HomFused Category lives
-- with the tree compose ladder (see 'composeHomFused').

--------------------------------------------------------------------------------
-- Fused associator primitives (3-leaf) and FuseRep-in-one-leg naturality
--
-- Unfused Mac Lane on four factors factors as:
--
-- @
-- (a⊗b) ⊗ (b⊗c)  ─rassoc→  a ⊗ (b ⊗ (b⊗c))  ─id⊗lassoc→  a ⊗ ((b⊗b) ⊗ c)
-- @
--
-- Fused (genealogy on trees; see 'composeHomTrees'):
--
-- @
-- fmoveOuterHom ; fmoveInnerHom =
--   fuseMapRight (fmoveInvTrees @b @b @c) ∘ fmoveOuterHom @a @b @c
-- @
--
-- Outer F is 'CanFmoveOuterHom' (leaf → 'fmoveOuterHomLeaves'); inner triple
-- leaf F is 'CanFmoveTrees'.
-- 'fuseMapRight' is naturality of @Fuse(a, –)@ on /intertwiners/ (e.g. F-moves),
-- not a general @fuseBimap f g@ (that would need Split∘(f⊗g)∘Fuse†).
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Tree-indexed F-move / bimap / Hom-compose (genealogy-preserving)
--
-- Fused Hom composition (the real fused path):
--   tensorHom → fmoveOuterHom → fmoveInnerHom → cupTensorIdHom → unitorHom
--
-- Domain\/codomain of F are @FuseRep (FuseRep a b) c@ \/ @FuseRep a (FuseRep b c)@.
-- Same-root trees stay
-- distinct list entries, so cup can project on trivial-root middle subtrees.
--------------------------------------------------------------------------------

-- | Concrete @½⊗½⊗½@ association trees (matches compile-time AssocL/R smokes).
--
-- Channel order within each total @d@ is the F-block multiplicity basis
-- (@e@ left \/ @f@ right): for @d=1@ channels @[0,2]@; for @d=3@ channel @[2]@.
type AssocL111 =
  '[ 'Node 1 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Leaf 1)
   , 'Node 1 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 1)
   , 'Node 3 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 1)
   ]

type AssocR111 =
  '[ 'Node 1 ('Leaf 1) ('Node 0 ('Leaf 1) ('Leaf 1))
   , 'Node 1 ('Leaf 1) ('Node 2 ('Leaf 1) ('Leaf 1))
   , 'Node 3 ('Leaf 1) ('Node 2 ('Leaf 1) ('Leaf 1))
   ]

-- | Trivial @0⊗0⊗0@ assoc spines (single F-block, @F = id@).
type AssocL000 =
  '[ 'Node 0 ('Node 0 ('Leaf 0) ('Leaf 0)) ('Leaf 0)]

type AssocR000 =
  '[ 'Node 0 ('Leaf 0) ('Node 0 ('Leaf 0) ('Leaf 0))]

-- | @½⊗½⊗0@: totals @d∈{0,2}@, singleton multiplicity each.
type AssocL110 =
  '[ 'Node 0 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Leaf 0)
   , 'Node 2 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 0)
   ]

type AssocR110 =
  '[ 'Node 0 ('Leaf 1) ('Node 1 ('Leaf 1) ('Leaf 0))
   , 'Node 2 ('Leaf 1) ('Node 1 ('Leaf 1) ('Leaf 0))
   ]

-- | @½⊗½⊗1@: totals @d∈{0,2,4}@; @d=2@ has mult @[0,2]@ (left) \/ @[1,3]@ (right).
-- Tree order follows left-assoc @FuseRep (FuseRep …) …@ (not sorted by @d@):
-- @d=2,e=0@ then @d=0@ then @d=2,e=2@ then @d=4@.
type AssocL112 =
  '[ 'Node 2 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Leaf 2)
   , 'Node 0 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 2)
   , 'Node 2 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 2)
   , 'Node 4 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 2)
   ]

type AssocR112 =
  '[ 'Node 0 ('Leaf 1) ('Node 1 ('Leaf 1) ('Leaf 2))
   , 'Node 2 ('Leaf 1) ('Node 1 ('Leaf 1) ('Leaf 2))
   , 'Node 2 ('Leaf 1) ('Node 3 ('Leaf 1) ('Leaf 2))
   , 'Node 4 ('Leaf 1) ('Node 3 ('Leaf 1) ('Leaf 2))
   ]

-- | 3-factor F-move on fusion-tree spines: @(x⊗y)⊗z → x⊗(y⊗z)@.
--
-- Leaf triples: polymorphic instance via 'fmoveTreesLeaves' → 'fmoveTreesAtoms'
-- (@FuseRep (FuseRep a b) c → FuseRep a (FuseRep b c)@). Outer Hom F
-- (@z = FuseRep b c@) cannot put that type family in an instance head — use
-- 'CanFmoveOuterHom' instead.
class CanFmoveTrees (a :: Rep) (b :: Rep) (c :: Rep) where
  fmoveTrees
    :: RepV (FuseRep (FuseRep a b) c)
    -> RepV (FuseRep a (FuseRep b c))
  fmoveInvTrees
    :: RepV (FuseRep a (FuseRep b c))
    -> RepV (FuseRep (FuseRep a b) c)

-- | Outer Hom F for leaf objects: @(a⊗b) ⊗ Hom(b,c) → a ⊗ (b ⊗ Hom(b,c))@.
-- Instance head is three leaf spines (no 'FuseRep' in the head).
class CanFmoveOuterHom (a :: Rep) (b :: Rep) (c :: Rep) where
  fmoveOuterHom
    :: RepV (FuseRep (FuseRep a b) (FuseRep b c))
    -> RepV (FuseRep a (FuseRep b (FuseRep b c)))
  fmoveInvOuterHom
    :: RepV (FuseRep a (FuseRep b (FuseRep b c)))
    -> RepV (FuseRep (FuseRep a b) (FuseRep b c))

--------------------------------------------------------------------------------
-- Label-driven atom F-move (general; no per-triple FlatXXX)
--------------------------------------------------------------------------------

rootLab :: SIrrepTree t -> Int
rootLab (SLeaf @j) = fromIntegral (natVal (Proxy @j))
rootLab (SNode @j _ _) = fromIntegral (natVal (Proxy @j))

-- | Collect left-assoc channels from @((a_i⊗b_j)_e ⊗ c_k)_d@.
--
-- Keys include roots of the embedded factors so multi-tree spines
-- (e.g. Hom⊗leaf⊗leaf) do not collide on @(d,e)@ alone.
collectAssocLChannel
  :: SRep ts
  -> RepV ts
  -> [(Int, Int, Int, Int, Int, VS.Vector (Complex Double))]
collectAssocLChannel SRepNil RNil = []
collectAssocLChannel (SRepCons t rest) (RCons v rs) =
  case t of
    SNode @d left right ->
      case left of
        SNode @_ a_i b_j ->
          ( fromIntegral (natVal (Proxy @d))
          , rootLab left
          , rootLab a_i
          , rootLab b_j
          , rootLab right
          , toArray v
          )
            : collectAssocLChannel rest rs
        SLeaf {} ->
          error "collectAssocLChannel: expected Node intermediate (not left-assoc FuseRep?)"
        SLeaf {} ->
          error "collectAssocLChannel: leaf in association spine (not left-assoc FuseRep?)"

-- | Collect right-assoc channels from @(a_i ⊗ (b_j⊗c_k)_f)_d@.
collectAssocRChannel
  :: SRep ts
  -> RepV ts
  -> [(Int, Int, Int, Int, Int, VS.Vector (Complex Double))]
collectAssocRChannel SRepNil RNil = []
collectAssocRChannel (SRepCons t rest) (RCons v rs) =
  case t of
    SNode @d left right ->
      case right of
        SNode @_ b_j c_k ->
          ( fromIntegral (natVal (Proxy @d))
          , rootLab right
          , rootLab left
          , rootLab b_j
          , rootLab c_k
          , toArray v
          )
            : collectAssocRChannel rest rs
        SLeaf {} ->
          error "collectAssocRChannel: expected Node intermediate (not right-assoc FuseRep?)"
        SLeaf {} ->
          error "collectAssocRChannel: leaf in association spine (not right-assoc FuseRep?)"

-- | @(d, mid, ra, rb, rc)@ channel map → AssocL spine.
scatterAssocLChannel
  :: SRep ts
  -> Map.Map (Int, Int, Int, Int, Int) (VS.Vector (Complex Double))
  -> RepV ts
scatterAssocLChannel SRepNil _ = RNil
scatterAssocLChannel (SRepCons (t :: SIrrepTree u) rest) m =
  case t of
    SNode @d left right ->
      case left of
        SNode @_ a_i b_j ->
          let key =
                ( fromIntegral (natVal (Proxy @d))
                , rootLab left
                , rootLab a_i
                , rootLab b_j
                , rootLab right
                )
           in RCons @u
                (unsafeFromArray (Map.findWithDefault (zeroLike5 key m) key m))
                (scatterAssocLChannel rest m)
        SLeaf {} ->
          error "scatterAssocLChannel: expected Node intermediate"
    SLeaf {} ->
      error "scatterAssocLChannel: leaf in association spine"

scatterAssocRChannel
  :: SRep ts
  -> Map.Map (Int, Int, Int, Int, Int) (VS.Vector (Complex Double))
  -> RepV ts
scatterAssocRChannel SRepNil _ = RNil
scatterAssocRChannel (SRepCons (t :: SIrrepTree u) rest) m =
  case t of
    SNode @d left right ->
      case right of
        SNode @_ b_j c_k ->
          let key =
                ( fromIntegral (natVal (Proxy @d))
                , rootLab right
                , rootLab left
                , rootLab b_j
                , rootLab c_k
                )
           in RCons @u
                (unsafeFromArray (Map.findWithDefault (zeroLike5 key m) key m))
                (scatterAssocRChannel rest m)
        SLeaf {} ->
          error "scatterAssocRChannel: expected Node intermediate"
    SLeaf {} ->
      error "scatterAssocRChannel: leaf in association spine"

-- | Zero vector for a missing 5-key channel (same @d@-block length as peers).
zeroLike5
  :: (Int, Int, Int, Int, Int)
  -> Map.Map (Int, Int, Int, Int, Int) (VS.Vector (Complex Double))
  -> VS.Vector (Complex Double)
zeroLike5 (d, _, _, _, _) m =
  case [v | ((d', _, _, _, _), v) <- Map.toList m, d' == d] of
    (v : _) -> VS.replicate (VS.length v) 0
    [] -> VS.replicate (d + 1) 0

-- | 3-factor F-move: @FuseRep (FuseRep a b) c → FuseRep a (FuseRep b c)@.
--
-- 'FuseRep' distributes into channels @((a_i⊗b_j)_e ⊗ c_k)_d@. For each
-- distinct root triple @(r(a_i),r(b_j),r(c_k))@ apply dense Racah
-- @F^{ra rb rc}@, keeping genealogy in the channel key.
fmoveTreesAtoms
  :: forall a b c
   . ( KnownRep (FuseRep (FuseRep a b) c)
     , KnownRep (FuseRep a (FuseRep b c))
     )
  => RepV (FuseRep (FuseRep a b) c)
  -> RepV (FuseRep a (FuseRep b c))
fmoveTreesAtoms tv =
  let chans = collectAssocLChannel (repSing @(FuseRep (FuseRep a b) c)) tv
      triples =
        Map.keys $
          Map.fromList [((ra, rb, rc), ()) | (_, _, ra, rb, rc, _) <- chans]
      out =
        concatMap
          ( \(ra, rb, rc) ->
              let chH =
                    [ (d, e, v)
                    | (d, e, ra', rb', rc', v) <- chans
                    , ra' == ra
                    , rb' == rb
                    , rc' == rc
                    ]
                  buf =
                    packAtomsFlat
                      (leftSectors ra rb rc)
                      (\d -> allowedE ra rb rc d)
                      chH
                  buf' = fmoveAtomsFlat False ra rb rc buf
                  unpacked =
                    unpackAtomsFlat
                      (rightSectors ra rb rc)
                      (\d -> allowedF ra rb rc d)
                      buf'
               in [(d, f, ra, rb, rc, v) | (d, f, v) <- unpacked]
          )
          triples
   in scatterAssocRChannel
        (repSing @(FuseRep a (FuseRep b c)))
        (Map.fromList [((d, f, ra, rb, rc), v) | (d, f, ra, rb, rc, v) <- out])

fmoveInvTreesAtoms
  :: forall a b c
   . ( KnownRep (FuseRep (FuseRep a b) c)
     , KnownRep (FuseRep a (FuseRep b c))
     )
  => RepV (FuseRep a (FuseRep b c))
  -> RepV (FuseRep (FuseRep a b) c)
fmoveInvTreesAtoms tv =
  let chans = collectAssocRChannel (repSing @(FuseRep a (FuseRep b c))) tv
      triples =
        Map.keys $
          Map.fromList [((ra, rb, rc), ()) | (_, _, ra, rb, rc, _) <- chans]
      out =
        concatMap
          ( \(ra, rb, rc) ->
              let chH =
                    [ (d, f, v)
                    | (d, f, ra', rb', rc', v) <- chans
                    , ra' == ra
                    , rb' == rb
                    , rc' == rc
                    ]
                  buf =
                    packAtomsFlat
                      (rightSectors ra rb rc)
                      (\d -> allowedF ra rb rc d)
                      chH
                  buf' = fmoveAtomsFlat True ra rb rc buf
                  unpacked =
                    unpackAtomsFlat
                      (leftSectors ra rb rc)
                      (\d -> allowedE ra rb rc d)
                      buf'
               in [(d, e, ra, rb, rc, v) | (d, e, v) <- unpacked]
          )
          triples
   in scatterAssocLChannel
        (repSing @(FuseRep (FuseRep a b) c))
        (Map.fromList [((d, e, ra, rb, rc), v) | (d, e, ra, rb, rc, v) <- out])

-- | Atom-leaf triple F-move from type-level @2j@.
fmoveTreesLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
     , KnownRep ( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]) )
     )
  => RepV ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
  -> RepV ( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]) )
fmoveTreesLeaves =
  fmoveTreesAtoms @('[ 'Leaf ja]) @('[ 'Leaf jb]) @('[ 'Leaf jc])

fmoveInvTreesLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
     , KnownRep ( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]) )
     )
  => RepV ( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]) )
  -> RepV ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
fmoveInvTreesLeaves =
  fmoveInvTreesAtoms @('[ 'Leaf ja]) @('[ 'Leaf jb]) @('[ 'Leaf jc])

-- | Outer Hom F for three leaf labels (Hom = 'FuseRep' of the last two).
fmoveOuterHomLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep
         ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) (FuseRep '[ 'Leaf jb] '[ 'Leaf jc])
         )
     , KnownRep
         ( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]))
         )
     )
  => RepV
       ( FuseRep
           (FuseRep '[ 'Leaf ja] '[ 'Leaf jb])
           (FuseRep '[ 'Leaf jb] '[ 'Leaf jc])
       )
  -> RepV
       ( FuseRep
           '[ 'Leaf ja]
           (FuseRep '[ 'Leaf jb] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]))
       )
fmoveOuterHomLeaves =
  fmoveOuterLeafHom @ja @jb
    @( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) (FuseRep '[ 'Leaf jb] '[ 'Leaf jc])
     )
    @( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]))
     )

fmoveInvOuterHomLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep
         ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) (FuseRep '[ 'Leaf jb] '[ 'Leaf jc])
         )
     , KnownRep
         ( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]))
         )
     )
  => RepV
       ( FuseRep
           '[ 'Leaf ja]
           (FuseRep '[ 'Leaf jb] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]))
       )
  -> RepV
       ( FuseRep
           (FuseRep '[ 'Leaf ja] '[ 'Leaf jb])
           (FuseRep '[ 'Leaf jb] '[ 'Leaf jc])
       )
fmoveInvOuterHomLeaves =
  fmoveInvOuterLeafHom @ja @jb
    @( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]))
     )
    @( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) (FuseRep '[ 'Leaf jb] '[ 'Leaf jc])
     )

-- | Triple-leaf F-move via label-driven 'fmoveTreesLeaves'.
fmoveTrees111 :: RepV AssocL111 -> RepV AssocR111
fmoveTrees111 = fmoveTreesLeaves @1 @1 @1

fmoveInvTrees111 :: RepV AssocR111 -> RepV AssocL111
fmoveInvTrees111 = fmoveInvTreesLeaves @1 @1 @1

fmoveTrees000 :: RepV AssocL000 -> RepV AssocR000
fmoveTrees000 = fmoveTreesLeaves @0 @0 @0

fmoveInvTrees000 :: RepV AssocR000 -> RepV AssocL000
fmoveInvTrees000 = fmoveInvTreesLeaves @0 @0 @0

fmoveTrees110 :: RepV AssocL110 -> RepV AssocR110
fmoveTrees110 = fmoveTreesLeaves @1 @1 @0

fmoveInvTrees110 :: RepV AssocR110 -> RepV AssocL110
fmoveInvTrees110 = fmoveInvTreesLeaves @1 @1 @0

fmoveTrees112 :: RepV AssocL112 -> RepV AssocR112
fmoveTrees112 = fmoveTreesLeaves @1 @1 @2

fmoveInvTrees112 :: RepV AssocR112 -> RepV AssocL112
fmoveInvTrees112 = fmoveInvTreesLeaves @1 @1 @2

-- | Any three atom leaves: F via 'fmoveTreesLeaves' (no per-triple FlatXXX).
instance
  ( KnownNat ja
  , KnownNat jb
  , KnownNat jc
  , KnownRep ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
  , KnownRep ( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]) )
  ) =>
  CanFmoveTrees '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc]
  where
  fmoveTrees = fmoveTreesLeaves @ja @jb @jc
  fmoveInvTrees = fmoveInvTreesLeaves @ja @jb @jc

-- | Nested unfused @a ⊗ q@ before CG (layout for Fuse-right naturality).
data TensorTrees (a :: Rep) (q :: Rep) where
  TensorTrees :: RepV a -> RepV q -> TensorTrees a q

mapTensorTreesRight
  :: (RepV q -> RepV q')
  -> TensorTrees a q
  -> TensorTrees a q'
mapTensorTreesRight f (TensorTrees a q) = TensorTrees a (f q)

fuseTensorTrees
  :: forall a q
   . ( KnownRep a
     , KnownRep q
     , FuseRepTermC a q
     )
  => TensorTrees a q
  -> RepV (FuseRep a q)
fuseTensorTrees (TensorTrees a q) = fuseRepTerm @a @q a q

--------------------------------------------------------------------------------
-- Leaf object / Hom aliases (thin names over 'FuseRep')
--------------------------------------------------------------------------------

type Leaf1 = '[ 'Leaf 1]

type Leaf0 = '[ 'Leaf 0]

type Leaf2 = '[ 'Leaf 2]

type Leaf3 = '[ 'Leaf 3]

-- | Endomorphism Hom on a leaf: @FuseRep a a@.
type Hom00 = FuseRep Leaf0 Leaf0

type Hom11 = FuseRep Leaf1 Leaf1

type Hom22 = FuseRep Leaf2 Leaf2

type Hom33 = FuseRep Leaf3 Leaf3

-- | Unequal-leaf Homs (for @½ → 1 → ½@ compose smoke).
type Hom12 = FuseRep Leaf1 Leaf2

type Hom21 = FuseRep Leaf2 Leaf1

-- | Leaf outer Hom F: any three leaf labels (Hom = 'FuseRep' of last two).
instance
  ( KnownNat ja
  , KnownNat jb
  , KnownNat jc
  , KnownRep
      ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) (FuseRep '[ 'Leaf jb] '[ 'Leaf jc])
      )
  , KnownRep
      ( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]))
      )
  ) =>
  CanFmoveOuterHom '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc]
  where
  fmoveOuterHom = fmoveOuterHomLeaves @ja @jb @jc
  fmoveInvOuterHom = fmoveInvOuterHomLeaves @ja @jb @jc

-- | Hom-left nested F: left factor @FuseRep '[Leaf ja] '[Leaf ja]@.
-- Plain functions (Nat-indexed so 'FuseRep' stays out of instance heads).
fmoveTreesHomLeft
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep
         ( FuseRep (FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf ja]) '[ 'Leaf jb]) '[ 'Leaf jc]
         )
     , KnownRep
         ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf ja]) (FuseRep '[ 'Leaf jb] '[ 'Leaf jc])
         )
     )
  => RepV
       ( FuseRep (FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf ja]) '[ 'Leaf jb]) '[ 'Leaf jc]
       )
  -> RepV
       ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf ja]) (FuseRep '[ 'Leaf jb] '[ 'Leaf jc])
       )
fmoveTreesHomLeft =
  fmoveTreesAtoms
    @(FuseRep '[ 'Leaf ja] '[ 'Leaf ja])
    @('[ 'Leaf jb])
    @('[ 'Leaf jc])

fmoveInvTreesHomLeft
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep
         ( FuseRep (FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf ja]) '[ 'Leaf jb]) '[ 'Leaf jc]
         )
     , KnownRep
         ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf ja]) (FuseRep '[ 'Leaf jb] '[ 'Leaf jc])
         )
     )
  => RepV
       ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf ja]) (FuseRep '[ 'Leaf jb] '[ 'Leaf jc])
       )
  -> RepV
       ( FuseRep (FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf ja]) '[ 'Leaf jb]) '[ 'Leaf jc]
       )
fmoveInvTreesHomLeft =
  fmoveInvTreesAtoms
    @(FuseRep '[ 'Leaf ja] '[ 'Leaf ja])
    @('[ 'Leaf jb])
    @('[ 'Leaf jc])

-- | Fill a spine with scaled ones (deterministic nested-F sample).
fillRepVScaled
  :: forall ts
   . KnownRep ts
  => RepV ts
fillRepVScaled = go 0 (repSing @ts)
  where
    go :: Int -> SRep ts' -> RepV ts'
    go _ SRepNil = RNil
    go i (SRepCons t rest) =
      case t of
        SLeaf {} ->
          RCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)
        SNode {} ->
          RCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)

-- | @(Hom ⊗ Hom)@ left-assoc / right-assoc spines for leaf-½ (Mac Lane outer F).
type Dom111 = FuseRep (FuseRep Leaf1 Leaf1) Hom11

type Mid111 = FuseRep Leaf1 (FuseRep Leaf1 Hom11)

type CupR111 = FuseRep Leaf1 AssocL111

type Dom000 = FuseRep (FuseRep Leaf0 Leaf0) Hom00

type CupR000 = FuseRep Leaf0 (FuseRep Hom00 Leaf0)

-- | @Fuse(id, F-inv)@ on Mid — instance of 'fuseMapRight'.
fuseMapRightFinv111 :: RepV Mid111 -> RepV CupR111
fuseMapRightFinv111 =
  fuseMapRight @Leaf1 @AssocR111 @AssocL111 fmoveInvTrees111

approxRepV
  :: forall ts
   . KnownRep ts
  => RepV ts
  -> RepV ts
  -> Bool
approxRepV = go (repSing @ts)
  where
    closeVec a b =
      let da = toArray a
          db = toArray b
       in VS.all (\z -> magnitude z < 1e-9) (VS.zipWith (-) da db)
    go :: SRep ts' -> RepV ts' -> RepV ts' -> Bool
    go SRepNil RNil RNil = True
    go (SRepCons t rest) (RCons a as) (RCons b bs) =
      case t of
        SLeaf {} -> closeVec a b && go rest as bs
        SNode {} -> closeVec a b && go rest as bs
    go _ _ _ = False

-- | Tree F round-trip on @½⊗½⊗½@ (@F⁻¹ ∘ F ≈ id@).
checkFmoveTrees111 :: RepV AssocL111 -> Bool
checkFmoveTrees111 tv =
  approxRepV @AssocL111 tv (fmoveInvTrees111 (fmoveTrees111 tv))

-- | Tree F round-trip on @½⊗½⊗0@.
checkFmoveTrees110 :: RepV AssocL110 -> Bool
checkFmoveTrees110 tv =
  approxRepV @AssocL110 tv (fmoveInvTrees110 (fmoveTrees110 tv))

-- | Tree F round-trip on @½⊗½⊗1@.
checkFmoveTrees112 :: RepV AssocL112 -> Bool
checkFmoveTrees112 tv =
  approxRepV @AssocL112 tv (fmoveInvTrees112 (fmoveTrees112 tv))

-- | Round-trip only: works for any atom-leaf triple.
checkFmoveTreesLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
     , KnownRep ( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]) )
     )
  => RepV ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
  -> Bool
checkFmoveTreesLeaves tv =
  let rt = fmoveInvTreesLeaves @ja @jb @jc (fmoveTreesLeaves @ja @jb @jc tv)
   in approxRepV
        @( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
        tv
        rt

-- | Deterministic sample on left-assoc atom spine (sector flats → scatter).
sampleAssocLLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
     )
  => RepV ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
sampleAssocLLeaves =
  let a = fromIntegral (natVal (Proxy @ja)) :: Int
      b = fromIntegral (natVal (Proxy @jb)) :: Int
      c = fromIntegral (natVal (Proxy @jc)) :: Int
      chans =
        [ ( d
          , e
          , a
          , b
          , c
          , VS.replicate
              (d + 1)
              ((0.1 * fromIntegral (d + e + 1)) :+ 0)
          )
        | (d, _, _) <- leftSectors a b c
        , e <- allowedE a b c d
        ]
   in scatterAssocLChannel
        (repSing @( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] ))
        (Map.fromList [((d, e, ra, rb, rc), v) | (d, e, ra, rb, rc, v) <- chans])

-- | Collect left-assoc Hom channels @(d, e, h, irrep)@ from
-- @((a⊗b)_e ⊗ Hom_h)_d@. Key includes Hom root @h@ so F cannot reshuffle
-- distinct Hom genealogies that share the same outer root.
collectAssocLHom
  :: SRep ts
  -> RepV ts
  -> [(Int, Int, Int, VS.Vector (Complex Double))]
collectAssocLHom SRepNil RNil = []
collectAssocLHom (SRepCons t rest) (RCons v rs) =
  case t of
    SNode @d left right ->
      case left of
        SNode {} ->
          ( fromIntegral (natVal (Proxy @d))
          , rootLab left
          , rootLab right
          , toArray v
          )
            : collectAssocLHom rest rs
        SLeaf {} ->
          error "collectAssocLHom: expected Node intermediate"
    SLeaf {} ->
      error "collectAssocLHom: leaf in association spine"

-- | Collect right-assoc Hom channels @(d, f, h, irrep)@ from
-- @(a ⊗ (b ⊗ Hom_h)_f)_d@.
collectAssocRHom
  :: SRep ts
  -> RepV ts
  -> [(Int, Int, Int, VS.Vector (Complex Double))]
collectAssocRHom SRepNil RNil = []
collectAssocRHom (SRepCons t rest) (RCons v rs) =
  case t of
    SNode @d _left right ->
      case right of
        SNode @_ _ midHom ->
          ( fromIntegral (natVal (Proxy @d))
          , rootLab right
          , rootLab midHom
          , toArray v
          )
            : collectAssocRHom rest rs
        SLeaf {} ->
          error "collectAssocRHom: expected Node intermediate"
    SLeaf {} ->
      error "collectAssocRHom: leaf in association spine"

scatterAssocLHom
  :: SRep ts
  -> Map.Map (Int, Int, Int) (VS.Vector (Complex Double))
  -> RepV ts
scatterAssocLHom SRepNil _ = RNil
scatterAssocLHom (SRepCons (t :: SIrrepTree u) rest) m =
  case t of
    SNode @d left right ->
      let key =
            ( fromIntegral (natVal (Proxy @d))
            , rootLab left
            , rootLab right
            )
       in RCons @u
            (unsafeFromArray (Map.findWithDefault (zeroLike key m) key m))
            (scatterAssocLHom rest m)
    SLeaf {} ->
      error "scatterAssocLHom: leaf in association spine"

scatterAssocRHom
  :: SRep ts
  -> Map.Map (Int, Int, Int) (VS.Vector (Complex Double))
  -> RepV ts
scatterAssocRHom SRepNil _ = RNil
scatterAssocRHom (SRepCons (t :: SIrrepTree u) rest) m =
  case t of
    SNode @d _left right ->
      case right of
        SNode @_ _ midHom ->
          let key =
                ( fromIntegral (natVal (Proxy @d))
                , rootLab right
                , rootLab midHom
                )
           in RCons @u
                (unsafeFromArray (Map.findWithDefault (zeroLike key m) key m))
                (scatterAssocRHom rest m)
        SLeaf {} ->
          error "scatterAssocRHom: expected Node intermediate"
    SLeaf {} ->
      error "scatterAssocRHom: leaf in association spine"

-- | Zero vector matching any sample in @m@ (same irrep dim as that @d@ block).
zeroLike
  :: (Int, Int, Int)
  -> Map.Map (Int, Int, Int) (VS.Vector (Complex Double))
  -> VS.Vector (Complex Double)
zeroLike (d, _, _) m =
  case [v | ((d', _, _), v) <- Map.toList m, d' == d] of
    (v : _) -> VS.replicate (VS.length v) 0
    [] -> VS.replicate (d + 1) 0

-- | Outer F for @Fuse(Fuse(a,b), Hom) → Fuse(a, Fuse(b, Hom))@ with Hom a
-- list of leaf–leaf channels. Runs atom F per Hom root @h@ so genealogy of
-- the Hom factor is preserved (forgetful flat F reshuffles same-root copies).
fmoveOuterLeafHom
  :: forall ja jb ls rs
   . ( KnownNat ja
     , KnownNat jb
     , KnownRep ls
     , KnownRep rs
     )
  => RepV ls
  -> RepV rs
fmoveOuterLeafHom tv =
  let a = fromIntegral (natVal (Proxy @ja)) :: Int
      b = fromIntegral (natVal (Proxy @jb)) :: Int
      chans = collectAssocLHom (repSing @ls) tv
      hs = Map.keys $ Map.fromList [(h, ()) | (_, _, h, _) <- chans]
      out =
        concatMap
          ( \h ->
              let chH = [(d, e, v) | (d, e, h', v) <- chans, h' == h]
                  buf =
                    packAtomsFlat
                      (leftSectors a b h)
                      (\d -> allowedE a b h d)
                      chH
                  buf' = fmoveAtomsFlat False a b h buf
                  unpacked =
                    unpackAtomsFlat
                      (rightSectors a b h)
                      (\d -> allowedF a b h d)
                      buf'
               in [(d, f, h, v) | (d, f, v) <- unpacked]
          )
          hs
   in scatterAssocRHom
        (repSing @rs)
        (Map.fromList [((d, f, h), v) | (d, f, h, v) <- out])

fmoveInvOuterLeafHom
  :: forall ja jb rs ls
   . ( KnownNat ja
     , KnownNat jb
     , KnownRep rs
     , KnownRep ls
     )
  => RepV rs
  -> RepV ls
fmoveInvOuterLeafHom tv =
  let a = fromIntegral (natVal (Proxy @ja)) :: Int
      b = fromIntegral (natVal (Proxy @jb)) :: Int
      chans = collectAssocRHom (repSing @rs) tv
      hs = Map.keys $ Map.fromList [(h, ()) | (_, _, h, _) <- chans]
      out =
        concatMap
          ( \h ->
              let chH = [(d, f, v) | (d, f, h', v) <- chans, h' == h]
                  buf =
                    packAtomsFlat
                      (rightSectors a b h)
                      (\d -> allowedF a b h d)
                      chH
                  buf' = fmoveAtomsFlat True a b h buf
                  unpacked =
                    unpackAtomsFlat
                      (leftSectors a b h)
                      (\d -> allowedE a b h d)
                      buf'
               in [(d, e, h, v) | (d, e, v) <- unpacked]
          )
          hs
   in scatterAssocLHom
        (repSing @ls)
        (Map.fromList [((d, e, h), v) | (d, e, h, v) <- out])

--------------------------------------------------------------------------------
-- Tree helpers used by fused cup / cap
--------------------------------------------------------------------------------

-- | Frobenius–Schur cup factor @FS(j)·dim(j)@ for SU(2) (@tj = 2j@).
-- @FS = (−1)^{tj}@, @dim = tj + 1@.
su2CupFactor :: Int -> Complex Double
su2CupFactor tj =
  let fs = if even tj then 1 else -1
      dim = fromIntegral (tj + 1) :: Double
   in (fs * dim) :+ 0

scaleRepV
  :: forall ts
   . KnownRep ts
  => Complex Double
  -> RepV ts
  -> RepV ts
scaleRepV s = go (repSing @ts)
  where
    go :: SRep ts' -> RepV ts' -> RepV ts'
    go SRepNil RNil = RNil
    go (SRepCons t rest) (RCons v rs) =
      case t of
        SLeaf {} -> RCons (s *^ v) (go rest rs)
        SNode {} -> RCons (s *^ v) (go rest rs)

-- | Singlet-only identity in 'Hom11' (@j=0@ channel).
idHom11 :: RepV Hom11
idHom11 = idHomLeaf @1

-- | Singlet-only identity in 'Hom22'.
idHom22 :: RepV Hom22
idHom22 = idHomLeaf @2

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
-- Singlet channels scaled by 'su2CupFactor' of the cupped root (FS·dim); others drop.
cup
  :: forall b
   . KnownRep (FuseRep b b)
  => RepV (FuseRep b b)
  -> RepV Unit
cup bb =
  RCons @('Leaf 0) (konst (cupHomTreesScalar @(FuseRep b b) bb)) RNil

-- | Singlet walk via 'SRep': @sameNat@ refines @j ~ 0@ so payloads stay @C 1@.
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
unitor = unitorGo (repSing @(FuseRep Unit c))

-- | Singleton walk: @sameNat@ refines left child to @'Leaf 0@; 'UnitorCodomain' drops it.
unitorGo
  :: forall uc
   . SRep uc
  -> RepV uc
  -> RepV (UnitorCodomain uc)
unitorGo SRepNil RNil = RNil
unitorGo (SRepCons t rest) (RCons v rs) =
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
                      RCons @('Leaf rj) v (unitorGo rest rs)
                    Nothing ->
                      error "unitorGo: root mismatch after 0⊗t"
                SNode @rj @rl @rr _l _r ->
                  case sameNat (Proxy @rj) (Proxy @j) of
                    Just Refl ->
                      RCons @('Node rj rl rr) v (unitorGo rest rs)
                    Nothing ->
                      error "unitorGo: root mismatch after 0⊗t"
            Nothing ->
              error "unitorGo: expected left child 'Leaf 0"
        SNode {} ->
          error "unitorGo: expected left child 'Leaf 0"
    SLeaf {} ->
      error "unitorGo: expected Node from FuseRep Unit"

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

-- | Approx equality on Hom / association spines (forgetful flat).
approxHomTrees
  :: forall ts
   . KnownRep ts
  => RepV ts
  -> RepV ts
  -> Bool
approxHomTrees u v =
  let bu = repVToForgetFlat @ts u
      bv = repVToForgetFlat @ts v
      err =
        VS.sum $
          VS.zipWith
            (\x y -> let d = x - y in realPart (d * conjugate d))
            bu
            bv
   in err < 1e-10

approxHom11 :: RepV Hom11 -> RepV Hom11 -> Bool
approxHom11 = approxHomTrees @Hom11

-- | 'unitor' on @Unit ⊗ Leaf½@: payload round-trip.
checkUnitorLeaf1 :: Bool
checkUnitorLeaf1 =
  let u =
        RCons @('Node 1 ('Leaf 0) ('Leaf 1)) (konst 0.42) RNil
          :: RepV (FuseRep Unit Leaf1)
      v = unitor @Leaf1 u
   in case repVToV @Leaf1 v of
        x ->
          let d = x ^-^ konst 0.42
           in magnitude (d <.> d) < 1e-18

-- | 'unitorHom' = 'fuseMapRight' 'unitor' on after-cup leaf-½ spine.
checkUnitorHom11 :: Bool
checkUnitorHom11 =
  let mid =
        RCons @('Node 0 ('Leaf 1) ('Node 1 ('Leaf 0) ('Leaf 1))) (konst 0.3) $
          RCons @('Node 2 ('Leaf 1) ('Node 1 ('Leaf 0) ('Leaf 1))) (konst 0.7) RNil
      out = unitorHom @Leaf1 @Leaf1 mid
   in approxHom11 out $
        RCons @('Node 0 ('Leaf 1) ('Leaf 1)) (konst 0.3) $
          RCons @('Node 2 ('Leaf 1) ('Leaf 1)) (konst 0.7) RNil

-- | Mac Lane 'cup' on leaf Hom: singlet × FS·dim (@0 → 1@, @½ → −2@, @1 → 3@).
checkCupLeafHom :: Bool
checkCupLeafHom =
  let s0 =
        case cup @Leaf0 (idHomLeaf @0) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
      s1 =
        case cup @Leaf1 (idHomLeaf @1) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
      s2 =
        case cup @Leaf2 (idHomLeaf @2) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
   in magnitude (s0 - 1) < 1e-12
        && magnitude (s1 - (-2)) < 1e-12
        && magnitude (s2 - 3) < 1e-12

-- | Typechecks 'cupTensorIdHom' at leaf-½ (do not require a full sample spine here).
cupTensorIdHomLeaf1
  :: RepV (FuseRep Leaf1 (FuseRep Hom11 Leaf1))
  -> RepV (FuseRep Leaf1 (FuseRep Unit Leaf1))
cupTensorIdHomLeaf1 = cupTensorIdHom @Leaf1 @Leaf1 @Leaf1

-- | Five-morphism 'composeHomTrees' unit laws on leaf-½.
checkComposeHomTrees111 :: Bool
checkComposeHomTrees111 =
  let f =
        RCons @('Node 0 ('Leaf 1) ('Leaf 1)) (konst 0.3) $
          RCons @('Node 2 ('Leaf 1) ('Leaf 1)) (konst 0.7) RNil
      idH = idHomLeaf @1
      idid = composeHomTrees @Leaf1 @Leaf1 @Leaf1 idH idH
      fid = composeHomTrees @Leaf1 @Leaf1 @Leaf1 f idH
      idf = composeHomTrees @Leaf1 @Leaf1 @Leaf1 idH f
   in approxHomTrees @Hom11 idid idH
        && approxHomTrees @Hom11 fid f
        && approxHomTrees @Hom11 idf f

-- | Five-morphism compose unit laws on trivial Hom.
checkComposeHomTrees000 :: Bool
checkComposeHomTrees000 =
  let f = RCons @('Node 0 ('Leaf 0) ('Leaf 0)) (konst 0.4) RNil
      idH = idHomLeaf @0
   in approxHomTrees @Hom00
        (composeHomTrees @Leaf0 @Leaf0 @Leaf0 idH idH)
        idH
        && approxHomTrees @Hom00
          (composeHomTrees @Leaf0 @Leaf0 @Leaf0 f idH)
          f
        && approxHomTrees @Hom00
          (composeHomTrees @Leaf0 @Leaf0 @Leaf0 idH f)
          f

-- | Leaf spin-1 Hom compose: @id∘id ≈ id@ and left/right units on multi-channel Hom.
checkComposeHomTrees222 :: Bool
checkComposeHomTrees222 =
  let f =
        RCons @('Node 0 ('Leaf 2) ('Leaf 2)) (konst 0.2) $
          RCons @('Node 2 ('Leaf 2) ('Leaf 2)) (konst 0.3) $
            RCons @('Node 4 ('Leaf 2) ('Leaf 2)) (konst 0.5) RNil
      idH = idHomLeaf @2
      idid = composeHomTrees @Leaf2 @Leaf2 @Leaf2 idH idH
      fid = composeHomTrees @Leaf2 @Leaf2 @Leaf2 f idH
      idf = composeHomTrees @Leaf2 @Leaf2 @Leaf2 idH f
   in approxHomTrees @Hom22 idid idH
        && approxHomTrees @Hom22 fid f
        && approxHomTrees @Hom22 idf f

-- | Polymorphic leaf F + outer Hom: unit laws on @tj = 3@.
checkComposeHomTrees333 :: Bool
checkComposeHomTrees333 =
  let f =
        RCons @('Node 0 ('Leaf 3) ('Leaf 3)) (konst 0.1) $
          RCons @('Node 2 ('Leaf 3) ('Leaf 3)) (konst 0.2) $
            RCons @('Node 4 ('Leaf 3) ('Leaf 3)) (konst 0.3) $
              RCons @('Node 6 ('Leaf 3) ('Leaf 3)) (konst 0.4) RNil
      idH = idHomLeaf @3
      idid = composeHomTrees @Leaf3 @Leaf3 @Leaf3 idH idH
      fid = composeHomTrees @Leaf3 @Leaf3 @Leaf3 f idH
      idf = composeHomTrees @Leaf3 @Leaf3 @Leaf3 idH f
   in approxHomTrees @Hom33 idid idH
        && approxHomTrees @Hom33 fid f
        && approxHomTrees @Hom33 idf f

-- | Unequal-leaf compose @½ → 1 → ½@: left/right units on 'Hom12'.
checkComposeHomTrees121 :: Bool
checkComposeHomTrees121 =
  let f :: RepV Hom12
      f =
        RCons @('Node 1 ('Leaf 1) ('Leaf 2)) (konst 0.3) $
          RCons @('Node 3 ('Leaf 1) ('Leaf 2)) (konst 0.7) RNil
      id1 = idHomLeaf @1
      id2 = idHomLeaf @2
      -- f ∘ id₁  and  id₂ ∘ f
      idf = composeHomTrees @Leaf1 @Leaf1 @Leaf2 id1 f
      fid = composeHomTrees @Leaf1 @Leaf2 @Leaf2 f id2
   in approxHomTrees @Hom12 idf f && approxHomTrees @Hom12 fid f

-- | Atom-leaf F round-trip for @½⊗1⊗½@ via polymorphic 'CanFmoveTrees'.
checkFmoveTreesLeaves121 :: Bool
checkFmoveTreesLeaves121 =
  let assocL = sampleAssocLLeaves @1 @2 @1
      rt =
        fmoveInvTrees @Leaf1 @Leaf2 @Leaf1
          (fmoveTrees @Leaf1 @Leaf2 @Leaf1 assocL)
   in approxHomTrees @( FuseRep (FuseRep Leaf1 Leaf2) Leaf1 ) assocL rt

-- | Nested F: Hom⊗leaf⊗leaf (@Hom11 ⊗ ½ ⊗ ½@) round-trip via channel-keyed F.
checkFmoveHomLeft111 :: Bool
checkFmoveHomLeft111 =
  let assocL = fillRepVScaled @( FuseRep (FuseRep Hom11 Leaf1) Leaf1 )
      rt =
        fmoveInvTreesHomLeft @1 @1 @1
          (fmoveTreesHomLeft @1 @1 @1 assocL)
   in approxHomTrees @( FuseRep (FuseRep Hom11 Leaf1) Leaf1 ) assocL rt

--------------------------------------------------------------------------------
-- HomFused: RepV-backed fused Hom
--------------------------------------------------------------------------------

-- | 'HomFused' compose via the five Mac Lane morphisms ('composeHomTrees').
composeHomFused
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
  => HomFused b c
  -> HomFused a b
  -> HomFused a c
composeHomFused (HomFused g) (HomFused f) =
  HomFused (composeHomTrees @a @b @c f g)

instance Category HomFused where
  type Object HomFused a = KnownHomFused a

  id :: forall a. Object HomFused a => HomFused a a
  id = HomFused (idHomFusedVal @a)

  -- @(.)@ needs the five Mac Lane steps on @a,b,c@, which 'Object' alone does
  -- not imply. Use 'composeHomFused'.
  (.) = undefined

-- | 'HomFused' packaging unit laws on spin-1 via 'composeHomFused'.
checkHomFusedCategory222 :: Bool
checkHomFusedCategory222 =
  let f :: HomFused Leaf2 Leaf2
      f =
        HomFused $
          RCons @('Node 0 ('Leaf 2) ('Leaf 2)) (konst 0.2) $
            RCons @('Node 2 ('Leaf 2) ('Leaf 2)) (konst 0.3) $
              RCons @('Node 4 ('Leaf 2) ('Leaf 2)) (konst 0.5) RNil
      idT = HomFused (idHomFusedVal @Leaf2)
      HomFused idid = composeHomFused @Leaf2 @Leaf2 @Leaf2 idT idT
      HomFused fid = composeHomFused @Leaf2 @Leaf2 @Leaf2 idT f
      HomFused idf = composeHomFused @Leaf2 @Leaf2 @Leaf2 f idT
   in approxHomTrees @Hom22 idid (idHomLeaf @2)
        && approxHomTrees @Hom22 fid (unHomFused f)
        && approxHomTrees @Hom22 idf (unHomFused f)

-- | 'HomFused' unit laws on @tj = 3@ via polymorphic 'KnownHomFused' / 'idHomLeaf'.
checkHomFusedCategory333 :: Bool
checkHomFusedCategory333 =
  let f :: HomFused Leaf3 Leaf3
      f =
        HomFused $
          RCons @('Node 0 ('Leaf 3) ('Leaf 3)) (konst 0.1) $
            RCons @('Node 2 ('Leaf 3) ('Leaf 3)) (konst 0.2) $
              RCons @('Node 4 ('Leaf 3) ('Leaf 3)) (konst 0.3) $
                RCons @('Node 6 ('Leaf 3) ('Leaf 3)) (konst 0.4) RNil
      idT = HomFused (idHomFusedVal @Leaf3)
      HomFused idid = composeHomFused @Leaf3 @Leaf3 @Leaf3 idT idT
      HomFused fid = composeHomFused @Leaf3 @Leaf3 @Leaf3 idT f
      HomFused idf = composeHomFused @Leaf3 @Leaf3 @Leaf3 f idT
   in approxHomTrees @Hom33 idid (idHomFusedVal @Leaf3)
        && approxHomTrees @Hom33 fid (unHomFused f)
        && approxHomTrees @Hom33 idf (unHomFused f)

-- | Spin-1 leaf smoke: atom F + outer Hom F round-trips.
checkLeaf2FmoveSmoke :: Bool
checkLeaf2FmoveSmoke =
  let assocL = sampleAssocLLeaves @2 @2 @2
      assocOk =
        approxHomTrees @( FuseRep (FuseRep Leaf2 Leaf2) Leaf2 ) assocL $
          fmoveInvTreesLeaves @2 @2 @2 (fmoveTreesLeaves @2 @2 @2 assocL)
      idH = idHomLeaf @2
      dom = fuseRepTerm @Hom22 @Hom22 idH idH
      mid = fmoveOuterHom @Leaf2 @Leaf2 @Leaf2 dom
      back = fmoveInvOuterHom @Leaf2 @Leaf2 @Leaf2 mid
   in assocOk && approxHomTrees @( FuseRep (FuseRep Leaf2 Leaf2) Hom22 ) dom back

-- | Outer F round-trip on Dom = Fuse(id,id): @F⁻¹ ∘ F ≈ id@.
checkFmoveOuter111 :: Bool
checkFmoveOuter111 =
  let dom = fuseRepTerm @Hom11 @Hom11 (idHomLeaf @1) (idHomLeaf @1)
      mid = fmoveOuterHom @Leaf1 @Leaf1 @Leaf1 dom
      back = fmoveInvOuterHom @Leaf1 @Leaf1 @Leaf1 mid
   in approxHomTrees @Dom111 dom back

-- | 'fuseMapLeft id' is the identity on Mid.
checkFuseMapLeftId111 :: Bool
checkFuseMapLeftId111 =
  let mid =
        fmoveOuterHom @Leaf1 @Leaf1 @Leaf1 $
          fuseRepTerm @Hom11 @Hom11 (idHomLeaf @1) (idHomLeaf @1)
      mid' = fuseMapLeft @Leaf1 @Leaf1 @AssocR111 id mid
   in approxHomTrees @Mid111 mid mid'

-- | Forgetful coalesced flat of a 'RepV' (same layout as 'fuseSU2Flat' output /
-- 'ForgetRep'): sectors sorted by root @2j@, multiplicity = spine order.
repVToForgetFlat
  :: forall ts
   . KnownRep ts
  => RepV ts
  -> VS.Vector (Complex Double)
repVToForgetFlat = packRootChannels . collectRootChannels (repSing @ts)

collectRootChannels
  :: SRep ts
  -> RepV ts
  -> [(Int, VS.Vector (Complex Double))]
collectRootChannels SRepNil RNil = []
collectRootChannels (SRepCons t rest) (RCons v rs) =
  case t of
    SLeaf @j ->
      (fromIntegral (natVal (Proxy @j)), toArray v)
        : collectRootChannels rest rs
    SNode @j _ _ ->
      (fromIntegral (natVal (Proxy @j)), toArray v)
        : collectRootChannels rest rs
collectRootChannels _ _ =
  error "collectRootChannels: RepV / SRep mismatch"

packRootChannels
  :: [(Int, VS.Vector (Complex Double))]
  -> VS.Vector (Complex Double)
packRootChannels chans =
  let byJ =
        Prelude.foldl
          (\m (j, v) -> Map.insertWith (flip (++)) j [v] m)
          Map.empty
          chans
   in VS.concat [VS.concat vs | (_, vs) <- Map.toAscList byJ]

-- | Inverse of 'repVToForgetFlat' for a known spine (pops mult copies in spine order).
forgetFlatToRepV
  :: forall ts
   . KnownRep ts
  => VS.Vector (Complex Double)
  -> RepV ts
forgetFlatToRepV buf =
  let s = repSing @ts
      byJ0 = splitForgetByRoots (treeRootList s) buf
   in scatterRootChannels s byJ0

splitForgetByRoots
  :: [Int]
  -> VS.Vector (Complex Double)
  -> Map.Map Int [VS.Vector (Complex Double)]
splitForgetByRoots roots buf =
  let counts =
        Prelude.foldl
          (\m j -> Map.insertWith (+) j 1 m)
          Map.empty
          roots
      sortedJs = Map.keys counts
      offsets =
        Map.fromList $
          zip
            sortedJs
            (scanl (+) 0 [counts Map.! j * (j + 1) | j <- sortedJs])
      sliceJ j =
        let mult = counts Map.! j
            d = j + 1
            off = offsets Map.! j
         in [ VS.slice (off + μ * d) d buf
            | μ <- [0 .. mult - 1]
            ]
   in Map.fromList [(j, sliceJ j) | j <- sortedJs]

scatterRootChannels
  :: SRep ts
  -> Map.Map Int [VS.Vector (Complex Double)]
  -> RepV ts
scatterRootChannels SRepNil _ = RNil
scatterRootChannels (SRepCons (t :: SIrrepTree u) rest) m =
  case t of
    SLeaf @j ->
      let tj = fromIntegral (natVal (Proxy @j)) :: Int
       in case Map.lookup tj m of
            Just (v : vs) ->
              RCons @u
                (unsafeFromArray v)
                (scatterRootChannels rest (Map.insert tj vs m))
            _ ->
              error "scatterRootChannels: missing multiplicity slot"
    SNode @j _ _ ->
      let tj = fromIntegral (natVal (Proxy @j)) :: Int
       in case Map.lookup tj m of
            Just (v : vs) ->
              RCons @u
                (unsafeFromArray v)
                (scatterRootChannels rest (Map.insert tj vs m))
            _ ->
              error "scatterRootChannels: missing multiplicity slot"

-- | Naturality of @Fuse(a, –)@: @refuse ∘ (id ⊗ f) ∘ unfuse@ on fusion trees.
--
-- Uses /expanded/ sector lists (one multiplicity slot per tree in spine order)
-- so same-root genealogies are not coalesced before @id ⊗ f@. Coalesced forget
-- flats reshuffle @Fuse(Leaf, Assoc)@ multiplicity and break Hom-compose unit
-- laws for spin-1.
fuseMapRight
  :: forall a q q'
   . ( KnownRep a
     , KnownRep q
     , KnownRep q'
     , KnownRep (FuseRep a q)
     , KnownRep (FuseRep a q')
     )
  => (RepV q -> RepV q')
  -> RepV (FuseRep a q)
  -> RepV (FuseRep a q')
fuseMapRight f tv =
  let secsA = repExpandedSectors (repSing @a)
      secsQ = repExpandedSectors (repSing @q)
      secsQ' = repExpandedSectors (repSing @q')
      fFlat =
        repVToExpandedFlat @q' . f . expandedFlatToRepV @q
      vin = repVToForgetFlat @(FuseRep a q) tv
      vout = fuseMapRightFlatSectors secsA secsQ secsQ' fFlat vin
   in forgetFlatToRepV @(FuseRep a q') vout

-- | Expanded @(tj, 1, off)@ sectors — one slot per tree (spine order).
repExpandedSectors :: SRep ts -> [(Int, Int, Int)]
repExpandedSectors = go 0
  where
    go :: Int -> SRep ts' -> [(Int, Int, Int)]
    go _ SRepNil = []
    go off (SRepCons t rest) =
      let tj = rootLab t
          d = tj + 1
       in (tj, 1, off) : go (off + d) rest

-- | Concatenate root vectors in spine order (matches 'repExpandedSectors').
repVToExpandedFlat
  :: forall ts
   . KnownRep ts
  => RepV ts
  -> VS.Vector (Complex Double)
repVToExpandedFlat = go (repSing @ts)
  where
    go :: SRep ts' -> RepV ts' -> VS.Vector (Complex Double)
    go SRepNil RNil = VS.empty
    go (SRepCons t rest) (RCons v rs) =
      case t of
        SLeaf {} -> toArray v VS.++ go rest rs
        SNode {} -> toArray v VS.++ go rest rs
    go _ _ = error "repVToExpandedFlat: RepV / SRep mismatch"

-- | Inverse of 'repVToExpandedFlat'.
expandedFlatToRepV
  :: forall ts
   . KnownRep ts
  => VS.Vector (Complex Double)
  -> RepV ts
expandedFlatToRepV buf = go 0 (repSing @ts)
  where
    go :: Int -> SRep ts' -> RepV ts'
    go _ SRepNil = RNil
    go off (SRepCons (t :: SIrrepTree u) rest) =
      case t of
        SLeaf @j ->
          let d = fromIntegral (natVal (Proxy @j)) + 1
              v = unsafeFromArray (VS.slice off d buf)
           in RCons @u v (go (off + d) rest)
        SNode @j _ _ ->
          let d = fromIntegral (natVal (Proxy @j)) + 1
              v = unsafeFromArray (VS.slice off d buf)
           in RCons @u v (go (off + d) rest)

-- | Coalesced @(tj, multiplicity)@ pairs matching 'ForgetRep' / 'fuseSU2Flat'.
forgetSectorPairs :: SRep ts -> [(Int, Int)]
forgetSectorPairs =
  Map.toAscList
    . Prelude.foldl
      (\m j -> Map.insertWith (+) j 1 m)
      Map.empty
    . treeRootList

treeRootList :: SRep ts -> [Int]
treeRootList SRepNil = []
treeRootList (SRepCons t rest) = rootLab t : treeRootList rest

fuseMapLeft
  :: forall a a' b
   . ( KnownRep a
     , KnownRep a'
     , KnownRep b
     , KnownRep (FuseRep a b)
     , KnownRep (FuseRep a' b)
     )
  => (RepV a -> RepV a')
  -> RepV (FuseRep a b)
  -> RepV (FuseRep a' b)
fuseMapLeft f tv =
  let secsA = repExpandedSectors (repSing @a)
      secsA' = repExpandedSectors (repSing @a')
      secsB = repExpandedSectors (repSing @b)
      fFlat =
        repVToExpandedFlat @a' . f . expandedFlatToRepV @a
      vin = repVToForgetFlat @(FuseRep a b) tv
      vout = fuseMapLeftFlatSectors secsA secsA' secsB fFlat vin
   in forgetFlatToRepV @(FuseRep a' b) vout

