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

-- | Term-level symbolic SU(2) reps: singletons, 'RepV', coalesce / cup.
--
-- Type kinds and families live in 'Experiments.Symbolic.Expr' /
-- 'Experiments.Symbolic.TypeLevel'. Flat-buffer oracles:
-- 'Experiments.Symbolic.Reference'. Examples: 'Experiments.SymbolicExamples'.
--
-- Sectors are atom-keyed. Unfused tensor / dual spaces are 'ToVSpine' values
-- ('rtensor' / 'rdual' / 'rmor'), paired by 'cupUnfused' / 'cupRdual'.
-- Fused monoidal product is genealogy-preserving 'fuseTrees' /
-- 'fuseTreeRepTerm' only. Fused Hom is 'HomFused' ('TreeV' of 'FuseTreeRep');
-- compose via 'composeHomTrees' \/ 'composeHomFused' (five Mac Lane steps).
-- Cups: 'cupFused' / 'capFused' on singlet trees.
module Experiments.Symbolic.Core where

import Data.Complex (Complex ((:+)), conjugate, magnitude, realPart)
import Data.Coerce (coerce)
import Data.Kind (Constraint, Type)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.VectorSpace (AdditiveGroup (zeroV, (^+^), (^-^)), InnerSpace ((<.>)), Scalar, VectorSpace ((*^)), sumV)
import qualified Data.Vector.Storable as VS
import GHC.TypeLits (CmpNat, KnownNat, Nat, natVal, sameNat, type (*), type (+))
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
  , fMultEntry
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
  , LSpace
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
import Math.LinearMap.Coercion (uncurryLinearMap, (-+$=>))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, konst)
import Symmetry.Utils (Append)
import Symmetry.CG.FSymbol (fSymbolHomSU2, fSymbolHomSU2Inv)
import Symmetry.CG.SU2
  ( fuseCGChannel
  , fuseMapLeftFlatSectors
  , fuseMapRightFlatSectors
  )
import Symmetry.FunctorExperiment
  ( ApplyIntertwinerG
  , CollectCompiledGo
  , IntertwinerG (..)
  , RepListG
  , RepLookup
  , ToCG (..)
  , intertwinerLinearG
  )
import Symmetry.Group (Group (..), RepDimG)
import Symmetry.HomBlock (HasHomBlock)
import Symmetry.RepSingleton (KnownRep (..), repSing)
import qualified Symmetry.Tensor as ST
import Symmetry.SU2 (SU2Element, applyWigner)
import TensorNetwork.Categorical
  ( flattenCopyProd
  , fuseBond
  , lassocMap
  , mergeCopyAxis
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

-- | Singleton for 'MultExpr'.
data SMult (μ :: MultExpr) where
  SMultAtom
    :: forall m
     . KnownNat m
    => SMult ('AtomM m)
  SMultProd
    :: SMult μ1
    -> SMult μ2
    -> SMult ('Prod μ1 μ2)

-- | General spine singleton: one 'SIrrep'/'SMult' pair per sector.
data SRep (rs :: Rep) where
  SRepNil :: SRep '[]
  SRepCons
    :: forall e μ rest
     . SIrrep e
    -> SMult μ
    -> SRep rest
    -> SRep ('(e, μ) ': rest)

-- | Materialize 'SRep' for a statically known spine.
class KnownSymRep (rs :: Rep) where
  symRepSing :: SRep rs

instance KnownSymRep '[] where
  symRepSing = SRepNil

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownSymRep rest
  ) =>
  KnownSymRep ('(j, 'AtomM m) ': rest)
  where
  symRepSing =
    SRepCons (SAtomI @j) (SMultAtom @m) (symRepSing @rest)

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j)
  , KnownSymRep rest
  ) =>
  KnownSymRep ('(j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  symRepSing =
    SRepCons
      (SAtomI @j)
      (SMultProd (SMultAtom @m) (SMultAtom @n))
      (symRepSing @rest)

-- | Flat-multiplicity atom spine (subset of 'KnownSymRep'). Walks use 'symRepSing'.
class KnownSymRep rs => KnownAtomRep (rs :: Rep)

instance KnownAtomRep '[]

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownAtomRep rest
  ) =>
  KnownAtomRep ('(j, 'AtomM m) ': rest)

--------------------------------------------------------------------------------
-- Fusion-tree singletons ('Irrep' / 'TreeRep')
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

-- | Singleton spine for 'TreeRep'.
data STreeRep (ts :: TreeRep) where
  STreeNil :: STreeRep '[]
  STreeCons
    :: forall t rest
     . SIrrepTree t
    -> STreeRep rest
    -> STreeRep (t ': rest)

-- | Materialize 'STreeRep' for a statically known tree list.
class KnownTreeRep (ts :: TreeRep) where
  treeRepSing :: STreeRep ts

instance KnownTreeRep '[] where
  treeRepSing = STreeNil

instance
  ( KnownIrrep t
  , KnownTreeRep rest
  ) =>
  KnownTreeRep (t ': rest)
  where
  treeRepSing = STreeCons (irrepSing @t) (treeRepSing @rest)

--------------------------------------------------------------------------------
-- Term-level fusion trees ('TreeV')
--------------------------------------------------------------------------------

-- | Spine of root vectors, indexed by type-level 'TreeRep'.
data TreeV (ts :: TreeRep) where
  TNil :: TreeV '[]
  TCons
    :: forall t rest
     . ToVTree t
    -> TreeV rest
    -> TreeV (t ': rest)

-- | Forgetful map: nonempty 'TreeV' → 'ToVTreeRep'.
treeVToV :: forall ts. KnownTreeRep ts => TreeV ts -> ToVTreeRep ts
treeVToV = go (treeRepSing @ts)
  where
    go :: forall ts'. STreeRep ts' -> TreeV ts' -> ToVTreeRep ts'
    go (STreeCons _ STreeNil) (TCons v TNil) = v
    go (STreeCons _ sRest@(STreeCons {})) (TCons v rest) =
      (v, go sRest rest)
    go _ _ = error "treeVToV: expected nonempty KnownTreeRep"

-- | Inverse of 'treeVToV'.
vToTreeV :: forall ts. KnownTreeRep ts => ToVTreeRep ts -> TreeV ts
vToTreeV = go (treeRepSing @ts)
  where
    go :: forall ts'. STreeRep ts' -> ToVTreeRep ts' -> TreeV ts'
    go (STreeCons (_ :: SIrrepTree t) STreeNil) v =
      TCons @t v TNil
    go (STreeCons (_ :: SIrrepTree t) sRest@(STreeCons {})) (v, rest) =
      TCons @t v (go sRest rest)
    go _ _ = error "vToTreeV: expected nonempty KnownTreeRep"

-- | Append two tree spines.
appendTreeV
  :: TreeV ts1
  -> TreeV ts2
  -> TreeV (Append ts1 ts2)
appendTreeV TNil r2 = r2
appendTreeV (TCons v rest) r2 =
  TCons v (appendTreeV rest r2)

-- | CG one output channel on bare root spaces.
fuseOneChannelTree
  :: forall j1 j2 j
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     , KnownNat (IrrepDim j)
     )
  => C (IrrepDim j1) ⊗ C (IrrepDim j2)
  -> C (IrrepDim j)
fuseOneChannelTree v = fuseCGChannel @j1 @j2 @j $ v

-- | Walk CG channels for a pair of trees → 'TreeV' of @'Node@ outcomes.
class FuseTreesGo (t1 :: Irrep) (t2 :: Irrep) (cg :: [(Nat, Nat)]) where
  fuseTreesGo
    :: C (IrrepDim (Root t1)) ⊗ C (IrrepDim (Root t2))
    -> TreeV (NodesFromCG t1 t2 cg)

instance FuseTreesGo t1 t2 '[] where
  fuseTreesGo _ = TNil

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
    TCons @('Node j t1 t2)
      (fuseOneChannelTree @(Root t1) @(Root t2) @j v)
      (fuseTreesGo @t1 @t2 @rest v)

-- | CG-fuse two fusion trees into the channel list 'FuseTrees'.
fuseTrees
  :: forall t1 t2
   . ( KnownIrrep t1
     , KnownIrrep t2
     , FuseTreesGo t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))
     )
  => ToVTree t1 ⊗ ToVTree t2
  -> TreeV (FuseTrees t1 t2)
fuseTrees =
  fuseTreesGo @t1 @t2 @(TensorIrrepRepSU2 (Root t1) (Root t2))

-- | Constraints for walking 'FuseTreeRep' at the term level.
type family FuseTreeRepTermC (rs :: TreeRep) (qs :: TreeRep) :: Constraint where
  FuseTreeRepTermC '[] _ = ()
  FuseTreeRepTermC (t1 ': rest) qs =
    ( FuseTreeRepOneTermC t1 qs
    , FuseTreeRepTermC rest qs
    )

type family FuseTreeRepOneTermC (t1 :: Irrep) (qs :: TreeRep) :: Constraint where
  FuseTreeRepOneTermC _ '[] = ()
  FuseTreeRepOneTermC t1 (t2 ': rest) =
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
    , FuseTreeRepOneTermC t1 rest
    )

fuseTreeRepOneTerm
  :: forall t1 qs
   . FuseTreeRepOneTermC t1 qs
  => ToVTree t1
  -> STreeRep qs
  -> TreeV qs
  -> TreeV (FuseTreeRepOne t1 qs)
fuseTreeRepOneTerm _ STreeNil TNil = TNil
fuseTreeRepOneTerm v1 (STreeCons (_ :: SIrrepTree t2) qRest) (TCons v2 rest) =
  appendTreeV
    (fuseTrees @t1 @t2 (v1 ⊗ v2))
    (fuseTreeRepOneTerm @t1 v1 qRest rest)

-- | Cartesian fuse of two 'TreeV' spines (matches 'FuseTreeRep').
fuseTreeRepTerm
  :: forall rs qs
   . ( KnownTreeRep rs
     , KnownTreeRep qs
     , FuseTreeRepTermC rs qs
     )
  => TreeV rs
  -> TreeV qs
  -> TreeV (FuseTreeRep rs qs)
fuseTreeRepTerm rs qs =
  fuseTreeRepTermGo (treeRepSing @rs) rs (treeRepSing @qs) qs

fuseTreeRepTermGo
  :: forall rs qs
   . FuseTreeRepTermC rs qs
  => STreeRep rs
  -> TreeV rs
  -> STreeRep qs
  -> TreeV qs
  -> TreeV (FuseTreeRep rs qs)
fuseTreeRepTermGo STreeNil TNil _ _ = TNil
fuseTreeRepTermGo
  (STreeCons (_ :: SIrrepTree t1) rRest)
  (TCons v1 rRestV)
  qSing
  q =
  appendTreeV
    (fuseTreeRepOneTerm @t1 v1 qSing q)
    (fuseTreeRepTermGo rRest rRestV qSing q)

--------------------------------------------------------------------------------
-- Term-level spine ('RepV') and fusion
--
-- Uniform @RCons@: sector shape lives in the type index @'(e, μ)@, not in a
-- GADT constructor per leaf shape. Old constructor names are pattern synonyms
-- for call sites; discriminating walks match @RCons@ / 'SRep'.
--------------------------------------------------------------------------------

-- | Spine of sectors, indexed by type-level 'Rep'.
data RepV (rs :: Rep) where
  RNil :: RepV '[]
  RCons
    :: forall e μ rest
     . ToVSector e μ
    -> RepV rest
    -> RepV ('(e, μ) ': rest)

pattern RConsAtomAtomM
  :: () => (μ ~ 'AtomM m)
  => ToVSector j ('AtomM m)
  -> RepV rest
  -> RepV ('(j, 'AtomM m) ': rest)
pattern RConsAtomAtomM v rs = RCons @j @('AtomM m) v rs

pattern RConsAtomProd
  :: () => (μ ~ 'Prod ('AtomM m) ('AtomM n))
  => ToVSector j ('Prod ('AtomM m) ('AtomM n))
  -> RepV rest
  -> RepV ('(j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
pattern RConsAtomProd v rs =
  RCons @j @('Prod ('AtomM m) ('AtomM n)) v rs

{-# COMPLETE RNil, RCons :: RepV #-}
-- Pattern synonyms remain for call sites; production walks use 'RCons'.

-- | Forgetful map: nonempty 'RepV' → 'ToVSpine' (sector payloads kept).
-- Handles @'AtomM@ and @'Prod ('AtomM m) ('AtomM n)@ (fused CG tags).
repVToV :: forall rs. KnownSymRep rs => RepV rs -> ToVSpine rs
repVToV = go (symRepSing @rs)
  where
    go :: forall rs'. SRep rs' -> RepV rs' -> ToVSpine rs'
    go (SRepCons SAtomI SMultAtom SRepNil) (RCons v RNil) = v
    go (SRepCons SAtomI SMultAtom sRest@(SRepCons {})) (RCons v rest) =
      (v, go sRest rest)
    go (SRepCons SAtomI (SMultProd SMultAtom SMultAtom) SRepNil) (RCons v RNil) = v
    go
      (SRepCons SAtomI (SMultProd SMultAtom SMultAtom) sRest@(SRepCons {}))
      (RCons v rest) =
        (v, go sRest rest)
    go _ _ = error "repVToV: expected nonempty KnownSymRep spine"

-- | Inverse of 'repVToV' (total on nonempty 'KnownSymRep' spines).
vToRepV :: forall rs. KnownSymRep rs => ToVSpine rs -> RepV rs
vToRepV = go (symRepSing @rs)
  where
    go :: forall rs'. SRep rs' -> ToVSpine rs' -> RepV rs'
    go (SRepCons (SAtomI @j) (SMultAtom @m) SRepNil) v =
      RCons @j @('AtomM m) v RNil
    go (SRepCons (SAtomI @j) (SMultAtom @m) sRest@(SRepCons {})) (v, rest) =
      RCons @j @('AtomM m) v (go sRest rest)
    go
      (SRepCons (SAtomI @j) (SMultProd (SMultAtom @m) (SMultAtom @n)) SRepNil)
      v =
        RCons @j @('Prod ('AtomM m) ('AtomM n)) v RNil
    go
      (SRepCons (SAtomI @j) (SMultProd (SMultAtom @m) (SMultAtom @n)) sRest@(SRepCons {}))
      (v, rest) =
        RCons @j @('Prod ('AtomM m) ('AtomM n)) v (go sRest rest)
    go _ _ = error "vToRepV: expected nonempty KnownSymRep spine"

-- | Unfused tensor of two atom spines: @ToVSpine r ⊗ ToVSpine q@ (does not distribute).
rtensor
  :: forall r q
   . ( KnownAtomRep r
     , KnownAtomRep q
     , TensorSpace (ToVSpine r)
     , TensorSpace (ToVSpine q)
     , Scalar (ToVSpine r) ~ Complex Double
     , Scalar (ToVSpine q) ~ Complex Double
     )
  => RepV r
  -> RepV q
  -> ToVSpine r ⊗ ToVSpine q
rtensor x y = repVToV x ⊗ repVToV y

-- | Cons onto a spine (@RCons@; shape from @e@/@μ@).
repCons
  :: forall e μ rest
   . ToVSector e μ
  -> RepV rest
  -> RepV ('(e, μ) ': rest)
repCons = RCons @e @μ

-- | Append two spines (@'Append'@ on keys).
appendRepV
  :: RepV rs1
  -> RepV rs2
  -> RepV (Append rs1 rs2)
appendRepV RNil r2 = r2
appendRepV (RCons v rest) r2 =
  RCons v (appendRepV rest r2)

-- | Unfused atom×atom payload: copy×irrep block for each leg.
type AtomPairV (j1 :: Nat) (j2 :: Nat) (m :: Nat) (n :: Nat) =
  (C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2))

--------------------------------------------------------------------------------
-- Undual (pivotal identification): DualVector → primal atom payload
--
-- Term-level undual is the Riesz inverse ('asTensor' + Hilbert coerce), then
-- Condon–Shortley on the irrep leg, then scale by @√(j+1)@ so the CG singlet
-- matches the DualVector Hilbert cup (@1/√(2j+1)@ from CG × @√(2j+1)@ here).
--------------------------------------------------------------------------------

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

-- | CS dual as a typed morphism on the irrep leg.
csIrrepMap
  :: forall j
   . ( KnownNat j
     , KnownNat (IrrepDim j)
     )
  => C (IrrepDim j) +> C (IrrepDim j)
csIrrepMap = arr (LinearFunction (csIrrepLinear @j))

-- | Inverse of 'dualAtomAtomM', then CS + @√(j+1)@ for cup coherence.
--
-- @DualVector (u ⊗ v) = u +> DualVector v@. With Hilbert @DualVector (C n) ~ C n@,
-- 'asTensor' recovers @DualVector (C m) ⊗ DualVector (C (j+1))@, coerce both
-- factors, apply CS on the irrep factor, scale by @√(IrrepDim j)@.
undualAtomAtomM
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , HilbertSpace (C m)
     , HilbertSpace (C (IrrepDim j))
     )
  => DualVector (ToVSector j ('AtomM m))
  -> ToVSector j ('AtomM m)
undualAtomAtomM φ =
  let tDual =
        asTensor -+$=> φ
          :: DualVector (C m) ⊗ DualVector (C (IrrepDim j))
      riesz =
        ( arr (LinearFunction (coerce :: DualVector (C m) -> C m))
            ⊗^ arr (LinearFunction (coerce :: DualVector (C (IrrepDim j)) -> C (IrrepDim j)))
        )
          $ tDual
      -- Pivotal: CG singlet has @1/√(2j+1)@; cancel it so @cup ∘ fuse ≅ cupRdual@.
      dim = fromIntegral (natVal (Proxy @(IrrepDim j))) :: Double
      scale = sqrt dim :+ 0
   in scale *^ ((id ⊗^ csIrrepMap @j) $ riesz)

-- | Sector algebra helpers below: insert / flatten / merge for 'coalesce'.
-- (Per-sector helpers for 'coalesce'; CG fused ⊗ is 'fuseTreeRepTerm'.)
-- Instance heads stay concrete so 'CmpNat' reduces; bodies match 'RCons'.
class InsertSpine (j :: Nat) (μ :: MultExpr) (rs :: Rep) where
  insertSpine
    :: ToVSector j μ
    -> RepV rs
    -> RepV (InsertSector j μ rs)

instance InsertSpine j μ '[] where
  insertSpine sv RNil = RCons @j @μ sv RNil

instance
  ( CmpNat j j2 ~ ord
  , InsertCompared ord j μ j2 ('AtomM m) rest
  ) =>
  InsertSpine j μ ('(j2, 'AtomM m) ': rest)
  where
  insertSpine sv (RCons sv2 restR) =
    insertCompared @ord @j @μ @j2 @('AtomM m) sv sv2 restR

instance
  ( CmpNat j j2 ~ ord
  , InsertCompared ord j μ j2 ('Prod ('AtomM m) ('AtomM n)) rest
  ) =>
  InsertSpine j μ ('(j2, 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  insertSpine sv (RCons sv2 restR) =
    insertCompared @ord @j @μ @j2 @('Prod ('AtomM m) ('AtomM n)) sv sv2 restR

-- | Compare incoming sector @j@ against spine head @j2@ (@ord ~ CmpNat j j2@).
-- LT/GT are polymorphic; EQ merges the copy axes.
class InsertCompared
  (ord :: Ordering)
  (j :: Nat) (μ :: MultExpr)
  (j2 :: Nat) (μ2 :: MultExpr)
  (rest :: Rep)
 where
  insertCompared
    :: ToVSector j μ
    -> ToVSector j2 μ2
    -> RepV rest
    -> RepV (InsertSectorOrd ord j μ j2 μ2 rest)

instance InsertCompared 'LT j μ j2 μ2 rest where
  insertCompared sv sv2 restR =
    RCons @j @μ sv (RCons @j2 @μ2 sv2 restR)

instance (InsertSpine j μ rest) => InsertCompared 'GT j μ j2 μ2 rest where
  insertCompared sv sv2 restR =
    RCons @j2 @μ2 sv2 (insertSpine @j @μ sv restR)

-- | Flatten a sector's copy axis to @'AtomM (EvalMult μ)@.
class FlattenCopy (j :: Nat) (μ :: MultExpr) where
  flattenCopy
    :: ToVSector j μ
    -> ToVSector j ('AtomM (EvalMult μ))

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  ) =>
  FlattenCopy j ('AtomM m)
  where
  flattenCopy = id

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (m * n)
  , KnownNat (IrrepDim j)
  ) =>
  FlattenCopy j ('Prod ('AtomM m) ('AtomM n))
  where
  flattenCopy = flattenCopyProd @m @n @(IrrepDim j)

-- | Merge two already-flat @'AtomM@ sectors of equal irrep.
class MergeFlat (j :: Nat) (m1 :: Nat) (m2 :: Nat) where
  mergeFlat
    :: ToVSector j ('AtomM m1)
    -> ToVSector j ('AtomM m2)
    -> ToVSector j ('AtomM (m1 + m2))

instance
  ( KnownNat j
  , KnownNat m1
  , KnownNat m2
  , KnownNat (m1 + m2)
  , KnownNat (IrrepDim j)
  ) =>
  MergeFlat j m1 m2
  where
  mergeFlat = mergeCopyAxis @m1 @m2 @(IrrepDim j)

-- | Direct-sum same-irrep sectors along the copy axis (coalesce).
-- Flatten each side to @'AtomM@, then 'MergeFlat'.
class MergeSector (j :: Nat) (μ1 :: MultExpr) (μ2 :: MultExpr) (μOut :: MultExpr) where
  mergeSector
    :: ToVSector j μ1
    -> ToVSector j μ2
    -> ToVSector j μOut

instance
  ( FlattenCopy j μ1
  , FlattenCopy j μ2
  , EvalMult μ1 ~ m1
  , EvalMult μ2 ~ m2
  , mOut ~ m1 + m2
  , μOut ~ 'AtomM mOut
  , KnownNat m1
  , KnownNat m2
  , KnownNat mOut
  , MergeFlat j m1 m2
  ) =>
  MergeSector j μ1 μ2 μOut
  where
  mergeSector v1 v2 =
    mergeFlat @j @m1 @m2
      (flattenCopy @j @μ1 v1)
      (flattenCopy @j @μ2 v2)

instance
  ( j ~ k
  , AddMult μ μ2 ~ μOut
  , MergeSector j μ μ2 μOut
  ) =>
  InsertCompared 'EQ j μ k μ2 rest
  where
  insertCompared sv sv2 restR =
    RCons @j @μOut
      (mergeSector @j @μ @μ2 @μOut sv sv2)
      restR

-- | Constraints for coalescing: 'InsertSpine' into the coalesced tail.
type family CoalesceSpine (rs :: Rep) :: Constraint where
  CoalesceSpine '[] = ()
  CoalesceSpine ('(e, μ) ': rest) =
    ( InsertSpine e μ (Coalesce rest)
    , CoalesceSpine rest
    )

-- | Sort + merge equal irrep keys on a spine ('SRep' fold).
coalesce
  :: forall rs
   . ( KnownSymRep rs
     , CoalesceSpine rs
     )
  => RepV rs
  -> RepV (Coalesce rs)
coalesce = go (symRepSing @rs)
  where
    go :: forall rs'. CoalesceSpine rs' => SRep rs' -> RepV rs' -> RepV (Coalesce rs')
    go SRepNil RNil = RNil
    go (SRepCons @e @μ _ _ rest) (RCons sv rs) =
      insertSpine @e @μ sv (go rest rs)

--------------------------------------------------------------------------------
-- SU(2) group action (Wigner on irrep legs)
--
-- @g ↦ (RepV rs → RepV rs)@: identity on copy axes, @D^{j/2}(g)@ on the irrep
-- factor of each sector.
--------------------------------------------------------------------------------

-- | Wigner @D^{j/2}(g)@ as a typed morphism on the CG magnetic basis.
wignerD
  :: forall j
   . KnownNat j
  => SU2Element
  -> C (IrrepDim j) +> C (IrrepDim j)
wignerD g =
  arr $
    LinearFunction $
      applyWigner (fromIntegral (natVal (Proxy @j))) g

-- | Sector morphism: @id@ on multiplicity, Wigner on the irrep factor.
sectorMap
  :: SIrrep j
  -> SMult μ
  -> SU2Element
  -> ToVSector j μ +> ToVSector j μ
sectorMap (SAtomI @j) SMultAtom g =
  id ⊗^ wignerD @j g
sectorMap (SAtomI @j) (SMultProd SMultAtom SMultAtom) g =
  id ⊗^ wignerD @j g
sectorMap _ _ _ =
  error "Experiments.Symbolic.sectorMap: unsupported multiplicity shape"

-- | Apply 'sectorMap' to a sector payload.
actSector
  :: SIrrep j
  -> SMult μ
  -> SU2Element
  -> ToVSector j μ
  -> ToVSector j μ
actSector se@SAtomI sm@SMultAtom g v =
  sectorMap se sm g $ v
actSector se@SAtomI sm@(SMultProd SMultAtom SMultAtom) g v =
  sectorMap se sm g $ v
actSector se sm g _ =
  sectorMap se sm g `seq`
    error "Experiments.Symbolic.actSector: unsupported multiplicity shape"

-- | Group action on a spine: @SU2Element → (RepV rs → RepV rs)@.
actRep
  :: forall rs
   . KnownSymRep rs
  => SU2Element
  -> RepV rs
  -> RepV rs
actRep g = go (symRepSing @rs)
  where
    go :: forall rs'. SRep rs' -> RepV rs' -> RepV rs'
    go SRepNil RNil = RNil
    go (SRepCons e μ rest) (RCons v rs) =
      RCons (actSector e μ g v) (go rest rs)

--------------------------------------------------------------------------------
-- Dual / cup on spine spaces
--
-- Dual of a spine is @DualVector (ToVSpine rs)@ — no formal dual sector.
--------------------------------------------------------------------------------

-- | Unit amplitude as @ToVSpine Unit@ (@C 1 ⊗ C 1@).
unitToVFromScalar :: Complex Double -> ToVSpine Unit
unitToVFromScalar s = s *^ (konst 1 ⊗ konst 1)

-- | Read the amplitude from @ToVSpine Unit@.
unitToVScalar :: ToVSpine Unit -> Complex Double
unitToVScalar u = VS.head (toArray u)

-- | Unit element as a 'RepV' spine (fused / atom-spine API).
unitFromScalar :: Complex Double -> RepV Unit
unitFromScalar = vToRepV @Unit . unitToVFromScalar

-- | Read the amplitude stored in a 'Unit' 'RepV'.
unitScalar :: RepV Unit -> Complex Double
unitScalar = unitToVScalar . repVToV @Unit

-- | Dual of a leaf atom sector → @DualVector (C m ⊗ C (j+1))@.
--
-- Canonical Riesz via 'InnerSpace': linear form @w ↦ v <.> w@ (linear in @w@),
-- then 'fromLinearForm'. Not @w ↦ w <.> v@ (antilinear in @w@) and not
-- 'euclideanNorm' (that is @coerce@, only valid when @DualVector v ~ v@).
dualAtomAtomM
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , InnerSpace (ToVSector j ('AtomM m))
     , Scalar (ToVSector j ('AtomM m)) ~ Complex Double
     )
  => ToVSector j ('AtomM m)
  -> DualVector (ToVSector j ('AtomM m))
dualAtomAtomM v =
  fromLinearForm
    -+$> ( arr (LinearFunction ((v <.>)))
             :: ToVSector j ('AtomM m) +> Complex Double
         )

-- | Dual of an atom spine as @DualVector (ToVSpine rs)@.
rdual
  :: forall rs
   . KnownAtomRep rs
  => RepV rs
  -> DualVector (ToVSpine rs)
rdual = go (symRepSing @rs) . repVToV
  where
    go :: forall rs'. SRep rs' -> ToVSpine rs' -> DualVector (ToVSpine rs')
    go (SRepCons (SAtomI @j) (SMultAtom @m) SRepNil) v =
      dualAtomAtomM @j @m v
    go (SRepCons (SAtomI @j) (SMultAtom @m) sRest@(SRepCons {})) (v, rest) =
      (dualAtomAtomM @j @m v, go sRest rest)
    go _ _ = error "rdual: expected nonempty atom spine"

-- | Pivotal undual of an atom spine (@'undualAtomAtomM'@ per sector).
undualSpine
  :: forall rs
   . KnownAtomRep rs
  => DualVector (ToVSpine rs)
  -> ToVSpine rs
undualSpine = go (symRepSing @rs)
  where
    go :: forall rs'. SRep rs' -> DualVector (ToVSpine rs') -> ToVSpine rs'
    go (SRepCons (SAtomI @j) (SMultAtom @m) SRepNil) φ =
      undualAtomAtomM @j @m φ
    go (SRepCons (SAtomI @j) (SMultAtom @m) sRest@(SRepCons {})) (φ, rest) =
      (undualAtomAtomM @j @m φ, go sRest rest)
    go _ _ = error "undualSpine: expected nonempty atom spine"

-- | Unfused morphism space @DualVector (ToVSpine r) ⊗ ToVSpine q@.
rmor
  :: forall r q
   . ( KnownAtomRep r
     , KnownAtomRep q
     , TensorSpace (DualVector (ToVSpine r))
     , TensorSpace (ToVSpine q)
     , Scalar (DualVector (ToVSpine r)) ~ Complex Double
     , Scalar (ToVSpine q) ~ Complex Double
     )
  => RepV r
  -> RepV q
  -> (DualVector (ToVSpine r) ⊗ ToVSpine q)
rmor x y = rdual x ⊗ repVToV y

--------------------------------------------------------------------------------
-- Cup / cap (compact closed)
--
-- Unfused: closed in 'ToVSpine' / Dual-left Hom @Dual r ⊗ q@ / cups @r ⊗ Dual r@
-- (including @Unit@).
-- Fused: 'cupFused' / 'capFused' on singlet-root trees ('FilterTrivialTrees').
--------------------------------------------------------------------------------

-- | Unfused evaluation @ε : r ⊗ r* → 𝟙@.
cupUnfused
  :: forall r
   . ( KnownAtomRep r
     , LinearSpace (ToVSpine r)
     , LinearSpace (DualVector (ToVSpine r))
     , Scalar (ToVSpine r) ~ Complex Double
     , Scalar (DualVector (ToVSpine r)) ~ Complex Double
     )
  => (ToVSpine r ⊗ DualVector (ToVSpine r))
  -> ToVSpine Unit
cupUnfused t =
  unitToVFromScalar
    ( getLinearFunction
        trace
        (fromTensor -+$=> (swapMap $ t))
    )

-- | Unfused coevaluation @η : 𝟙 → r ⊗ r*@ (linearmap 'idTensor').
capUnfused
  :: forall r
   . ( KnownAtomRep r
     , LinearSpace (ToVSpine r)
     , LinearSpace (DualVector (ToVSpine r))
     , Scalar (ToVSpine r) ~ Complex Double
     , Scalar (DualVector (ToVSpine r)) ~ Complex Double
     )
  => ToVSpine Unit
  -> (ToVSpine r ⊗ DualVector (ToVSpine r))
capUnfused u = unitToVScalar u *^ idTensor @(ToVSpine r)

-- | Hom scalar from flat @'AtomM m@ trivial channel.
cupHomScalarAtomM
  :: forall m
   . ( KnownNat m
     , KnownNat (m * 1)
     , HilbertSpace (C m)
     , InnerSpace (C m)
     , Scalar (C m) ~ Complex Double
     )
  => ToVSector 0 ('AtomM m)
  -> Complex Double
cupHomScalarAtomM hom =
  let flat = fuseBond @m @1 $ hom
   in flat <.> flat

-- | Hom scalar from @0@ / @'Prod m m@ (copy-leg trace).
cupHomScalar
  :: forall m
   . ( KnownNat m
     , KnownNat (m * 1)
     , HilbertSpace (C m)
     , InnerSpace (C m)
     , Scalar (C m) ~ Complex Double
     )
  => ToVSector 0 ('Prod ('AtomM m) ('AtomM m))
  -> Complex Double
cupHomScalar t =
  let peeled =
        ((id ⊗^ fuseBond @m @1) . rassocMap) $ t
          :: C m ⊗ C m
      paired =
        (id ⊗^ (arr (LinearFunction (coerce :: C m -> DualVector (C m))))) $ peeled
   in getLinearFunction trace (fromTensor -+$=> (swapMap $ paired))

-- | Contract a trivial-only spine (@FilterTrivial@ / coalesced singlets) to 'Unit'.
class CupTrivial (rs :: Rep) where
  cupTrivial :: RepV rs -> RepV Unit

instance CupTrivial '[] where
  cupTrivial RNil = unitFromScalar 0

instance
  ( KnownNat m
  , KnownNat (m * 1)
  , HilbertSpace (C m)
  , InnerSpace (C m)
  , Scalar (C m) ~ Complex Double
  ) =>
  CupTrivial '[ '(0, 'AtomM m)]
  where
  cupTrivial (RCons v RNil) =
    unitFromScalar (cupHomScalarAtomM @m v)

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat (m * 1)
  , HilbertSpace (C m)
  , HilbertSpace (C n)
  , InnerSpace (C m)
  , Scalar (C m) ~ Complex Double
  , m ~ n
  ) =>
  CupTrivial '[ '(0, 'Prod ('AtomM m) ('AtomM n))]
  where
  cupTrivial (RCons t RNil) =
    unitFromScalar (cupHomScalar @m t)

-- | Contract a singlet-root tree spine (@FilterTrivialTrees@) to 'Unit'.
-- Each trivial root carries @C 1@; amplitudes are summed.
class CupTrivialTrees (ts :: TreeRep) where
  cupTrivialTrees :: TreeV ts -> RepV Unit

instance CupTrivialTrees '[] where
  cupTrivialTrees TNil = unitFromScalar 0

instance
  ( CupTrivialTrees rest
  , LinearSpace (C 1)
  , Scalar (C 1) ~ Complex Double
  , InnerSpace (C 1)
  ) =>
  CupTrivialTrees ('Leaf 0 ': rest)
  where
  cupTrivialTrees (TCons v rest) =
    unitFromScalar
      ( (konst 1 <.> v)
          + unitScalar (cupTrivialTrees rest)
      )

instance
  ( CupTrivialTrees rest
  , LinearSpace (C 1)
  , Scalar (C 1) ~ Complex Double
  , InnerSpace (C 1)
  ) =>
  CupTrivialTrees ('Node 0 l r ': rest)
  where
  cupTrivialTrees (TCons v rest) =
    unitFromScalar
      ( (konst 1 <.> v)
          + unitScalar (cupTrivialTrees rest)
      )

-- | Drop non-singlet-root trees (term-level 'FilterTrivialTrees').
class FilterTrivialTreesTerm (ts :: TreeRep) where
  filterTrivialTreesTerm :: TreeV ts -> TreeV (FilterTrivialTrees ts)

instance FilterTrivialTreesTerm '[] where
  filterTrivialTreesTerm TNil = TNil

instance {-# OVERLAPPING #-}
  ( FilterTrivialTreesTerm rest
  , LinearSpace (C 1)
  , Scalar (C 1) ~ Complex Double
  ) =>
  FilterTrivialTreesTerm ('Leaf 0 ': rest)
  where
  filterTrivialTreesTerm (TCons v rest) =
    TCons @('Leaf 0) v (filterTrivialTreesTerm rest)

instance {-# OVERLAPPING #-}
  ( FilterTrivialTreesTerm rest
  , LinearSpace (C 1)
  , Scalar (C 1) ~ Complex Double
  ) =>
  FilterTrivialTreesTerm ('Node 0 l r ': rest)
  where
  filterTrivialTreesTerm (TCons v rest) =
    TCons @('Node 0 l r) v (filterTrivialTreesTerm rest)

instance {-# OVERLAPPABLE #-}
  ( FilterTrivialTreesTerm rest
  , FilterTrivialTrees (t ': rest) ~ FilterTrivialTrees rest
  ) =>
  FilterTrivialTreesTerm (t ': rest)
  where
  filterTrivialTreesTerm (TCons _ rest) = filterTrivialTreesTerm rest

-- | Fused evaluation on singlet trees of @FuseTreeRep a a@ (dual≅primal).
cupFused
  :: forall a
   . ( FilterTrivialTreesTerm (FuseTreeRep a a)
     , CupTrivialTrees (FilterTrivialTrees (FuseTreeRep a a))
     )
  => TreeV (FuseTreeRep a a)
  -> RepV Unit
cupFused = cupTrivialTrees . filterTrivialTreesTerm @(FuseTreeRep a a)

-- | Fused coevaluation: scale the identity singlet(s) of @a@.
capFused
  :: forall a
   . ( KnownHomFused a
     , FilterTrivialTreesTerm (FuseTreeRep a a)
     , KnownTreeRep (FilterTrivialTrees (FuseTreeRep a a))
     , LinearSpace (ToVTreeRep (FilterTrivialTrees (FuseTreeRep a a)))
     , Scalar (ToVTreeRep (FilterTrivialTrees (FuseTreeRep a a))) ~ Complex Double
     )
  => RepV Unit
  -> TreeV (FilterTrivialTrees (FuseTreeRep a a))
capFused u =
  scaleTreeV
    @(FilterTrivialTrees (FuseTreeRep a a))
    (unitScalar u)
    (filterTrivialTreesTerm @(FuseTreeRep a a) (idMorFused @a))

-- | Self-pairing @r ↦ ε(r ⊗ r*)@; wraps 'cupUnfused' into 'RepV Unit'.
cupRdual
  :: forall r
   . ( KnownAtomRep r
     , LinearSpace (ToVSpine r)
     , LinearSpace (DualVector (ToVSpine r))
     , Scalar (ToVSpine r) ~ Complex Double
     , Scalar (DualVector (ToVSpine r)) ~ Complex Double
     , TensorSpace (DualVector (ToVSpine r))
     )
  => RepV r
  -> RepV Unit
cupRdual r =
  vToRepV @Unit (cupUnfused @r (repVToV @r r ⊗ rdual @r r))

--------------------------------------------------------------------------------
-- Unfused composition (compact closed)
--
--   compose f g = unitor ∘ (cup ⊗ id) ∘ assoc ∘ (f ⊗ g)
--
-- Hom elements are Dual-left @Dual r ⊗ q@. Identity is coevaluation
-- braided into Dual-left packing. 'assocCompose' is monoidal @α@ (no F-move).
--------------------------------------------------------------------------------

-- | Unfused morphisms @a → b@: Dual-left packing on tree spaces
-- @Dual(ToVObj a) ⊗ ToVObj b@ (@'Tensor@ = Kronecker).
newtype HomUnfused (a :: Obj Nat) (b :: Obj Nat) = HomUnfused
  { unHomUnfused :: DualVector (ToVObj a) ⊗ ToVObj b }

-- | Fused morphisms @a → b@: genealogy-preserving 'TreeV' of 'FuseTreeRep'
-- (SU(2) dual≅primal; left child plays dual). Compose via 'composeHomTrees'.
newtype HomFused (a :: TreeRep) (b :: TreeRep) = HomFused
  { unHomFused :: TreeV (FuseTreeRep a b) }

-- | Identity: @η@ from 'capUnfused', swapped into Dual-left packing.
idMor
  :: forall a
   . ( KnownAtomRep a
     , LinearSpace (ToVSpine a)
     , LinearSpace (DualVector (ToVSpine a))
     , Scalar (ToVSpine a) ~ Complex Double
     , Scalar (DualVector (ToVSpine a)) ~ Complex Double
     )
  => DualVector (ToVSpine a) ⊗ ToVSpine a
idMor = swapMap $ capUnfused @a (unitToVFromScalar 1)

-- | Fused identity on @FuseTreeRep a a@ (singlet channel = 1).
idMorFused
  :: forall a
   . KnownHomFused a
  => TreeV (FuseTreeRep a a)
idMorFused = idHomFusedVal @a

-- | Step 1: @f ⊗ g@.
tensorCompose
  :: forall a b c
   . ( TensorSpace (DualVector (ToVSpine a) ⊗ ToVSpine b)
     , TensorSpace ((DualVector (ToVSpine b) ⊗ ToVSpine c))
     , Scalar ((DualVector (ToVSpine a) ⊗ ToVSpine b)) ~ Complex Double
     , Scalar ((DualVector (ToVSpine b) ⊗ ToVSpine c)) ~ Complex Double
     )
  => (DualVector (ToVSpine a) ⊗ ToVSpine b)
  -> (DualVector (ToVSpine b) ⊗ ToVSpine c)
  -> (DualVector (ToVSpine a) ⊗ ToVSpine b) ⊗ (DualVector (ToVSpine b) ⊗ ToVSpine c)
tensorCompose = (⊗)

-- | Step 2: reassociate to @Dual a ⊗ ((b ⊗ Dual b) ⊗ c)@ (cup-ready middle).
--
-- Unfused path is plain monoidal @α@ (no SU(2) F-move):
--
-- @
-- (Dual a ⊗ b) ⊗ (Dual b ⊗ c)
--   ─ rassoc ─► Dual a ⊗ (b ⊗ (Dual b ⊗ c))
--   ─ id ⊗ lassoc ─► Dual a ⊗ ((b ⊗ Dual b) ⊗ c)
-- @
assocCompose
  :: forall a b c
   . ( LinearSpace (DualVector (ToVSpine a))
     , LinearSpace (ToVSpine b)
     , LinearSpace (DualVector (ToVSpine b))
     , LinearSpace (ToVSpine c)
     , Scalar (DualVector (ToVSpine a)) ~ Complex Double
     , Scalar (ToVSpine b) ~ Complex Double
     , Scalar (DualVector (ToVSpine b)) ~ Complex Double
     , Scalar (ToVSpine c) ~ Complex Double
     , TensorSpace (DualVector (ToVSpine a))
     , TensorSpace (ToVSpine b)
     , TensorSpace (DualVector (ToVSpine b))
     , TensorSpace (ToVSpine c)
     )
  => (DualVector (ToVSpine a) ⊗ ToVSpine b) ⊗ (DualVector (ToVSpine b) ⊗ ToVSpine c)
  -> DualVector (ToVSpine a) ⊗ ((ToVSpine b ⊗ DualVector (ToVSpine b)) ⊗ ToVSpine c)
assocCompose t =
  (id ⊗^ lassocMap @(ToVSpine b) @(DualVector (ToVSpine b)) @(ToVSpine c))
    $ ( rassocMap
          @(DualVector (ToVSpine a))
          @(ToVSpine b)
          @( DualVector (ToVSpine b)
               ⊗ ToVSpine c
           )
          $ t
      )

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

-- | Step 3: @(cup ⊗ id)@ on the middle @b ⊗ Dual b@.
cupTensorIdCompose
  :: forall a b c
   . ( KnownAtomRep b
     , LinearSpace (ToVSpine b)
     , LinearSpace (DualVector (ToVSpine b))
     , LinearSpace (ToVSpine a)
     , LinearSpace (DualVector (ToVSpine a))
     , LinearSpace (ToVSpine c)
     , Scalar (ToVSpine b) ~ Complex Double
     , Scalar (DualVector (ToVSpine b)) ~ Complex Double
     , Scalar (ToVSpine a) ~ Complex Double
     , Scalar (DualVector (ToVSpine a)) ~ Complex Double
     , Scalar (ToVSpine c) ~ Complex Double
     , TensorSpace (DualVector (ToVSpine a))
     , TensorSpace (ToVSpine c)
     , TensorSpace ((ToVSpine b ⊗ DualVector (ToVSpine b)))
     , TensorSpace (ToVSpine Unit)
     )
  => DualVector (ToVSpine a) ⊗ ((ToVSpine b ⊗ DualVector (ToVSpine b)) ⊗ ToVSpine c)
  -> DualVector (ToVSpine a) ⊗ (ToVSpine Unit ⊗ ToVSpine c)
cupTensorIdCompose t =
  ( id
      ⊗^ ( arr (LinearFunction (cupUnfused @b))
             ⊗^ id
         )
  )
    $ t

-- | Step 4: left unitor on the right factor @Unit ⊗ c → c@.
unitorCompose
  :: forall a c
   . ( LinearSpace (DualVector (ToVSpine a))
     , LinearSpace (ToVSpine c)
     , Scalar (DualVector (ToVSpine a)) ~ Complex Double
     , Scalar (ToVSpine c) ~ Complex Double
     , TensorSpace (DualVector (ToVSpine a))
     , TensorSpace (ToVSpine c)
     )
  => DualVector (ToVSpine a) ⊗ (ToVSpine Unit ⊗ ToVSpine c)
  -> (DualVector (ToVSpine a) ⊗ ToVSpine c)
unitorCompose t =
  (id ⊗^ unitLunit @(ToVSpine c)) $ t

-- | Unfused Hom composition:
-- @unitor ∘ (cup ⊗ id) ∘ assoc ∘ (f ⊗ g)@.
composeMor
  :: forall a b c
   . ( TensorSpace ((DualVector (ToVSpine a) ⊗ ToVSpine b))
     , TensorSpace ((DualVector (ToVSpine b) ⊗ ToVSpine c))
     , Scalar ((DualVector (ToVSpine a) ⊗ ToVSpine b)) ~ Complex Double
     , Scalar ((DualVector (ToVSpine b) ⊗ ToVSpine c)) ~ Complex Double
     , KnownAtomRep b
     , LinearSpace (ToVSpine b)
     , LinearSpace (DualVector (ToVSpine b))
     , LinearSpace (ToVSpine a)
     , LinearSpace (DualVector (ToVSpine a))
     , LinearSpace (ToVSpine c)
     , Scalar (ToVSpine b) ~ Complex Double
     , Scalar (DualVector (ToVSpine b)) ~ Complex Double
     , Scalar (ToVSpine a) ~ Complex Double
     , Scalar (DualVector (ToVSpine a)) ~ Complex Double
     , Scalar (ToVSpine c) ~ Complex Double
     , TensorSpace (DualVector (ToVSpine a))
     , TensorSpace (ToVSpine b)
     , TensorSpace (DualVector (ToVSpine b))
     , TensorSpace (ToVSpine c)
     , TensorSpace ((ToVSpine b ⊗ DualVector (ToVSpine b)))
     , TensorSpace (ToVSpine Unit)
     )
  => (DualVector (ToVSpine a) ⊗ ToVSpine b)
  -> (DualVector (ToVSpine b) ⊗ ToVSpine c)
  -> (DualVector (ToVSpine a) ⊗ ToVSpine c)
composeMor f g =
  unitorCompose @a @c
    ( cupTensorIdCompose @a @b @c
        ( assocCompose @a @b @c
            (tensorCompose @a @b @c f g)
        )
    )

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
class KnownHomFused (a :: TreeRep) where
  idHomFusedVal :: TreeV (FuseTreeRep a a)

-- | Identity endomorphism on a leaf: singlet (@root = 0@) channel = 1, else 0.
idHomLeaf
  :: forall j
   . ( KnownNat j
     , KnownTreeRep (FuseTreeRep '[ 'Leaf j] '[ 'Leaf j])
     )
  => TreeV (FuseTreeRep '[ 'Leaf j] '[ 'Leaf j])
idHomLeaf = go (treeRepSing @(FuseTreeRep '[ 'Leaf j] '[ 'Leaf j]))
  where
    go :: forall ts. STreeRep ts -> TreeV ts
    go STreeNil = TNil
    go (STreeCons (t :: SIrrepTree u) rest) =
      case t of
        SNode @d _l _r ->
          case sameNat (Proxy @d) (Proxy @0) of
            Just Refl -> TCons @u (konst 1) (go rest)
            Nothing -> TCons @u zeroV (go rest)
        SLeaf {} ->
          error "idHomLeaf: expected Hom Node channels"

-- | Any single leaf: identity via 'idHomLeaf'.
instance
  ( KnownNat j
  , KnownTreeRep (FuseTreeRep '[ 'Leaf j] '[ 'Leaf j])
  ) =>
  KnownHomFused '[ 'Leaf j]
  where
  idHomFusedVal = idHomLeaf @j

-- Category \/ monoidal structure: HomUnfused (complete). HomFused Category lives
-- with the tree compose ladder (see 'composeHomFused').

--------------------------------------------------------------------------------
-- Fused associator primitives (3-leaf) and FuseHom-in-one-leg naturality
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

-- | Apply a Symmetry Schur intertwiner on a Symbolic flat buffer.
applySymInterFlat
  :: forall r q
   . ( RepLookup SU2
     , HasHomBlock SU2
     , CollectCompiledGo SU2
     , KnownRep SU2 r
     , KnownRep SU2 q
     , RepListG SU2 r
     , RepListG SU2 q
     , ApplyIntertwinerG SU2 r q
     , KnownNat (RepDimG SU2 r)
     , KnownNat (RepDimG SU2 q)
     )
  => IntertwinerG SU2 r q
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
applySymInterFlat mor vin =
  case getLinearFunction (intertwinerLinearG mor) (ToCG (unsafeFromArray vin)) of
    ToCG out -> toArray out

-- | Unit-multiplicity atom spine @'[ '(j, AtomM 1)]@.
type Atom1 (j :: Nat) = '[ '(j, 'AtomM 1)]

-- | 3-leaf F-move on flattened fused spines (dispatch; atoms via F-symbols).
class CanFmoveSym (a :: Rep) (b :: Rep) (c :: Rep) where
  fmoveSym
    :: ToVSpine (FuseFlat (FuseFlat a b) c)
    -> ToVSpine (FuseFlat a (FuseFlat b c))
  fmoveInvSym
    :: ToVSpine (FuseFlat a (FuseFlat b c))
    -> ToVSpine (FuseFlat (FuseFlat a b) c)

-- | Atom spines: bridge @toArray@ ↔ @fSymbolHomSU2@ flats (Symmetry.Tensor layout).
-- Concrete @2j@ triples so 'StaticDimension' \/ 'ToVSpine' reduce (open FuseFlat
-- nests do not yield 'Dimensional' in a polymorphic @j1,j2,j3@ instance).
instance CanFmoveSym (Atom1 1) (Atom1 1) (Atom1 1) where
  fmoveSym v =
    unsafeFromArray $
      applySymInterFlat
        @(ST.Tensor SU2 (ST.Tensor SU2 '[ '(1, 1)] '[ '(1, 1)]) '[ '(1, 1)])
        @(ST.Tensor SU2 '[ '(1, 1)] (ST.Tensor SU2 '[ '(1, 1)] '[ '(1, 1)]))
        (fSymbolHomSU2 (Proxy @'[ '(1, 1)]) (Proxy @'[ '(1, 1)]) (Proxy @'[ '(1, 1)]))
        (toArray v)
  fmoveInvSym v =
    unsafeFromArray $
      applySymInterFlat
        @(ST.Tensor SU2 '[ '(1, 1)] (ST.Tensor SU2 '[ '(1, 1)] '[ '(1, 1)]))
        @(ST.Tensor SU2 (ST.Tensor SU2 '[ '(1, 1)] '[ '(1, 1)]) '[ '(1, 1)])
        (fSymbolHomSU2Inv (Proxy @'[ '(1, 1)]) (Proxy @'[ '(1, 1)]) (Proxy @'[ '(1, 1)]))
        (toArray v)

-- | Trivial irreps (@j = 0@): F is identity on @C 1@.
instance CanFmoveSym (Atom1 0) (Atom1 0) (Atom1 0) where
  fmoveSym v =
    unsafeFromArray $
      applySymInterFlat
        @(ST.Tensor SU2 (ST.Tensor SU2 '[ '(0, 1)] '[ '(0, 1)]) '[ '(0, 1)])
        @(ST.Tensor SU2 '[ '(0, 1)] (ST.Tensor SU2 '[ '(0, 1)] '[ '(0, 1)]))
        (fSymbolHomSU2 (Proxy @'[ '(0, 1)]) (Proxy @'[ '(0, 1)]) (Proxy @'[ '(0, 1)]))
        (toArray v)
  fmoveInvSym v =
    unsafeFromArray $
      applySymInterFlat
        @(ST.Tensor SU2 '[ '(0, 1)] (ST.Tensor SU2 '[ '(0, 1)] '[ '(0, 1)]))
        @(ST.Tensor SU2 (ST.Tensor SU2 '[ '(0, 1)] '[ '(0, 1)]) '[ '(0, 1)])
        (fSymbolHomSU2Inv (Proxy @'[ '(0, 1)]) (Proxy @'[ '(0, 1)]) (Proxy @'[ '(0, 1)]))
        (toArray v)

-- | 3-leaf F-move (left → right association), matching 'Associative.associate':
-- @FuseFlat(FuseFlat(a,b), c) → FuseFlat(a, FuseFlat(b,c))@.
--
-- Atom spines: Schur F-symbols via 'fSymbolHomSU2' on matching flats.
-- Tree Hom-compose uses genealogy-preserving F ('fmoveTrees' / 'fmoveOuterHom').
fmove
  :: forall a b c
   . CanFmoveSym a b c
  => ToVSpine (FuseFlat (FuseFlat a b) c)
  -> ToVSpine (FuseFlat a (FuseFlat b c))
fmove = fmoveSym @a @b @c

-- | Inverse 3-leaf F-move (right → left), matching 'disassociate':
-- @FuseFlat(a, FuseFlat(b,c)) → FuseFlat(FuseFlat(a,b), c)@.
fmoveInv
  :: forall a b c
   . CanFmoveSym a b c
  => ToVSpine (FuseFlat a (FuseFlat b c))
  -> ToVSpine (FuseFlat (FuseFlat a b) c)
fmoveInv = fmoveInvSym @a @b @c

--------------------------------------------------------------------------------
-- Tree-indexed F-move / bimap / Hom-compose (genealogy-preserving)
--
-- Fused Hom composition (the real fused path):
--   tensorHom → fmoveOuterHom → fmoveInnerHom → cupTensorIdHom → unitorHom
--
-- Domain\/codomain of F are 'FuseAssocL' \/ 'FuseAssocR'. Same-root trees stay
-- distinct list entries, so cup can project on trivial-root middle subtrees.
--------------------------------------------------------------------------------

-- | Concrete @½⊗½⊗½@ association trees (matches 'FuseAssocL' \/ 'FuseAssocR' smokes).
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
-- Tree order follows 'FuseAssocL' (not sorted by @d@): @d=2,e=0@ then @d=0@ then
-- @d=2,e=2@ then @d=4@.
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
-- @FuseAssocL → FuseAssocR@. Outer Hom F (@z = FuseTreeRep b c@) cannot put
-- that type family in an instance head — use 'CanFmoveOuterHom' instead.
class CanFmoveTrees (a :: TreeRep) (b :: TreeRep) (c :: TreeRep) where
  fmoveTrees
    :: TreeV (FuseAssocL a b c)
    -> TreeV (FuseAssocR a b c)
  fmoveInvTrees
    :: TreeV (FuseAssocR a b c)
    -> TreeV (FuseAssocL a b c)

-- | Outer Hom F for leaf objects: @(a⊗b) ⊗ Hom(b,c) → a ⊗ (b ⊗ Hom(b,c))@.
-- Instance head is three leaf spines (no 'FuseTreeRep' in the head).
class CanFmoveOuterHom (a :: TreeRep) (b :: TreeRep) (c :: TreeRep) where
  fmoveOuterHom
    :: TreeV (FuseTreeRep (FuseTreeRep a b) (FuseTreeRep b c))
    -> TreeV (FuseTreeRep a (FuseTreeRep b (FuseTreeRep b c)))
  fmoveInvOuterHom
    :: TreeV (FuseTreeRep a (FuseTreeRep b (FuseTreeRep b c)))
    -> TreeV (FuseTreeRep (FuseTreeRep a b) (FuseTreeRep b c))

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
  :: STreeRep ts
  -> TreeV ts
  -> [(Int, Int, Int, Int, Int, VS.Vector (Complex Double))]
collectAssocLChannel STreeNil TNil = []
collectAssocLChannel (STreeCons t rest) (TCons v rs) =
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
          error "collectAssocLChannel: expected Node intermediate (not FuseAssocL?)"
    SLeaf {} ->
      error "collectAssocLChannel: leaf in association spine (not FuseAssocL?)"

-- | Collect right-assoc channels from @(a_i ⊗ (b_j⊗c_k)_f)_d@.
collectAssocRChannel
  :: STreeRep ts
  -> TreeV ts
  -> [(Int, Int, Int, Int, Int, VS.Vector (Complex Double))]
collectAssocRChannel STreeNil TNil = []
collectAssocRChannel (STreeCons t rest) (TCons v rs) =
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
          error "collectAssocRChannel: expected Node intermediate (not FuseAssocR?)"
    SLeaf {} ->
      error "collectAssocRChannel: leaf in association spine (not FuseAssocR?)"

-- | @(d, mid, ra, rb, rc)@ channel map → AssocL spine.
scatterAssocLChannel
  :: STreeRep ts
  -> Map.Map (Int, Int, Int, Int, Int) (VS.Vector (Complex Double))
  -> TreeV ts
scatterAssocLChannel STreeNil _ = TNil
scatterAssocLChannel (STreeCons (t :: SIrrepTree u) rest) m =
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
           in TCons @u
                (unsafeFromArray (Map.findWithDefault (zeroLike5 key m) key m))
                (scatterAssocLChannel rest m)
        SLeaf {} ->
          error "scatterAssocLChannel: expected Node intermediate"
    SLeaf {} ->
      error "scatterAssocLChannel: leaf in association spine"

scatterAssocRChannel
  :: STreeRep ts
  -> Map.Map (Int, Int, Int, Int, Int) (VS.Vector (Complex Double))
  -> TreeV ts
scatterAssocRChannel STreeNil _ = TNil
scatterAssocRChannel (STreeCons (t :: SIrrepTree u) rest) m =
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
           in TCons @u
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

-- | Legacy @(d,e)@ collect — leaf triples only (unique mid roots).
collectAssocL
  :: STreeRep ts
  -> TreeV ts
  -> [(Int, Int, VS.Vector (Complex Double))]
collectAssocL s tv =
  [(d, e, v) | (d, e, _ra, _rb, _rc, v) <- collectAssocLChannel s tv]

collectAssocR
  :: STreeRep ts
  -> TreeV ts
  -> [(Int, Int, VS.Vector (Complex Double))]
collectAssocR s tv =
  [(d, f, v) | (d, f, _ra, _rb, _rc, v) <- collectAssocRChannel s tv]

scatterAssocL
  :: STreeRep ts
  -> Map.Map (Int, Int) (VS.Vector (Complex Double))
  -> TreeV ts
scatterAssocL STreeNil _ = TNil
scatterAssocL (STreeCons (t :: SIrrepTree u) rest) m =
  case t of
    SNode @d left _ ->
      let key = (fromIntegral (natVal (Proxy @d)), rootLab left)
       in TCons @u
            (unsafeFromArray (m Map.! key))
            (scatterAssocL rest m)
    SLeaf {} ->
      error "scatterAssocL: leaf in association spine (not FuseAssocL?)"

scatterAssocR
  :: STreeRep ts
  -> Map.Map (Int, Int) (VS.Vector (Complex Double))
  -> TreeV ts
scatterAssocR STreeNil _ = TNil
scatterAssocR (STreeCons (t :: SIrrepTree u) rest) m =
  case t of
    SNode @d _ right ->
      let key = (fromIntegral (natVal (Proxy @d)), rootLab right)
       in TCons @u
            (unsafeFromArray (m Map.! key))
            (scatterAssocR rest m)
    SLeaf {} ->
      error "scatterAssocR: leaf in association spine (not FuseAssocR?)"

-- | 3-factor F-move: @FuseAssocL a b c → FuseAssocR a b c@.
--
-- 'FuseTreeRep' distributes into channels @((a_i⊗b_j)_e ⊗ c_k)_d@. For each
-- distinct root triple @(r(a_i),r(b_j),r(c_k))@ apply dense Racah
-- @F^{ra rb rc}@, keeping genealogy in the channel key.
fmoveTreesAtoms
  :: forall a b c
   . ( KnownTreeRep (FuseAssocL a b c)
     , KnownTreeRep (FuseAssocR a b c)
     )
  => TreeV (FuseAssocL a b c)
  -> TreeV (FuseAssocR a b c)
fmoveTreesAtoms tv =
  let chans = collectAssocLChannel (treeRepSing @(FuseAssocL a b c)) tv
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
        (treeRepSing @(FuseAssocR a b c))
        (Map.fromList [((d, f, ra, rb, rc), v) | (d, f, ra, rb, rc, v) <- out])

fmoveInvTreesAtoms
  :: forall a b c
   . ( KnownTreeRep (FuseAssocL a b c)
     , KnownTreeRep (FuseAssocR a b c)
     )
  => TreeV (FuseAssocR a b c)
  -> TreeV (FuseAssocL a b c)
fmoveInvTreesAtoms tv =
  let chans = collectAssocRChannel (treeRepSing @(FuseAssocR a b c)) tv
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
        (treeRepSing @(FuseAssocL a b c))
        (Map.fromList [((d, e, ra, rb, rc), v) | (d, e, ra, rb, rc, v) <- out])

-- | Atom-leaf triple F-move from type-level @2j@.
fmoveTreesLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownTreeRep (FuseAssocL '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
     , KnownTreeRep (FuseAssocR '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
     )
  => TreeV (FuseAssocL '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
  -> TreeV (FuseAssocR '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
fmoveTreesLeaves =
  fmoveTreesAtoms @('[ 'Leaf ja]) @('[ 'Leaf jb]) @('[ 'Leaf jc])

fmoveInvTreesLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownTreeRep (FuseAssocL '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
     , KnownTreeRep (FuseAssocR '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
     )
  => TreeV (FuseAssocR '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
  -> TreeV (FuseAssocL '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
fmoveInvTreesLeaves =
  fmoveInvTreesAtoms @('[ 'Leaf ja]) @('[ 'Leaf jb]) @('[ 'Leaf jc])

-- | Outer Hom F for three leaf labels (Hom = 'FuseTreeRep' of the last two).
fmoveOuterHomLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownTreeRep
         ( FuseAssocL
             '[ 'Leaf ja]
             '[ 'Leaf jb]
             (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
         )
     , KnownTreeRep
         ( FuseAssocR
             '[ 'Leaf ja]
             '[ 'Leaf jb]
             (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
         )
     )
  => TreeV
       ( FuseTreeRep
           (FuseTreeRep '[ 'Leaf ja] '[ 'Leaf jb])
           (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
       )
  -> TreeV
       ( FuseTreeRep
           '[ 'Leaf ja]
           (FuseTreeRep '[ 'Leaf jb] (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc]))
       )
fmoveOuterHomLeaves =
  fmoveOuterLeafHom @ja @jb
    @( FuseAssocL
         '[ 'Leaf ja]
         '[ 'Leaf jb]
         (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
     )
    @( FuseAssocR
         '[ 'Leaf ja]
         '[ 'Leaf jb]
         (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
     )

fmoveInvOuterHomLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownTreeRep
         ( FuseAssocL
             '[ 'Leaf ja]
             '[ 'Leaf jb]
             (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
         )
     , KnownTreeRep
         ( FuseAssocR
             '[ 'Leaf ja]
             '[ 'Leaf jb]
             (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
         )
     )
  => TreeV
       ( FuseTreeRep
           '[ 'Leaf ja]
           (FuseTreeRep '[ 'Leaf jb] (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc]))
       )
  -> TreeV
       ( FuseTreeRep
           (FuseTreeRep '[ 'Leaf ja] '[ 'Leaf jb])
           (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
       )
fmoveInvOuterHomLeaves =
  fmoveInvOuterLeafHom @ja @jb
    @( FuseAssocR
         '[ 'Leaf ja]
         '[ 'Leaf jb]
         (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
     )
    @( FuseAssocL
         '[ 'Leaf ja]
         '[ 'Leaf jb]
         (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
     )

-- | Standard basis vector of @C n@.
cnBasis :: forall n. KnownNat n => Int -> C n
cnBasis i =
  let n = fromIntegral (natVal (Proxy @n)) :: Int
   in unsafeFromArray $
        VS.generate n $ \j -> if j == i then 1 :+ 0 else 0

-- | Standard basis vector of @C 2@.
c2Basis :: Int -> C 2
c2Basis = cnBasis @2

c1Basis :: C 1
c1Basis = cnBasis @1 0

-- | Multiplicity matrix @[F^{abc}_d]@ (or @F⁻¹ ≈ Fᵀ@ for real SU(2)) as @C n +> C n@.
--
-- @dom@ \/ @cod@ are intermediate @2j@ labels in basis order (@allowedE@ →
-- @allowedF@ for forward; swapped for inverse). Forward:
-- @{cod}_j = Σ_i F_{dom_i,cod_j} in_i@. Inverse uses the transpose in the
-- same @(e,f)@ matrix (@F_{cod_j,dom_i}@) — required when @allowedE@ and
-- @allowedF@ are different label sets (e.g. @½⊗½⊗0@).
fmoveMult
  :: forall n
   . ( KnownNat n
     , HilbertSpace (C n)
     , InnerSpace (C n)
     , Scalar (C n) ~ Complex Double
     , AdditiveGroup (C n)
     )
  => Bool
  -> Int
  -> Int
  -> Int
  -> Int
  -> [Int]
  -> [Int]
  -> C n +> C n
fmoveMult inv a b c d dom cod =
  arr $ LinearFunction $ \v ->
    let n = fromIntegral (natVal (Proxy @n)) :: Int
        coeffs = [ cnBasis @n i <.> v | i <- [0 .. n - 1] ]
        amp i j =
          if inv
            then fMultEntry a b c d (cod !! j) (dom !! i)
            else fMultEntry a b c d (dom !! i) (cod !! j)
        outAt j =
          sum
            [ amp i j * (coeffs !! i)
            | i <- [0 .. n - 1]
            ]
     in sumV
          [ outAt j *^ cnBasis @n j
          | j <- [0 .. n - 1]
          ]

-- | @F^{abc}_d ⊗ id@ (or inverse) on @C n ⊗ C (IrrepDim d)@.
-- @n@ must equal @length (allowedE a b c d)@ (= @length (allowedF …)@).
fmoveSector
  :: forall n d
   . ( KnownNat n
     , KnownNat d
     , KnownNat (IrrepDim d)
     , HilbertSpace (C n)
     , InnerSpace (C n)
     , Scalar (C n) ~ Complex Double
     , AdditiveGroup (C n)
     , TensorSpace (C (IrrepDim d))
     , LSpace (C n)
     , LSpace (C (IrrepDim d))
     )
  => Bool
  -> Int
  -> Int
  -> Int
  -> (C n ⊗ C (IrrepDim d)) +> (C n ⊗ C (IrrepDim d))
fmoveSector inv a b c =
  let d = fromIntegral (natVal (Proxy @d)) :: Int
      es = allowedE a b c d
      fs = allowedF a b c d
      (dom, cod) = if inv then (fs, es) else (es, fs)
   in fmoveMult @n inv a b c d dom cod ⊗^ id

-- | F-blocked layout for @½⊗½⊗½@: group by @(a,b,c,d)=(1,1,1,d)@.
type Flat111 = (C 2 ⊗ C 2, C 1 ⊗ C 4)

-- | Pack two equal irrep vectors into mult⊗irrep (@C 2 ⊗ C d@).
packTwoCopy
  :: forall d
   . ( KnownNat d
     , AdditiveGroup (C 2 ⊗ C d)
     , TensorSpace (C d)
     , TensorSpace (C 2)
     )
  => C d
  -> C d
  -> C 2 ⊗ C d
packTwoCopy v0 v2 =
  (c2Basis 0 ⊗ v0) ^+^ (c2Basis 1 ⊗ v2)

-- | Unpack multiplicity-2 @C 2 ⊗ C d@ via Kronecker 'fuseBond' layout
-- (left-leg slices). Scalar-leg @ℂ ⊗ -@ contraction via @(<.>) ⊗ id@ hits a
-- broken @toFlatTensor@ path in the hmatrix backend, so stay on array slices.
unpackTwoCopy
  :: forall d
   . ( KnownNat d
     , KnownNat (2 * d)
     , TensorSpace (C d)
     )
  => C 2 ⊗ C d
  -> (C d, C d)
unpackTwoCopy sec =
  let buf = toArray (fuseBond @2 @d $ sec)
      di = fromIntegral (natVal (Proxy @d)) :: Int
   in ( unsafeFromArray (VS.take di buf)
      , unsafeFromArray (VS.drop di buf)
      )

packFlat111 :: (C 2, (C 2, C 4)) -> Flat111
packFlat111 (v0, (v2, v3)) =
  (packTwoCopy @2 v0 v2, c1Basis ⊗ v3)

unpackFlat111 :: Flat111 -> (C 2, (C 2, C 4))
unpackFlat111 (sec1, sec3) =
  case unpackTwoCopy @2 sec1 of
    (v0, v2) -> (v0, (v2, fuseBond @1 @4 $ sec3))

-- | @½⊗½⊗½@ F-move via polymorphic 'fmoveSector' (@F ⊗ id@ per total @d@).
fmoveFlat111 :: Flat111 -> Flat111
fmoveFlat111 (sec1, sec3) =
  ( fmoveSector @2 @1 False 1 1 1 $ sec1
  , fmoveSector @1 @3 False 1 1 1 $ sec3
  )

fmoveInvFlat111 :: Flat111 -> Flat111
fmoveInvFlat111 (sec1, sec3) =
  ( fmoveSector @2 @1 True 1 1 1 $ sec1
  , fmoveSector @1 @3 True 1 1 1 $ sec3
  )

-- | F-blocked @½⊗½⊗0@: @d=0@ (@C 1⊗C 1@) and @d=2@ (@C 1⊗C 3@).
type Flat110 = (C 1 ⊗ C 1, C 1 ⊗ C 3)

packFlat110 :: (C 1, C 3) -> Flat110
packFlat110 (v0, v2) = (c1Basis ⊗ v0, c1Basis ⊗ v2)

unpackFlat110 :: Flat110 -> (C 1, C 3)
unpackFlat110 (sec0, sec2) =
  (fuseBond @1 @1 $ sec0, fuseBond @1 @3 $ sec2)

fmoveFlat110 :: Flat110 -> Flat110
fmoveFlat110 (sec0, sec2) =
  ( fmoveSector @1 @0 False 1 1 0 $ sec0
  , fmoveSector @1 @2 False 1 1 0 $ sec2
  )

fmoveInvFlat110 :: Flat110 -> Flat110
fmoveInvFlat110 (sec0, sec2) =
  ( fmoveSector @1 @0 True 1 1 0 $ sec0
  , fmoveSector @1 @2 True 1 1 0 $ sec2
  )

-- | F-blocked @½⊗½⊗1@: @d=0,2,4@ with mult-2 on @d=2@.
type Flat112 = (C 1 ⊗ C 1, (C 2 ⊗ C 3, C 1 ⊗ C 5))

-- | Left-assoc tree payload ↔ F-blocks (regroup by @d@).
packFlat112L :: (C 3, (C 1, (C 3, C 5))) -> Flat112
packFlat112L (v2e0, (v0, (v2e2, v4))) =
  (c1Basis ⊗ v0, (packTwoCopy @3 v2e0 v2e2, c1Basis ⊗ v4))

unpackFlat112L :: Flat112 -> (C 3, (C 1, (C 3, C 5)))
unpackFlat112L (sec0, (sec2, sec4)) =
  case unpackTwoCopy @3 sec2 of
    (v2e0, v2e2) ->
      (v2e0, (fuseBond @1 @1 $ sec0, (v2e2, fuseBond @1 @5 $ sec4)))

-- | Right-assoc tree payload ↔ F-blocks (same sectors, 'FuseAssocR' order).
packFlat112R :: (C 1, (C 3, (C 3, C 5))) -> Flat112
packFlat112R (v0, (v2f1, (v2f3, v4))) =
  (c1Basis ⊗ v0, (packTwoCopy @3 v2f1 v2f3, c1Basis ⊗ v4))

unpackFlat112R :: Flat112 -> (C 1, (C 3, (C 3, C 5)))
unpackFlat112R (sec0, (sec2, sec4)) =
  case unpackTwoCopy @3 sec2 of
    (v2f1, v2f3) ->
      (fuseBond @1 @1 $ sec0, (v2f1, (v2f3, fuseBond @1 @5 $ sec4)))

fmoveFlat112 :: Flat112 -> Flat112
fmoveFlat112 (sec0, (sec2, sec4)) =
  ( fmoveSector @1 @0 False 1 1 2 $ sec0
  , ( fmoveSector @2 @2 False 1 1 2 $ sec2
    , fmoveSector @1 @4 False 1 1 2 $ sec4
    )
  )

fmoveInvFlat112 :: Flat112 -> Flat112
fmoveInvFlat112 (sec0, (sec2, sec4)) =
  ( fmoveSector @1 @0 True 1 1 2 $ sec0
  , ( fmoveSector @2 @2 True 1 1 2 $ sec2
    , fmoveSector @1 @4 True 1 1 2 $ sec4
    )
  )

-- | Triple-leaf F-move via label-driven 'fmoveTreesLeaves'.
fmoveTrees111 :: TreeV AssocL111 -> TreeV AssocR111
fmoveTrees111 = fmoveTreesLeaves @1 @1 @1

fmoveInvTrees111 :: TreeV AssocR111 -> TreeV AssocL111
fmoveInvTrees111 = fmoveInvTreesLeaves @1 @1 @1

fmoveTrees000 :: TreeV AssocL000 -> TreeV AssocR000
fmoveTrees000 = fmoveTreesLeaves @0 @0 @0

fmoveInvTrees000 :: TreeV AssocR000 -> TreeV AssocL000
fmoveInvTrees000 = fmoveInvTreesLeaves @0 @0 @0

fmoveTrees110 :: TreeV AssocL110 -> TreeV AssocR110
fmoveTrees110 = fmoveTreesLeaves @1 @1 @0

fmoveInvTrees110 :: TreeV AssocR110 -> TreeV AssocL110
fmoveInvTrees110 = fmoveInvTreesLeaves @1 @1 @0

fmoveTrees112 :: TreeV AssocL112 -> TreeV AssocR112
fmoveTrees112 = fmoveTreesLeaves @1 @1 @2

fmoveInvTrees112 :: TreeV AssocR112 -> TreeV AssocL112
fmoveInvTrees112 = fmoveInvTreesLeaves @1 @1 @2

-- | Any three atom leaves: F via 'fmoveTreesLeaves' (no per-triple FlatXXX).
instance
  ( KnownNat ja
  , KnownNat jb
  , KnownNat jc
  , KnownTreeRep (FuseAssocL '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
  , KnownTreeRep (FuseAssocR '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
  ) =>
  CanFmoveTrees '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc]
  where
  fmoveTrees = fmoveTreesLeaves @ja @jb @jc
  fmoveInvTrees = fmoveInvTreesLeaves @ja @jb @jc

-- | Nested unfused @a ⊗ q@ before CG (layout for Fuse-right naturality).
data TensorTrees (a :: TreeRep) (q :: TreeRep) where
  TensorTrees :: TreeV a -> TreeV q -> TensorTrees a q

mapTensorTreesRight
  :: (TreeV q -> TreeV q')
  -> TensorTrees a q
  -> TensorTrees a q'
mapTensorTreesRight f (TensorTrees a q) = TensorTrees a (f q)

fuseTensorTrees
  :: forall a q
   . ( KnownTreeRep a
     , KnownTreeRep q
     , FuseTreeRepTermC a q
     )
  => TensorTrees a q
  -> TreeV (FuseTreeRep a q)
fuseTensorTrees (TensorTrees a q) = fuseTreeRepTerm @a @q a q

--------------------------------------------------------------------------------
-- Leaf object / Hom aliases (thin names over 'FuseTreeRep' / 'FuseAssoc')
--------------------------------------------------------------------------------

type Leaf1 = '[ 'Leaf 1]

type Leaf0 = '[ 'Leaf 0]

type Leaf2 = '[ 'Leaf 2]

type Leaf3 = '[ 'Leaf 3]

-- | Endomorphism Hom on a leaf: @FuseTreeRep a a@.
type Hom00 = FuseTreeRep Leaf0 Leaf0

type Hom11 = FuseTreeRep Leaf1 Leaf1

type Hom22 = FuseTreeRep Leaf2 Leaf2

type Hom33 = FuseTreeRep Leaf3 Leaf3

-- | Unequal-leaf Homs (for @½ → 1 → ½@ compose smoke).
type Hom12 = FuseTreeRep Leaf1 Leaf2

type Hom21 = FuseTreeRep Leaf2 Leaf1

-- | Leaf outer Hom F: any three leaf labels (Hom = 'FuseTreeRep' of last two).
instance
  ( KnownNat ja
  , KnownNat jb
  , KnownNat jc
  , KnownTreeRep
      ( FuseAssocL
          '[ 'Leaf ja]
          '[ 'Leaf jb]
          (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
      )
  , KnownTreeRep
      ( FuseAssocR
          '[ 'Leaf ja]
          '[ 'Leaf jb]
          (FuseTreeRep '[ 'Leaf jb] '[ 'Leaf jc])
      )
  ) =>
  CanFmoveOuterHom '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc]
  where
  fmoveOuterHom = fmoveOuterHomLeaves @ja @jb @jc
  fmoveInvOuterHom = fmoveInvOuterHomLeaves @ja @jb @jc

-- | Hom-left nested F: left factor @FuseTreeRep '[Leaf ja] '[Leaf ja]@.
-- Nat-indexed so 'FuseTreeRep' never appears in an instance head.
class CanFmoveHomLeft (ja :: Nat) (jb :: Nat) (jc :: Nat) where
  fmoveTreesHomLeft
    :: TreeV
         ( FuseAssocL
             (FuseTreeRep '[ 'Leaf ja] '[ 'Leaf ja])
             '[ 'Leaf jb]
             '[ 'Leaf jc]
         )
    -> TreeV
         ( FuseAssocR
             (FuseTreeRep '[ 'Leaf ja] '[ 'Leaf ja])
             '[ 'Leaf jb]
             '[ 'Leaf jc]
         )
  fmoveInvTreesHomLeft
    :: TreeV
         ( FuseAssocR
             (FuseTreeRep '[ 'Leaf ja] '[ 'Leaf ja])
             '[ 'Leaf jb]
             '[ 'Leaf jc]
         )
    -> TreeV
         ( FuseAssocL
             (FuseTreeRep '[ 'Leaf ja] '[ 'Leaf ja])
             '[ 'Leaf jb]
             '[ 'Leaf jc]
         )

instance
  ( KnownNat ja
  , KnownNat jb
  , KnownNat jc
  , KnownTreeRep
      ( FuseAssocL
          (FuseTreeRep '[ 'Leaf ja] '[ 'Leaf ja])
          '[ 'Leaf jb]
          '[ 'Leaf jc]
      )
  , KnownTreeRep
      ( FuseAssocR
          (FuseTreeRep '[ 'Leaf ja] '[ 'Leaf ja])
          '[ 'Leaf jb]
          '[ 'Leaf jc]
      )
  ) =>
  CanFmoveHomLeft ja jb jc
  where
  fmoveTreesHomLeft =
    fmoveTreesAtoms
      @(FuseTreeRep '[ 'Leaf ja] '[ 'Leaf ja])
      @('[ 'Leaf jb])
      @('[ 'Leaf jc])
  fmoveInvTreesHomLeft =
    fmoveInvTreesAtoms
      @(FuseTreeRep '[ 'Leaf ja] '[ 'Leaf ja])
      @('[ 'Leaf jb])
      @('[ 'Leaf jc])

-- | Fill a spine with scaled ones (deterministic nested-F sample).
fillTreeVScaled
  :: forall ts
   . KnownTreeRep ts
  => TreeV ts
fillTreeVScaled = go 0 (treeRepSing @ts)
  where
    go :: Int -> STreeRep ts' -> TreeV ts'
    go _ STreeNil = TNil
    go i (STreeCons t rest) =
      case t of
        SLeaf {} ->
          TCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)
        SNode {} ->
          TCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)

-- | @(Hom ⊗ Hom)@ left-assoc / right-assoc spines for leaf-½ (Mac Lane outer F).
type Dom111 = FuseAssocL Leaf1 Leaf1 Hom11

type Mid111 = FuseAssocR Leaf1 Leaf1 Hom11

type CupR111 = FuseTreeRep Leaf1 AssocL111

type Dom000 = FuseAssocL Leaf0 Leaf0 Hom00

type CupR000 = FuseTreeRep Leaf0 (FuseTreeRep Hom00 Leaf0)

-- | @Fuse(id, F-inv)@ on Mid — instance of 'fuseMapRight'.
fuseMapRightFinv111 :: TreeV Mid111 -> TreeV CupR111
fuseMapRightFinv111 =
  fuseMapRight @Leaf1 @AssocR111 @AssocL111 fmoveInvTrees111

approxAssoc111
  :: (C 2, (C 2, C 4))
  -> (C 2, (C 2, C 4))
  -> Bool
approxAssoc111 (u0, (u2, u3)) (v0, (v2, v3)) =
  let close a b =
        let d = a ^-^ b
         in magnitude (d <.> d) < 1e-18
   in close u0 v0 && close u2 v2 && close u3 v3

checkFmoveTrees111 :: TreeV AssocL111 -> Bool
checkFmoveTrees111 tv =
  let packed = packFlat111 (treeVToV @AssocL111 tv)
      viaFlat = unpackFlat111 (fmoveFlat111 packed)
      viaTrees = treeVToV @AssocR111 (fmoveTrees111 tv)
      roundtrip =
        treeVToV @AssocL111 (fmoveInvTrees111 (fmoveTrees111 tv))
   in approxAssoc111 viaFlat viaTrees
        && approxAssoc111 (treeVToV @AssocL111 tv) roundtrip

approxAssoc110 :: (C 1, C 3) -> (C 1, C 3) -> Bool
approxAssoc110 (u0, u2) (v0, v2) =
  let close a b =
        let d = a ^-^ b
         in magnitude (d <.> d) < 1e-18
   in close u0 v0 && close u2 v2

checkFmoveTrees110 :: TreeV AssocL110 -> Bool
checkFmoveTrees110 tv =
  let packed = packFlat110 (treeVToV @AssocL110 tv)
      viaFlat = unpackFlat110 (fmoveFlat110 packed)
      viaTrees = treeVToV @AssocR110 (fmoveTrees110 tv)
      roundtrip =
        treeVToV @AssocL110 (fmoveInvTrees110 (fmoveTrees110 tv))
   in approxAssoc110 viaFlat viaTrees
        && approxAssoc110 (treeVToV @AssocL110 tv) roundtrip

approxAssoc112L
  :: (C 3, (C 1, (C 3, C 5)))
  -> (C 3, (C 1, (C 3, C 5)))
  -> Bool
approxAssoc112L (u2e0, (u0, (u2e2, u4))) (v2e0, (v0, (v2e2, v4))) =
  let close a b =
        let d = a ^-^ b
         in magnitude (d <.> d) < 1e-18
   in close u2e0 v2e0 && close u0 v0 && close u2e2 v2e2 && close u4 v4

approxAssoc112R
  :: (C 1, (C 3, (C 3, C 5)))
  -> (C 1, (C 3, (C 3, C 5)))
  -> Bool
approxAssoc112R (u0, (u2f1, (u2f3, u4))) (v0, (v2f1, (v2f3, v4))) =
  let close a b =
        let d = a ^-^ b
         in magnitude (d <.> d) < 1e-18
   in close u0 v0 && close u2f1 v2f1 && close u2f3 v2f3 && close u4 v4

checkFmoveTrees112 :: TreeV AssocL112 -> Bool
checkFmoveTrees112 tv =
  let packed = packFlat112L (treeVToV @AssocL112 tv)
      viaFlat = unpackFlat112R (fmoveFlat112 packed)
      viaTrees = treeVToV @AssocR112 (fmoveTrees112 tv)
      roundtrip =
        treeVToV @AssocL112 (fmoveInvTrees112 (fmoveTrees112 tv))
   in approxAssoc112R viaFlat viaTrees
        && approxAssoc112L (treeVToV @AssocL112 tv) roundtrip

approxTreeV
  :: forall ts
   . KnownTreeRep ts
  => TreeV ts
  -> TreeV ts
  -> Bool
approxTreeV = go (treeRepSing @ts)
  where
    closeVec a b =
      let da = toArray a
          db = toArray b
       in VS.all (\z -> magnitude z < 1e-9) (VS.zipWith (-) da db)
    go :: STreeRep ts' -> TreeV ts' -> TreeV ts' -> Bool
    go STreeNil TNil TNil = True
    go (STreeCons t rest) (TCons a as) (TCons b bs) =
      case t of
        SLeaf {} -> closeVec a b && go rest as bs
        SNode {} -> closeVec a b && go rest as bs
    go _ _ _ = False

-- | Round-trip only (no typed Flat): works for any atom-leaf triple.
checkFmoveTreesLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownTreeRep (FuseAssocL '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
     , KnownTreeRep (FuseAssocR '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
     )
  => TreeV (FuseAssocL '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
  -> Bool
checkFmoveTreesLeaves tv =
  let rt = fmoveInvTreesLeaves @ja @jb @jc (fmoveTreesLeaves @ja @jb @jc tv)
   in approxTreeV
        @(FuseAssocL '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
        tv
        rt

-- | Deterministic sample on left-assoc atom spine (sector flats → scatter).
sampleAssocLLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownTreeRep (FuseAssocL '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
     )
  => TreeV (FuseAssocL '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc])
sampleAssocLLeaves =
  let a = fromIntegral (natVal (Proxy @ja)) :: Int
      b = fromIntegral (natVal (Proxy @jb)) :: Int
      c = fromIntegral (natVal (Proxy @jc)) :: Int
      chans =
        [ ( d
          , e
          , VS.replicate
              (d + 1)
              ((0.1 * fromIntegral (d + e + 1)) :+ 0)
          )
        | (d, _, _) <- leftSectors a b c
        , e <- allowedE a b c d
        ]
   in scatterAssocL
        (treeRepSing @(FuseAssocL '[ 'Leaf ja] '[ 'Leaf jb] '[ 'Leaf jc]))
        (Map.fromList [((d, e), v) | (d, e, v) <- chans])

-- | Collect left-assoc Hom channels @(d, e, h, irrep)@ from
-- @((a⊗b)_e ⊗ Hom_h)_d@. Key includes Hom root @h@ so F cannot reshuffle
-- distinct Hom genealogies that share the same outer root.
collectAssocLHom
  :: STreeRep ts
  -> TreeV ts
  -> [(Int, Int, Int, VS.Vector (Complex Double))]
collectAssocLHom STreeNil TNil = []
collectAssocLHom (STreeCons t rest) (TCons v rs) =
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
  :: STreeRep ts
  -> TreeV ts
  -> [(Int, Int, Int, VS.Vector (Complex Double))]
collectAssocRHom STreeNil TNil = []
collectAssocRHom (STreeCons t rest) (TCons v rs) =
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
  :: STreeRep ts
  -> Map.Map (Int, Int, Int) (VS.Vector (Complex Double))
  -> TreeV ts
scatterAssocLHom STreeNil _ = TNil
scatterAssocLHom (STreeCons (t :: SIrrepTree u) rest) m =
  case t of
    SNode @d left right ->
      let key =
            ( fromIntegral (natVal (Proxy @d))
            , rootLab left
            , rootLab right
            )
       in TCons @u
            (unsafeFromArray (Map.findWithDefault (zeroLike key m) key m))
            (scatterAssocLHom rest m)
    SLeaf {} ->
      error "scatterAssocLHom: leaf in association spine"

scatterAssocRHom
  :: STreeRep ts
  -> Map.Map (Int, Int, Int) (VS.Vector (Complex Double))
  -> TreeV ts
scatterAssocRHom STreeNil _ = TNil
scatterAssocRHom (STreeCons (t :: SIrrepTree u) rest) m =
  case t of
    SNode @d _left right ->
      case right of
        SNode @_ _ midHom ->
          let key =
                ( fromIntegral (natVal (Proxy @d))
                , rootLab right
                , rootLab midHom
                )
           in TCons @u
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
     , KnownTreeRep ls
     , KnownTreeRep rs
     )
  => TreeV ls
  -> TreeV rs
fmoveOuterLeafHom tv =
  let a = fromIntegral (natVal (Proxy @ja)) :: Int
      b = fromIntegral (natVal (Proxy @jb)) :: Int
      chans = collectAssocLHom (treeRepSing @ls) tv
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
        (treeRepSing @rs)
        (Map.fromList [((d, f, h), v) | (d, f, h, v) <- out])

fmoveInvOuterLeafHom
  :: forall ja jb rs ls
   . ( KnownNat ja
     , KnownNat jb
     , KnownTreeRep rs
     , KnownTreeRep ls
     )
  => TreeV rs
  -> TreeV ls
fmoveInvOuterLeafHom tv =
  let a = fromIntegral (natVal (Proxy @ja)) :: Int
      b = fromIntegral (natVal (Proxy @jb)) :: Int
      chans = collectAssocRHom (treeRepSing @rs) tv
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
        (treeRepSing @ls)
        (Map.fromList [((d, e, h), v) | (d, e, h, v) <- out])

-- | Outer Hom F for Leaf-½ (via 'fmoveOuterHom').
fmoveOuter111 :: TreeV Dom111 -> TreeV Mid111
fmoveOuter111 = fmoveOuterHom @Leaf1 @Leaf1 @Leaf1

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

scaleTreeV
  :: forall ts
   . KnownTreeRep ts
  => Complex Double
  -> TreeV ts
  -> TreeV ts
scaleTreeV s = go (treeRepSing @ts)
  where
    go :: STreeRep ts' -> TreeV ts' -> TreeV ts'
    go STreeNil TNil = TNil
    go (STreeCons t rest) (TCons v rs) =
      case t of
        SLeaf {} -> TCons (s *^ v) (go rest rs)
        SNode {} -> TCons (s *^ v) (go rest rs)

idHom00 :: TreeV Hom00
idHom00 = idHomLeaf @0

-- | Singlet-only identity in 'Hom11' (@j=0@ channel).
idHom11 :: TreeV Hom11
idHom11 = idHomLeaf @1

-- | Singlet-only identity in 'Hom22'.
idHom22 :: TreeV Hom22
idHom22 = idHomLeaf @2

-- | Singlet-only identity in 'Hom33' (@tj = 3@).
idHom33 :: TreeV Hom33
idHom33 = idHomLeaf @3

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
   . ( KnownTreeRep (FuseTreeRep a b)
     , KnownTreeRep (FuseTreeRep b c)
     , FuseTreeRepTermC (FuseTreeRep a b) (FuseTreeRep b c)
     )
  => TreeV (FuseTreeRep a b)
  -> TreeV (FuseTreeRep b c)
  -> TreeV (FuseTreeRep (FuseTreeRep a b) (FuseTreeRep b c))
tensorHom = fuseTreeRepTerm @(FuseTreeRep a b) @(FuseTreeRep b c)

-- | Step 2: outer F — @(a*⊗b) ⊗ (b*⊗c) → a* ⊗ (b ⊗ (b*⊗c))@.
--
-- Discharged by 'CanFmoveOuterHom' (leaf instance → 'fmoveOuterHomLeaves').
-- ('fmoveInnerHom' is the subsequent @id ⊗ F@ via 'fuseMapRight' 'fmoveInvTrees'.)

-- | Step 3: @id ⊗ F@ — @a* ⊗ (b ⊗ (b*⊗c)) → a* ⊗ ((b ⊗ b*) ⊗ c)@.
--
-- Right factor: @FuseAssocR b b c → FuseAssocL b b c@ via 'fmoveInvTrees'.
fmoveInnerHom
  :: forall a b c
   . ( KnownTreeRep a
     , KnownTreeRep (FuseTreeRep b (FuseTreeRep b c))
     , KnownTreeRep (FuseTreeRep (FuseTreeRep b b) c)
     , KnownTreeRep (FuseTreeRep a (FuseTreeRep b (FuseTreeRep b c)))
     , KnownTreeRep (FuseTreeRep a (FuseTreeRep (FuseTreeRep b b) c))
     , CanFmoveTrees b b c
     )
  => TreeV (FuseTreeRep a (FuseTreeRep b (FuseTreeRep b c)))
  -> TreeV (FuseTreeRep a (FuseTreeRep (FuseTreeRep b b) c))
fmoveInnerHom =
  fuseMapRight
    @a
    @(FuseTreeRep b (FuseTreeRep b c))
    @(FuseTreeRep (FuseTreeRep b b) c)
    (fmoveInvTrees @b @b @c)

-- | Step 4: @id ⊗ (cup ⊗ id)@ — Unit remains in the type.
cupTensorIdHom
  :: forall a b c
   . ( KnownTreeRep a
     , KnownTreeRep b
     , KnownTreeRep c
     , KnownTreeRep (FuseTreeRep b b)
     , KnownTreeRep TreeUnit
     , KnownTreeRep (FuseTreeRep (FuseTreeRep b b) c)
     , KnownTreeRep (FuseTreeRep TreeUnit c)
     , KnownTreeRep (FuseTreeRep a (FuseTreeRep (FuseTreeRep b b) c))
     , KnownTreeRep (FuseTreeRep a (FuseTreeRep TreeUnit c))
     , KnownTreeRep (FuseTreeRep b b)
     )
  => TreeV (FuseTreeRep a (FuseTreeRep (FuseTreeRep b b) c))
  -> TreeV (FuseTreeRep a (FuseTreeRep TreeUnit c))
cupTensorIdHom =
  fuseMapRight
    @a
    @(FuseTreeRep (FuseTreeRep b b) c)
    @(FuseTreeRep TreeUnit c)
    ( fuseMapLeft
        @(FuseTreeRep b b)
        @TreeUnit
        @c
        (cup @b)
    )

-- | Evaluation @ε : b ⊗ b* → 𝟙@ on genealogy Hom (@FuseTreeRep b b@, dual≅primal).
-- Singlet channels scaled by 'su2CupFactor' of the cupped root (FS·dim); others drop.
cup
  :: forall b
   . KnownTreeRep (FuseTreeRep b b)
  => TreeV (FuseTreeRep b b)
  -> TreeV TreeUnit
cup bb =
  TCons @('Leaf 0) (konst (cupHomTreesScalar @(FuseTreeRep b b) bb)) TNil

-- | Singlet walk via 'STreeRep': @sameNat@ refines @j ~ 0@ so payloads stay @C 1@.
cupHomTreesScalar
  :: forall ts
   . KnownTreeRep ts
  => TreeV ts
  -> Complex Double
cupHomTreesScalar = go (treeRepSing @ts)
  where
    go :: forall ts'. STreeRep ts' -> TreeV ts' -> Complex Double
    go STreeNil TNil = 0
    go (STreeCons t rest) (TCons v rs) =
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
   . ( KnownTreeRep a
     , KnownTreeRep c
     , KnownTreeRep (FuseTreeRep TreeUnit c)
     , KnownTreeRep (FuseTreeRep a (FuseTreeRep TreeUnit c))
     , KnownTreeRep (FuseTreeRep a c)
     , UnitorCodomain (FuseTreeRep TreeUnit c) ~ c
     )
  => TreeV (FuseTreeRep a (FuseTreeRep TreeUnit c))
  -> TreeV (FuseTreeRep a c)
unitorHom =
  fuseMapRight @a @(FuseTreeRep TreeUnit c) @c (unitor @c)

-- | Left unitor on fusion trees: @TreeUnit ⊗ c → c@ (drop @'Leaf 0@ left child).
--
-- For each @t@ in @c@, @FuseTrees ('Leaf 0) t = '[ 'Node (Root t) ('Leaf 0) t ]@
-- (SU(2): @0 ⊗ j = j@); payloads are already the root irrep of @t@.
unitor
  :: forall c
   . ( KnownTreeRep (FuseTreeRep TreeUnit c)
     , UnitorCodomain (FuseTreeRep TreeUnit c) ~ c
     )
  => TreeV (FuseTreeRep TreeUnit c)
  -> TreeV c
unitor = unitorGo (treeRepSing @(FuseTreeRep TreeUnit c))

-- | Singleton walk: @sameNat@ refines left child to @'Leaf 0@; 'UnitorCodomain' drops it.
unitorGo
  :: forall uc
   . STreeRep uc
  -> TreeV uc
  -> TreeV (UnitorCodomain uc)
unitorGo STreeNil TNil = TNil
unitorGo (STreeCons t rest) (TCons v rs) =
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
                      TCons @('Leaf rj) v (unitorGo rest rs)
                    Nothing ->
                      error "unitorGo: root mismatch after 0⊗t"
                SNode @rj @rl @rr _l _r ->
                  case sameNat (Proxy @rj) (Proxy @j) of
                    Just Refl ->
                      TCons @('Node rj rl rr) v (unitorGo rest rs)
                    Nothing ->
                      error "unitorGo: root mismatch after 0⊗t"
            Nothing ->
              error "unitorGo: expected left child 'Leaf 0"
        SNode {} ->
          error "unitorGo: expected left child 'Leaf 0"
    SLeaf {} ->
      error "unitorGo: expected Node from FuseTreeRep TreeUnit"

-- | Fused Hom compose as the five Mac Lane morphisms.
composeHomTrees
  :: forall a b c
   . ( KnownTreeRep (FuseTreeRep a b)
     , KnownTreeRep (FuseTreeRep b c)
     , FuseTreeRepTermC (FuseTreeRep a b) (FuseTreeRep b c)
     , KnownTreeRep a
     , KnownTreeRep b
     , KnownTreeRep c
     , KnownTreeRep (FuseTreeRep b b)
     , KnownTreeRep TreeUnit
     , KnownTreeRep (FuseTreeRep b (FuseTreeRep b c))
     , KnownTreeRep (FuseTreeRep (FuseTreeRep b b) c)
     , KnownTreeRep (FuseTreeRep TreeUnit c)
     , KnownTreeRep (FuseTreeRep a (FuseTreeRep b (FuseTreeRep b c)))
     , KnownTreeRep (FuseTreeRep a (FuseTreeRep (FuseTreeRep b b) c))
     , KnownTreeRep (FuseTreeRep a (FuseTreeRep TreeUnit c))
     , KnownTreeRep (FuseTreeRep a c)
     , CanFmoveOuterHom a b c
     , CanFmoveTrees b b c
     , UnitorCodomain (FuseTreeRep TreeUnit c) ~ c
     )
  => TreeV (FuseTreeRep a b)
  -> TreeV (FuseTreeRep b c)
  -> TreeV (FuseTreeRep a c)
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
   . KnownTreeRep ts
  => TreeV ts
  -> TreeV ts
  -> Bool
approxHomTrees u v =
  let bu = treeVToForgetFlat @ts u
      bv = treeVToForgetFlat @ts v
      err =
        VS.sum $
          VS.zipWith
            (\x y -> let d = x - y in realPart (d * conjugate d))
            bu
            bv
   in err < 1e-10

approxHom11 :: TreeV Hom11 -> TreeV Hom11 -> Bool
approxHom11 = approxHomTrees @Hom11

-- | 'unitor' on @TreeUnit ⊗ Leaf½@: payload round-trip.
checkUnitorLeaf1 :: Bool
checkUnitorLeaf1 =
  let u =
        TCons @('Node 1 ('Leaf 0) ('Leaf 1)) (konst 0.42) TNil
          :: TreeV (FuseTreeRep TreeUnit Leaf1)
      v = unitor @Leaf1 u
   in case treeVToV @Leaf1 v of
        x ->
          let d = x ^-^ konst 0.42
           in magnitude (d <.> d) < 1e-18

-- | 'unitorHom' = 'fuseMapRight' 'unitor' on after-cup leaf-½ spine.
checkUnitorHom11 :: Bool
checkUnitorHom11 =
  let mid =
        TCons @('Node 0 ('Leaf 1) ('Node 1 ('Leaf 0) ('Leaf 1))) (konst 0.3) $
          TCons @('Node 2 ('Leaf 1) ('Node 1 ('Leaf 0) ('Leaf 1))) (konst 0.7) TNil
      out = unitorHom @Leaf1 @Leaf1 mid
   in approxHom11 out $
        TCons @('Node 0 ('Leaf 1) ('Leaf 1)) (konst 0.3) $
          TCons @('Node 2 ('Leaf 1) ('Leaf 1)) (konst 0.7) TNil

-- | Mac Lane 'cup' on leaf Hom: singlet × FS·dim (@0 → 1@, @½ → −2@, @1 → 3@).
checkCupLeafHom :: Bool
checkCupLeafHom =
  let s0 =
        case cup @Leaf0 (idHomLeaf @0) of
          TCons v TNil -> konst 1 <.> v
          _ -> 0
      s1 =
        case cup @Leaf1 (idHomLeaf @1) of
          TCons v TNil -> konst 1 <.> v
          _ -> 0
      s2 =
        case cup @Leaf2 (idHomLeaf @2) of
          TCons v TNil -> konst 1 <.> v
          _ -> 0
   in magnitude (s0 - 1) < 1e-12
        && magnitude (s1 - (-2)) < 1e-12
        && magnitude (s2 - 3) < 1e-12

-- | Typechecks 'cupTensorIdHom' at leaf-½ (do not require a full sample spine here).
cupTensorIdHomLeaf1
  :: TreeV (FuseTreeRep Leaf1 (FuseTreeRep Hom11 Leaf1))
  -> TreeV (FuseTreeRep Leaf1 (FuseTreeRep TreeUnit Leaf1))
cupTensorIdHomLeaf1 = cupTensorIdHom @Leaf1 @Leaf1 @Leaf1

-- | Five-morphism 'composeHomTrees' unit laws on leaf-½.
checkComposeHomTrees111 :: Bool
checkComposeHomTrees111 =
  let f =
        TCons @('Node 0 ('Leaf 1) ('Leaf 1)) (konst 0.3) $
          TCons @('Node 2 ('Leaf 1) ('Leaf 1)) (konst 0.7) TNil
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
  let f = TCons @('Node 0 ('Leaf 0) ('Leaf 0)) (konst 0.4) TNil
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

approxHom22 :: TreeV Hom22 -> TreeV Hom22 -> Bool
approxHom22 = approxHomTrees @Hom22

-- | Leaf spin-1 Hom compose: @id∘id ≈ id@ and left/right units on multi-channel Hom.
checkComposeHomTrees222 :: Bool
checkComposeHomTrees222 =
  let f =
        TCons @('Node 0 ('Leaf 2) ('Leaf 2)) (konst 0.2) $
          TCons @('Node 2 ('Leaf 2) ('Leaf 2)) (konst 0.3) $
            TCons @('Node 4 ('Leaf 2) ('Leaf 2)) (konst 0.5) TNil
      idH = idHomLeaf @2
      idid = composeHomTrees @Leaf2 @Leaf2 @Leaf2 idH idH
      fid = composeHomTrees @Leaf2 @Leaf2 @Leaf2 f idH
      idf = composeHomTrees @Leaf2 @Leaf2 @Leaf2 idH f
   in approxHomTrees @Hom22 idid idH
        && approxHomTrees @Hom22 fid f
        && approxHomTrees @Hom22 idf f

approxHom33 :: TreeV Hom33 -> TreeV Hom33 -> Bool
approxHom33 = approxHomTrees @Hom33

-- | Polymorphic leaf F + outer Hom: unit laws on @tj = 3@.
checkComposeHomTrees333 :: Bool
checkComposeHomTrees333 =
  let f =
        TCons @('Node 0 ('Leaf 3) ('Leaf 3)) (konst 0.1) $
          TCons @('Node 2 ('Leaf 3) ('Leaf 3)) (konst 0.2) $
            TCons @('Node 4 ('Leaf 3) ('Leaf 3)) (konst 0.3) $
              TCons @('Node 6 ('Leaf 3) ('Leaf 3)) (konst 0.4) TNil
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
  let f :: TreeV Hom12
      f =
        TCons @('Node 1 ('Leaf 1) ('Leaf 2)) (konst 0.3) $
          TCons @('Node 3 ('Leaf 1) ('Leaf 2)) (konst 0.7) TNil
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
   in approxHomTrees @(FuseAssocL Leaf1 Leaf2 Leaf1) assocL rt

-- | Nested F: Hom⊗leaf⊗leaf (@Hom11 ⊗ ½ ⊗ ½@) round-trip via channel-keyed F.
checkFmoveHomLeft111 :: Bool
checkFmoveHomLeft111 =
  let assocL = fillTreeVScaled @(FuseAssocL Hom11 Leaf1 Leaf1)
      rt =
        fmoveInvTreesHomLeft @1 @1 @1
          (fmoveTreesHomLeft @1 @1 @1 assocL)
   in approxHomTrees @(FuseAssocL Hom11 Leaf1 Leaf1) assocL rt

--------------------------------------------------------------------------------
-- HomFused: TreeV-backed fused Hom
--------------------------------------------------------------------------------

-- | 'HomFused' compose via the five Mac Lane morphisms ('composeHomTrees').
composeHomFused
  :: forall a b c
   . ( KnownTreeRep (FuseTreeRep a b)
     , KnownTreeRep (FuseTreeRep b c)
     , FuseTreeRepTermC (FuseTreeRep a b) (FuseTreeRep b c)
     , KnownTreeRep a
     , KnownTreeRep b
     , KnownTreeRep c
     , KnownTreeRep (FuseTreeRep b b)
     , KnownTreeRep TreeUnit
     , KnownTreeRep (FuseTreeRep b (FuseTreeRep b c))
     , KnownTreeRep (FuseTreeRep (FuseTreeRep b b) c)
     , KnownTreeRep (FuseTreeRep TreeUnit c)
     , KnownTreeRep (FuseTreeRep a (FuseTreeRep b (FuseTreeRep b c)))
     , KnownTreeRep (FuseTreeRep a (FuseTreeRep (FuseTreeRep b b) c))
     , KnownTreeRep (FuseTreeRep a (FuseTreeRep TreeUnit c))
     , KnownTreeRep (FuseTreeRep a c)
     , CanFmoveOuterHom a b c
     , CanFmoveTrees b b c
     , UnitorCodomain (FuseTreeRep TreeUnit c) ~ c
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
          TCons @('Node 0 ('Leaf 2) ('Leaf 2)) (konst 0.2) $
            TCons @('Node 2 ('Leaf 2) ('Leaf 2)) (konst 0.3) $
              TCons @('Node 4 ('Leaf 2) ('Leaf 2)) (konst 0.5) TNil
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
          TCons @('Node 0 ('Leaf 3) ('Leaf 3)) (konst 0.1) $
            TCons @('Node 2 ('Leaf 3) ('Leaf 3)) (konst 0.2) $
              TCons @('Node 4 ('Leaf 3) ('Leaf 3)) (konst 0.3) $
                TCons @('Node 6 ('Leaf 3) ('Leaf 3)) (konst 0.4) TNil
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
        approxHomTrees @(FuseAssocL Leaf2 Leaf2 Leaf2) assocL $
          fmoveInvTreesLeaves @2 @2 @2 (fmoveTreesLeaves @2 @2 @2 assocL)
      idH = idHomLeaf @2
      dom = fuseTreeRepTerm @Hom22 @Hom22 idH idH
      mid = fmoveOuterHom @Leaf2 @Leaf2 @Leaf2 dom
      back = fmoveInvOuterHom @Leaf2 @Leaf2 @Leaf2 mid
   in assocOk && approxHomTrees @(FuseAssocL Leaf2 Leaf2 Hom22) dom back

-- | Outer F round-trip on Dom = Fuse(id,id): @F⁻¹ ∘ F ≈ id@.
checkFmoveOuter111 :: Bool
checkFmoveOuter111 =
  let dom = fuseTreeRepTerm @Hom11 @Hom11 (idHomLeaf @1) (idHomLeaf @1)
      mid = fmoveOuterHom @Leaf1 @Leaf1 @Leaf1 dom
      back = fmoveInvOuterHom @Leaf1 @Leaf1 @Leaf1 mid
   in approxHomTrees @Dom111 dom back

-- | 'fuseMapLeft id' is the identity on Mid.
checkFuseMapLeftId111 :: Bool
checkFuseMapLeftId111 =
  let mid =
        fmoveOuterHom @Leaf1 @Leaf1 @Leaf1 $
          fuseTreeRepTerm @Hom11 @Hom11 (idHomLeaf @1) (idHomLeaf @1)
      mid' = fuseMapLeft @Leaf1 @Leaf1 @AssocR111 id mid
   in approxHomTrees @Mid111 mid mid'

-- | Forgetful coalesced flat of a 'TreeV' (same layout as 'fuseSU2Flat' output /
-- 'ForgetTreeRep'): sectors sorted by root @2j@, multiplicity = spine order.
treeVToForgetFlat
  :: forall ts
   . KnownTreeRep ts
  => TreeV ts
  -> VS.Vector (Complex Double)
treeVToForgetFlat = packRootChannels . collectRootChannels (treeRepSing @ts)

collectRootChannels
  :: STreeRep ts
  -> TreeV ts
  -> [(Int, VS.Vector (Complex Double))]
collectRootChannels STreeNil TNil = []
collectRootChannels (STreeCons t rest) (TCons v rs) =
  case t of
    SLeaf @j ->
      (fromIntegral (natVal (Proxy @j)), toArray v)
        : collectRootChannels rest rs
    SNode @j _ _ ->
      (fromIntegral (natVal (Proxy @j)), toArray v)
        : collectRootChannels rest rs
collectRootChannels _ _ =
  error "collectRootChannels: TreeV / STreeRep mismatch"

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

-- | Inverse of 'treeVToForgetFlat' for a known spine (pops mult copies in spine order).
forgetFlatToTreeV
  :: forall ts
   . KnownTreeRep ts
  => VS.Vector (Complex Double)
  -> TreeV ts
forgetFlatToTreeV buf =
  let s = treeRepSing @ts
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
  :: STreeRep ts
  -> Map.Map Int [VS.Vector (Complex Double)]
  -> TreeV ts
scatterRootChannels STreeNil _ = TNil
scatterRootChannels (STreeCons (t :: SIrrepTree u) rest) m =
  case t of
    SLeaf @j ->
      let tj = fromIntegral (natVal (Proxy @j)) :: Int
       in case Map.lookup tj m of
            Just (v : vs) ->
              TCons @u
                (unsafeFromArray v)
                (scatterRootChannels rest (Map.insert tj vs m))
            _ ->
              error "scatterRootChannels: missing multiplicity slot"
    SNode @j _ _ ->
      let tj = fromIntegral (natVal (Proxy @j)) :: Int
       in case Map.lookup tj m of
            Just (v : vs) ->
              TCons @u
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
   . ( KnownTreeRep a
     , KnownTreeRep q
     , KnownTreeRep q'
     , KnownTreeRep (FuseTreeRep a q)
     , KnownTreeRep (FuseTreeRep a q')
     )
  => (TreeV q -> TreeV q')
  -> TreeV (FuseTreeRep a q)
  -> TreeV (FuseTreeRep a q')
fuseMapRight f tv =
  let secsA = treeRepExpandedSectors (treeRepSing @a)
      secsQ = treeRepExpandedSectors (treeRepSing @q)
      secsQ' = treeRepExpandedSectors (treeRepSing @q')
      fFlat =
        treeVToExpandedFlat @q' . f . expandedFlatToTreeV @q
      vin = treeVToForgetFlat @(FuseTreeRep a q) tv
      vout = fuseMapRightFlatSectors secsA secsQ secsQ' fFlat vin
   in forgetFlatToTreeV @(FuseTreeRep a q') vout

-- | Expanded @(tj, 1, off)@ sectors — one slot per tree (spine order).
treeRepExpandedSectors :: STreeRep ts -> [(Int, Int, Int)]
treeRepExpandedSectors = go 0
  where
    go :: Int -> STreeRep ts' -> [(Int, Int, Int)]
    go _ STreeNil = []
    go off (STreeCons t rest) =
      let tj = rootLab t
          d = tj + 1
       in (tj, 1, off) : go (off + d) rest

-- | Concatenate root vectors in spine order (matches 'treeRepExpandedSectors').
treeVToExpandedFlat
  :: forall ts
   . KnownTreeRep ts
  => TreeV ts
  -> VS.Vector (Complex Double)
treeVToExpandedFlat = go (treeRepSing @ts)
  where
    go :: STreeRep ts' -> TreeV ts' -> VS.Vector (Complex Double)
    go STreeNil TNil = VS.empty
    go (STreeCons t rest) (TCons v rs) =
      case t of
        SLeaf {} -> toArray v VS.++ go rest rs
        SNode {} -> toArray v VS.++ go rest rs
    go _ _ = error "treeVToExpandedFlat: TreeV / STreeRep mismatch"

-- | Inverse of 'treeVToExpandedFlat'.
expandedFlatToTreeV
  :: forall ts
   . KnownTreeRep ts
  => VS.Vector (Complex Double)
  -> TreeV ts
expandedFlatToTreeV buf = go 0 (treeRepSing @ts)
  where
    go :: Int -> STreeRep ts' -> TreeV ts'
    go _ STreeNil = TNil
    go off (STreeCons (t :: SIrrepTree u) rest) =
      case t of
        SLeaf @j ->
          let d = fromIntegral (natVal (Proxy @j)) + 1
              v = unsafeFromArray (VS.slice off d buf)
           in TCons @u v (go (off + d) rest)
        SNode @j _ _ ->
          let d = fromIntegral (natVal (Proxy @j)) + 1
              v = unsafeFromArray (VS.slice off d buf)
           in TCons @u v (go (off + d) rest)

-- | Coalesced @(tj, multiplicity)@ pairs matching 'ForgetTreeRep' / 'fuseSU2Flat'.
forgetSectorPairs :: STreeRep ts -> [(Int, Int)]
forgetSectorPairs =
  Map.toAscList
    . Prelude.foldl
      (\m j -> Map.insertWith (+) j 1 m)
      Map.empty
    . treeRootList

treeRootList :: STreeRep ts -> [Int]
treeRootList STreeNil = []
treeRootList (STreeCons t rest) = rootLab t : treeRootList rest

fuseMapLeft
  :: forall a a' b
   . ( KnownTreeRep a
     , KnownTreeRep a'
     , KnownTreeRep b
     , KnownTreeRep (FuseTreeRep a b)
     , KnownTreeRep (FuseTreeRep a' b)
     )
  => (TreeV a -> TreeV a')
  -> TreeV (FuseTreeRep a b)
  -> TreeV (FuseTreeRep a' b)
fuseMapLeft f tv =
  let secsA = treeRepExpandedSectors (treeRepSing @a)
      secsA' = treeRepExpandedSectors (treeRepSing @a')
      secsB = treeRepExpandedSectors (treeRepSing @b)
      fFlat =
        treeVToExpandedFlat @a' . f . expandedFlatToTreeV @a
      vin = treeVToForgetFlat @(FuseTreeRep a b) tv
      vout = fuseMapLeftFlatSectors secsA secsA' secsB fFlat vin
   in forgetFlatToTreeV @(FuseTreeRep a' b) vout

--------------------------------------------------------------------------------
-- Braid (copy-axis swap on each sector)
--------------------------------------------------------------------------------

-- | Categorical swap of copy factors @C m ⊗ C n@ (irrep leg unchanged).
swapCopyProductSector
  :: forall m n d
   . ( KnownNat m
     , KnownNat n
     , KnownNat d
     )
  => (C m ⊗ C n) ⊗ C d
  -> (C n ⊗ C m) ⊗ C d
swapCopyProductSector sec = (swapMap ⊗^ id) $ sec

-- | Braid an unfused atom pair: @r ⊗ q → q ⊗ r@.
swapAtomPair
  :: forall j1 j2 m n
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat m
     , KnownNat n
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     )
  => AtomPairV j1 j2 m n
  -> AtomPairV j2 j1 n m
swapAtomPair sec = swapMap $ sec

-- | Sector-level braid payload (@BraidMult@ on the copy axis).
braidSector
  :: SIrrep j
  -> SMult μ
  -> ToVSector j μ
  -> ToVSector j (BraidMult μ)
braidSector SAtomI SMultAtom v = v
braidSector (SAtomI @j) (SMultProd (SMultAtom @m) (SMultAtom @n)) v =
  swapCopyProductSector @m @n @(IrrepDim j) v
braidSector _ _ _ =
  error "braidSector: unsupported multiplicity shape"

-- | Braid every sector in a 'RepV' spine (driven by 'SRep'; no 'BraidSpine' class).
braid
  :: forall rs
   . KnownSymRep rs
  => RepV rs
  -> RepV (Braid rs)
braid = go (symRepSing @rs)
  where
    go :: forall rs'. SRep rs' -> RepV rs' -> RepV (Braid rs')
    go SRepNil RNil = RNil
    go (SRepCons se sm rest) (RCons v rs) =
      RCons (braidSector se sm v) (go rest rs)

-- | Project a spine onto its trivial (@0@) sectors.
--
-- Atom keep-vs-drop still needs 'ProjectAtomOrd': @CmpNat j 0@ only reduces when
-- @j@ is in an instance head.
class ProjectToSymmetric (rs :: Rep) where
  projectToSymmetric :: RepV rs -> RepV (FilterTrivial rs)

instance ProjectToSymmetric '[] where
  projectToSymmetric RNil = RNil

instance {-# OVERLAPPING #-}
  ( CmpNat j 0 ~ ord
  , ProjectAtomOrd ord j ('AtomM m) rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('(j, 'AtomM m) ': rest)
  where
  projectToSymmetric (RCons v rs) =
    projectAtomOrd @ord @j @('AtomM m) @rest
      v
      (projectToSymmetric rs)

instance {-# OVERLAPPING #-}
  ( CmpNat j 0 ~ ord
  , ProjectAtomOrd ord j ('Prod ('AtomM m) ('AtomM n)) rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('(j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  projectToSymmetric (RCons v rs) =
    projectAtomOrd @ord @j @('Prod ('AtomM m) ('AtomM n)) @rest
      v
      (projectToSymmetric rs)

instance {-# OVERLAPPABLE #-}
  ( FilterTrivial ('(e, μ) ': rest) ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('(e, μ) ': rest)
  where
  projectToSymmetric (RCons _ rs) = projectToSymmetric rs

-- | Keep (@'EQ@ / @j ~ 0@) or drop (@'GT@) one atom sector.
-- Rest is already 'FilterTrivial'-projected (caller responsibility).
class ProjectAtomOrd
  (ord :: Ordering)
  (j :: Nat)
  (μ :: MultExpr)
  (rest :: Rep)
 where
  projectAtomOrd
    :: ToVSector j μ
    -> RepV (FilterTrivial rest)
    -> RepV (FilterTrivial ('(j, μ) ': rest))

instance
  ( j ~ 0
  ) =>
  ProjectAtomOrd 'EQ j μ rest
  where
  projectAtomOrd v rs = RCons @0 @μ v rs

instance
  ( FilterTrivial ('(j, μ) ': rest) ~ FilterTrivial rest
  ) =>
  ProjectAtomOrd 'GT j μ rest
  where
  projectAtomOrd _ rs = rs

--------------------------------------------------------------------------------
-- rmove (R-matrix on fused tensor)
--------------------------------------------------------------------------------

-- | SU(2) R-phase @(-1)^((j₁+j₂-j)/2)@ on one fused atom sector.
rPhaseSector
  :: forall j1 j2 j μ
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , VectorSpace (ToVSector j μ)
     , Scalar (ToVSector j μ) ~ Complex Double
     )
  => ToVSector j μ
  -> ToVSector j μ
rPhaseSector v = (phase :+ 0) *^ v
  where
    phase = (-1) ^ ((tj1 + tj2 - tj) `div` 2)
    tj1 = fromIntegral (natVal (Proxy @j1)) :: Int
    tj2 = fromIntegral (natVal (Proxy @j2)) :: Int
    tj = fromIntegral (natVal (Proxy @j)) :: Int

-- | Copy-leg swap after R-phase (@'AtomM'@ fixed; @'Prod'@ legs flip).
type family RmoveMult (μ :: MultExpr) :: MultExpr where
  RmoveMult ('AtomM m) = 'AtomM m
  RmoveMult ('Prod ('AtomM m) ('AtomM n)) = 'Prod ('AtomM n) ('AtomM m)
  RmoveMult ('Prod μ1 μ2) = 'Prod (RmoveMult μ2) (RmoveMult μ1)

-- | Fused spine after R-move: irrep fixed; multiplicity via 'RmoveMult'.
type family RmoveTarget (j1 :: Nat) (j2 :: Nat) (rs :: Rep) :: Rep where
  RmoveTarget _ _ '[] = '[]
  RmoveTarget j1 j2 ('(e, μ) ': rest) =
    '(e, RmoveMult μ) ': RmoveTarget j1 j2 rest

-- | Sector-level R-move (phase + optional copy swap). Fused atom spines only.
rmoveSector
  :: forall j1 j2 j μ
   . ( KnownNat j1
     , KnownNat j2
     )
  => SIrrep j
  -> SMult μ
  -> ToVSector j μ
  -> ToVSector j (RmoveMult μ)
rmoveSector SAtomI (SMultAtom @m) v =
  rPhaseSector @j1 @j2 @j @('AtomM m) v
rmoveSector SAtomI (SMultProd (SMultAtom @m) (SMultAtom @n)) v =
  swapCopyProductSector @m @n @(IrrepDim j)
    (rPhaseSector @j1 @j2 @j @('Prod ('AtomM m) ('AtomM n)) v)
rmoveSector _ _ _ =
  error "rmoveSector: expected fused atom spine"

-- | R-move every sector in a fused 'RepV' spine (R-phase, then copy swap on @'Prod'@).
-- Driven by 'SRep' (no dedicated fused-atom singleton).
rmoveSpine
  :: forall j1 j2 rs
   . ( KnownNat j1
     , KnownNat j2
     , KnownSymRep rs
     )
  => RepV rs
  -> RepV (RmoveTarget j1 j2 rs)
rmoveSpine = go (symRepSing @rs)
  where
    go
      :: forall rs'
       . SRep rs'
      -> RepV rs'
      -> RepV (RmoveTarget j1 j2 rs')
    go SRepNil RNil = RNil
    go (SRepCons se sm rest) (RCons v rs) =
      RCons (rmoveSector @j1 @j2 se sm v) (go rest rs)

-- | Leaf braiding @r ⊗ s → s ⊗ r@ on a fused pair
-- (@fuseExpr ∘ braid ≅ rmove ∘ fuseExpr@).
rmove
  :: forall j1 j2 r s
   . ( KnownNat j1
     , KnownNat j2
     , KnownSymRep (FuseHom r s)
     , RmoveTarget j1 j2 (FuseHom r s) ~ FuseHom s r
     )
  => RepV (FuseHom r s)
  -> RepV (FuseHom s r)
rmove = rmoveSpine @j1 @j2 @(FuseHom r s)



-- f : Hom(½ → 1) = FuseTreeRep Leaf1 Leaf2
f :: TreeV Hom12
f =
  TCons @('Node 1 ('Leaf 1) ('Leaf 2)) (konst 0.3) $
    TCons @('Node 3 ('Leaf 1) ('Leaf 2)) (konst 0.7) TNil
-- right unit: id₁ ∘ f = f

g :: TreeV Hom21
g = TCons @('Node 1 ('Leaf 2) ('Leaf 1)) (konst 0.3) $
    TCons @('Node 3 ('Leaf 2) ('Leaf 1)) (konst 0.7) TNil


example = composeHomTrees @Leaf1 @Leaf2 @Leaf1 f g
-- left unit: f ∘ id₂ = f
-- composeHomTrees @Leaf1 @Leaf2 @Leaf2 f (idHomLeaf @2)