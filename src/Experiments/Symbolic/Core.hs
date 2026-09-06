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

-- | Term-level symbolic SU(2) reps: singletons, 'RepV', fuseExpr / coalesce / cup.
--
-- Type kinds and families live in 'Experiments.Symbolic.Expr' /
-- 'Experiments.Symbolic.TypeLevel'. Flat-buffer oracles:
-- 'Experiments.Symbolic.Reference'. Examples: 'Experiments.SymbolicExamples'.
--
-- Sectors are atom-keyed. Unfused tensor / dual spaces are 'ToVSpine' values
-- ('rtensor' / 'rdual' / 'rmor'), reduced by 'fuseExpr' or paired by
-- 'cupUnfused' / 'cupRdual' (object @r ⊗ r*@); fused 'cupFused' / 'capFused'
-- on singlets of @FilterTrivial (FuseHom r r)@ after dual≅primal.
-- 'HomUnfused' \/ 'HomFused' index morphisms by fusion trees @Obj Nat@.
-- Unfused Hom: @Dual(ToVObj a) ⊗ ToVObj b@ (complete Category, linearmap α / unitors).
-- Fused Hom: @ToVSpine (FuseHom (FuseSym a) (FuseSym b))@ — coalesced 'Rep' spine
-- ('composeMorFused': fuseExpr then stubbed F-move \/ cup; FuseRep unitor).
-- 'repVToV' / 'vToRepV' round-trip a 'KnownSymRep' spine through 'ToVSpine'.
-- Phase-1 'Irrep' \/ 'TreeRep' singletons live alongside; Hom not yet rewired onto trees.
module Experiments.Symbolic.Core where

import Data.Complex (Complex ((:+)), magnitude)
import Data.Coerce (coerce)
import Data.Kind (Constraint, Type)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (AdditiveGroup (zeroV, (^+^), (^-^)), InnerSpace ((<.>)), Scalar, VectorSpace ((*^)))
import qualified Data.Vector.Storable as VS
import GHC.TypeLits (CmpNat, KnownNat, Nat, natVal, type (*), type (+))
import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..))
import Experiments.Categorical.Associative (Associative (..))
import Experiments.Categorical.Bifunctor (Bifunctor (..), PFunctor (..), QFunctor (..))
import Experiments.Categorical.Braided (Braided (..))
import Experiments.Categorical.Monoidal (Monoidal (..))
import Experiments.Fusion.Obj (Obj)
import qualified Experiments.Fusion.Obj as FObj
import Experiments.Fusion.SU2 (su2FSymbol)
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
  , fuseLeafAssocHalf
  , unfuseCGChannel
  , unfuseLeafAssocHalf
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
  , flattenTensorProdCopy
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

-- | CG one output channel on irrep legs (@'AtomM'@ copy layout).
fuseOneChannelAtomM
  :: forall j1 j2 j m
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     , KnownNat (IrrepDim j)
     )
  => (C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  -> ToVSector j ('AtomM m)
fuseOneChannelAtomM sec =
  ((id ⊗^ fuseCGChannel @j1 @j2 @j) . rassocMap) $ sec

-- | CG one output channel on irrep legs (@'Prod'@ copy layout).
fuseOneChannelProd
  :: forall j1 j2 j m n
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , KnownNat m
     , KnownNat n
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     , KnownNat (IrrepDim j)
     , KnownNat (m * n)
     )
  => AtomPairV j1 j2 m n
  -> ToVSector j ('Prod ('AtomM m) ('AtomM n))
fuseOneChannelProd sec =
  ( (id ⊗^ fuseCGChannel @j1 @j2 @j)
      . (splitBond @m @n ⊗^ id)
      . arr (LinearFunction flattenTensorProdCopy)
  )
    $ sec

-- | Walk CG channels for an atom pair, building a tagged atom spine.
class FuseAtomPairSpine (j1 :: Nat) (j2 :: Nat) (μ :: MultExpr) (cg :: [(Nat, Nat)]) where
  fuseAtomPairSpine
    :: AtomPairPayload j1 j2 μ
    -> RepV (TagMult μ (AtomsFromCG cg))

-- | Payload for @fuseAtomPairSpine@ by multiplicity shape.
type family AtomPairPayload (j1 :: Nat) (j2 :: Nat) (μ :: MultExpr) :: Type where
  AtomPairPayload j1 j2 ('AtomM m) =
    C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2)
  AtomPairPayload j1 j2 ('Prod ('AtomM m) ('AtomM n)) =
    AtomPairV j1 j2 m n

instance FuseAtomPairSpine j1 j2 μ '[] where
  fuseAtomPairSpine _ = RNil

instance
  ( FuseAtomPairSpine j1 j2 ('AtomM m) rest
  , KnownNat j
  , KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , KnownNat (IrrepDim j)
  ) =>
  FuseAtomPairSpine j1 j2 ('AtomM m) ('(j, mOut) ': rest)
  where
  fuseAtomPairSpine v =
    repCons @j @('AtomM m)
      (fuseOneChannelAtomM @j1 @j2 @j @m v)
      (fuseAtomPairSpine @j1 @j2 @('AtomM m) @rest v)

instance
  ( FuseAtomPairSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) rest
  , KnownNat j
  , KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , KnownNat (IrrepDim j)
  , KnownNat (m * n)
  ) =>
  FuseAtomPairSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) ('(j, mOut) ': rest)
  where
  fuseAtomPairSpine v =
    repCons @j @('Prod ('AtomM m) ('AtomM n))
      (fuseOneChannelProd @j1 @j2 @j @m @n v)
      (fuseAtomPairSpine @j1 @j2 @('Prod ('AtomM m) ('AtomM n)) @rest v)

-- | CG-fuse one atom×atom pair (@'AtomM@ copy) to a tagged atom spine.
fuseOneSectorTensorAtomM
  :: forall j1 j2 m
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat m
     , FuseAtomPairSpine j1 j2 ('AtomM m) (TensorIrrepRepSU2 j1 j2)
     )
  => (C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  -> RepV (FuseAtoms j1 j2 ('AtomM m))
fuseOneSectorTensorAtomM =
  fuseAtomPairSpine @j1 @j2 @('AtomM m) @(TensorIrrepRepSU2 j1 j2)

-- | CG-fuse one atom×atom pair (@'Prod@ copy) to a tagged atom spine.
fuseOneSectorTensorProd
  :: forall j1 j2 m n
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat m
     , KnownNat n
     , FuseAtomPairSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) (TensorIrrepRepSU2 j1 j2)
     )
  => AtomPairV j1 j2 m n
  -> RepV (FuseAtoms j1 j2 ('Prod ('AtomM m) ('AtomM n)))
fuseOneSectorTensorProd =
  fuseAtomPairSpine @j1 @j2 @('Prod ('AtomM m) ('AtomM n)) @(TensorIrrepRepSU2 j1 j2)

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
-- (Per-sector "fuse" is identity on atom keys; CG fuse is 'fuseExpr'.)
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

-- | Flatten every sector copy axis to @'AtomM@ (term-level 'FlattenRep').
class FlattenRepTerm (rs :: Rep) where
  flattenRepTerm :: RepV rs -> RepV (FlattenRep rs)

instance FlattenRepTerm '[] where
  flattenRepTerm RNil = RNil

instance
  ( FlattenCopy j μ
  , FlattenRepTerm rest
  , EvalMult μ ~ m
  , FlattenMult μ ~ 'AtomM m
  , KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  ) =>
  FlattenRepTerm ('(j, μ) ': rest)
  where
  flattenRepTerm (RCons v rs) =
    RCons @j @('AtomM m) (flattenCopy @j @μ v) (flattenRepTerm rs)

-- | Fuse two atom spines by CG on each atom pair.
fuseExpr
  :: forall r q
   . ( KnownAtomRep r
     , KnownAtomRep q
     , FuseAtomSpinesTerm r q
     , KnownSymRep (FuseAtomSpines r q)
     , CoalesceSpine (FuseAtomSpines r q)
     )
  => RepV r
  -> RepV q
  -> RepV (FuseHom r q)
fuseExpr x y =
  coalesce (fuseAtomSpinesTerm (symRepSing @r) x (symRepSing @q) y)

-- | 'fuseExpr' then flatten @'Prod@ → @'AtomM@ (F-move / Symmetry flat layout).
fuseExprFlat
  :: forall r q
   . ( KnownAtomRep r
     , KnownAtomRep q
     , FuseAtomSpinesTerm r q
     , KnownSymRep (FuseAtomSpines r q)
     , CoalesceSpine (FuseAtomSpines r q)
     , FlattenRepTerm (FuseHom r q)
     )
  => RepV r
  -> RepV q
  -> RepV (FuseFlat r q)
fuseExprFlat x y =
  flattenRepTerm @(FuseHom r q) (fuseExpr @r @q x y)

-- | Term-level constraints for walking @FuseAtomSpines@.
type family FuseAtomSpinesTerm (r :: Rep) (q :: Rep) :: Constraint where
  FuseAtomSpinesTerm '[] _ = ()
  FuseAtomSpinesTerm ('(j1, 'AtomM m1) ': rest) q =
    ( FuseAtomSpineOneTerm j1 ('AtomM m1) q
    , FuseAtomSpinesTerm rest q
    )

type family FuseAtomSpineOneTerm (j1 :: Nat) (μ1 :: MultExpr) (q :: Rep) :: Constraint where
  FuseAtomSpineOneTerm _ _ '[] = ()
  FuseAtomSpineOneTerm j1 ('AtomM m1) ('(j2, 'AtomM m2) ': rest) =
    ( KnownNat j1
    , KnownNat j2
    , KnownNat m1
    , KnownNat m2
    , KnownNat (IrrepDim j1)
    , KnownNat (IrrepDim j2)
    , FuseAtomPairSpine j1 j2 ('Prod ('AtomM m1) ('AtomM m2)) (TensorIrrepRepSU2 j1 j2)
    , FuseAtomSpineOneTerm j1 ('AtomM m1) rest
    )

fuseAtomSpinesTerm
  :: forall r q
   . FuseAtomSpinesTerm r q
  => SRep r
  -> RepV r
  -> SRep q
  -> RepV q
  -> RepV (FuseAtomSpines r q)
fuseAtomSpinesTerm SRepNil RNil _ _ = RNil
fuseAtomSpinesTerm
  (SRepCons (SAtomI @j1) (SMultAtom @m1) rRest)
  (RCons v1 rRestV)
  qSing
  q =
  appendRepV
    (fuseAtomSpineOneTerm @j1 @('AtomM m1) (SAtomI @j1) (SMultAtom @m1) v1 qSing q)
    (fuseAtomSpinesTerm rRest rRestV qSing q)
fuseAtomSpinesTerm _ _ _ _ =
  error "fuseAtomSpinesTerm: expected atom spine"

fuseAtomSpineOneTerm
  :: forall j1 μ1 q
   . FuseAtomSpineOneTerm j1 μ1 q
  => SIrrep j1
  -> SMult μ1
  -> ToVSector j1 μ1
  -> SRep q
  -> RepV q
  -> RepV (FuseAtomSpineOne j1 μ1 q)
fuseAtomSpineOneTerm _ _ _ SRepNil RNil = RNil
fuseAtomSpineOneTerm
  SAtomI
  (SMultAtom @m1)
  v1
  (SRepCons (SAtomI @j2) (SMultAtom @m2) qRest)
  (RCons v2 qRestV) =
  appendRepV
    ( fuseOneSectorTensorProd @j1 @j2 @m1 @m2 (v1 ⊗ v2)
    )
    (fuseAtomSpineOneTerm @j1 @('AtomM m1) (SAtomI @j1) (SMultAtom @m1) v1 qRest qRestV)
fuseAtomSpineOneTerm _ _ _ _ _ =
  error "fuseAtomSpineOneTerm: expected atom spine"

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
-- Fused: 'RepV' on singlet spines after dual≅primal + 'FuseHom'.
-- Cap on ⊕ is the diagonal coevaluation (biproduct natural η).
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

-- | Fused evaluation on singlets of @FuseHom r r@ (dual≅primal).
cupFused
  :: forall r
   . ( KnownAtomRep r
     , CupTrivial (FilterTrivial (FuseHom r r))
     )
  => RepV (FilterTrivial (FuseHom r r))
  -> RepV Unit
cupFused = cupTrivial

-- | Linear extension of 'fuseExpr' @r ⊗ r → FuseHom r r@.
fuseExprTensor
  :: forall r
   . ( KnownAtomRep r
     , FuseAtomSpinesTerm r r
     , KnownSymRep (FuseAtomSpines r r)
     , CoalesceSpine (FuseAtomSpines r r)
     , KnownSymRep (FuseHom r r)
     , LinearSpace (ToVSpine r)
     , LinearSpace (ToVSpine (FuseHom r r))
     , Scalar (ToVSpine r) ~ Complex Double
     , Scalar (ToVSpine (FuseHom r r))
         ~ Complex Double
     )
  => ToVSpine r ⊗ ToVSpine r
  -> RepV (FuseHom r r)
fuseExprTensor t =
  vToRepV @(FuseHom r r) $
    (uncurryLinearMap -+$=> fuseCurried) $ t
  where
    fuseCurried ::
      ToVSpine r
        +> ( ToVSpine r
               +> ToVSpine (FuseHom r r)
           )
    fuseCurried =
      arr . LinearFunction $ \x ->
        arr . LinearFunction $ \y ->
          repVToV $ fuseExpr @r @r (vToRepV @r x) (vToRepV @r y)

-- | Fused coevaluation: diagonal @η@ into singlets of @FuseHom r r@.
--
-- @projectToSymmetric ∘ fuseExprTensor ∘ (id ⊗ undual) ∘ idTensor@ — biproduct-natural
-- (off-diagonal blocks vanish under 'FilterTrivial' for SU(2)).
capFused
  :: forall r
   . ( KnownAtomRep r
     , FuseAtomSpinesTerm r r
     , KnownSymRep (FuseAtomSpines r r)
     , CoalesceSpine (FuseAtomSpines r r)
     , KnownSymRep (FuseHom r r)
     , ProjectToSymmetric (FuseHom r r)
     , LinearSpace (ToVSpine r)
     , LinearSpace (DualVector (ToVSpine r))
     , LinearSpace (ToVSpine (FuseHom r r))
     , Scalar (ToVSpine r) ~ Complex Double
     , Scalar (DualVector (ToVSpine r)) ~ Complex Double
     , Scalar (ToVSpine (FuseHom r r))
         ~ Complex Double
     , TensorSpace (DualVector (ToVSpine r))
     )
  => RepV Unit
  -> RepV (FilterTrivial (FuseHom r r))
capFused u =
  let η = unitScalar u *^ idTensor @(ToVSpine r)
      undualMap =
        arr (LinearFunction (undualSpine @r))
          :: DualVector (ToVSpine r) +> ToVSpine r
      ηPrimal = (id ⊗^ undualMap) $ η
   in projectToSymmetric (fuseExprTensor @r ηPrimal)

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

-- | Fused morphisms @a → b@: CG Hom as a coalesced 'Rep' spine
-- @ToVSpine (FuseHom (FuseSym a) (FuseSym b))@ (SU(2) dual≅primal).
-- Composition needs an F-move; Category @(. )@ is stubbed.
newtype HomFused (a :: Obj Nat) (b :: Obj Nat) = HomFused
  { unHomFused :: ToVSpine (FuseHom (FuseSym a) (FuseSym b)) }

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

-- | Fused identity: undual Dual-left @η@, then CG-fuse to @FuseHom a a@.
idMorFused
  :: forall a
   . ( KnownAtomRep a
     , FuseAtomSpinesTerm a a
     , KnownSymRep (FuseAtomSpines a a)
     , CoalesceSpine (FuseAtomSpines a a)
     , KnownSymRep (FuseHom a a)
     , LinearSpace (ToVSpine a)
     , LinearSpace (DualVector (ToVSpine a))
     , LinearSpace (ToVSpine (FuseHom a a))
     , Scalar (ToVSpine a) ~ Complex Double
     , Scalar (DualVector (ToVSpine a)) ~ Complex Double
     , Scalar (ToVSpine (FuseHom a a)) ~ Complex Double
     , TensorSpace (DualVector (ToVSpine a))
     )
  => ToVSpine (FuseHom a a)
idMorFused =
  let undualMap =
        arr (LinearFunction (undualSpine @a))
          :: DualVector (ToVSpine a) +> ToVSpine a
      ηPrimal = (undualMap ⊗^ id) $ idMor @a
   in repVToV @(FuseHom a a) (fuseExprTensor @a ηPrimal)

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
-- Category \/ monoidal structure: HomUnfused (complete) and HomFused (stubbed compose)
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

-- | Object constraint for fused Hom: @FuseHom a a@ identity / cups on the diagonal.
type KnownHomFused (a :: Rep) =
  ( KnownAtomRep a
  , FuseAtomSpinesTerm a a
  , KnownSymRep (FuseAtomSpines a a)
  , CoalesceSpine (FuseAtomSpines a a)
  , KnownSymRep (FuseHom a a)
  , LinearSpace (ToVSpine a)
  , LinearSpace (DualVector (ToVSpine a))
  , LinearSpace (ToVSpine (FuseHom a a))
  , Scalar (ToVSpine a) ~ Complex Double
  , Scalar (DualVector (ToVSpine a)) ~ Complex Double
  , Scalar (ToVSpine (FuseHom a a)) ~ Complex Double
  , TensorSpace (ToVSpine a)
  , TensorSpace (DualVector (ToVSpine a))
  , TensorSpace (ToVSpine (FuseHom a a))
  )

instance Category HomFused where
  type Object HomFused a = KnownHomFused (FuseSym a)

  id :: forall a. Object HomFused a => HomFused a a
  id = HomFused (idMorFused @(FuseSym a))

  (.)
    :: forall a b c
     . (Object HomFused a, Object HomFused b, Object HomFused c)
    => HomFused b c
    -> HomFused a b
    -> HomFused a c
  -- Needs F-move / braiding on @FuseHom@ spines; not Dual-left reassoc.
  (.) = undefined

instance PFunctor FObj.Tensor HomFused HomFused where
  -- Via 'bimap' once general fused bimap exists; Schur path: 'bimapHomFusedIrrep'.
  first _ = undefined

instance QFunctor FObj.Tensor HomFused HomFused where
  second _ = undefined

-- | Fused @f ⊗ g@ on irrep endomorphisms (Schur): @α id ⊗ β id = αβ id@ on every
-- total-@J@ block of @Fuse(a,b)@. No unfuse / refuse densify.
--
-- General HomFused @bimap@ (arbitrary Dual-left Hom spines) still needs the
-- reducible mult-space formula or braid+F after @fuseExpr@; see 'bimapHomFusedIrrep'.
instance Bifunctor FObj.Tensor HomFused HomFused HomFused where
  bimap
    :: forall a b c d
     . ( Object HomFused a
       , Object HomFused b
       , Object HomFused c
       , Object HomFused d
       , Object HomFused (FObj.Tensor a c)
       , Object HomFused (FObj.Tensor b d)
       )
    => HomFused a b
    -> HomFused c d
    -> HomFused (FObj.Tensor a c) (FObj.Tensor b d)
  -- Blocker: general Dual-left Hom spines (not just Schur scalars on atoms).
  bimap = undefined

-- | Read the Schur scalar of a fused Hom endomorphism on an atom (@cup@ of the
-- singlet \/ @cup@ of @id@). For @α · id@, returns @α@.
homFusedAtomScalar
  :: forall j
   . ( Object HomFused ('FObj.Atom j)
     , CupTrivial (FilterTrivial (FuseHom (Atom1 j) (Atom1 j)))
     , ProjectToSymmetric (FuseHom (Atom1 j) (Atom1 j))
     , KnownSymRep (FilterTrivial (FuseHom (Atom1 j) (Atom1 j)))
     )
  => HomFused ('FObj.Atom j) ('FObj.Atom j)
  -> Complex Double
homFusedAtomScalar (HomFused m) =
  let u = unitToVScalar (cupMiddleFused @(Atom1 j) m)
      uId =
        unitToVScalar
          (cupMiddleFused @(Atom1 j) (idMorFused @(Atom1 j)))
   in if magnitude uId < 1e-14 then 0 else u / uId

-- | Object-level fused bimap for irreps: scale every channel of @FuseFlat ja jb@
-- by @αβ@ (Schur). Codomain equals domain (@α id ⊗ β id@).
fuseBimapIrrep
  :: forall ja jb
   . ( KnownSymRep (FuseFlat (Atom1 ja) (Atom1 jb))
     , LinearSpace (ToVSpine (FuseFlat (Atom1 ja) (Atom1 jb)))
     , Scalar (ToVSpine (FuseFlat (Atom1 ja) (Atom1 jb))) ~ Complex Double
     )
  => Complex Double
  -> Complex Double
  -> ToVSpine (FuseFlat (Atom1 ja) (Atom1 jb))
  -> ToVSpine (FuseFlat (Atom1 ja) (Atom1 jb))
fuseBimapIrrep alpha beta = ((alpha * beta) *^)

-- | Hom-level fused bimap for atom endomorphisms (screenshot Schur case):
-- @Hom(ja,ja) × Hom(jb,jb) → Hom(ja⊗jb, ja⊗jb)@ via @αβ · id@.
bimapHomFusedIrrep
  :: forall ja jb
   . ( Object HomFused ('FObj.Atom ja)
     , Object HomFused ('FObj.Atom jb)
     , Object HomFused
         (FObj.Tensor ('FObj.Atom ja) ('FObj.Atom jb))
     , CupTrivial (FilterTrivial (FuseHom (Atom1 ja) (Atom1 ja)))
     , CupTrivial (FilterTrivial (FuseHom (Atom1 jb) (Atom1 jb)))
     , ProjectToSymmetric (FuseHom (Atom1 ja) (Atom1 ja))
     , ProjectToSymmetric (FuseHom (Atom1 jb) (Atom1 jb))
     , KnownSymRep (FilterTrivial (FuseHom (Atom1 ja) (Atom1 ja)))
     , KnownSymRep (FilterTrivial (FuseHom (Atom1 jb) (Atom1 jb)))
     )
  => HomFused ('FObj.Atom ja) ('FObj.Atom ja)
  -> HomFused ('FObj.Atom jb) ('FObj.Atom jb)
  -> HomFused
       (FObj.Tensor ('FObj.Atom ja) ('FObj.Atom jb))
       (FObj.Tensor ('FObj.Atom ja) ('FObj.Atom jb))
bimapHomFusedIrrep f g =
  let alpha = homFusedAtomScalar @ja f
      beta = homFusedAtomScalar @jb g
   in HomFused $
        (alpha * beta)
          *^ idMorFused
            @( FuseSym
                 (FObj.Tensor ('FObj.Atom ja) ('FObj.Atom jb))
             )

instance Associative HomFused FObj.Tensor where
  associate = undefined
  disassociate = undefined

instance Monoidal HomFused FObj.Tensor where
  type Id HomFused FObj.Tensor = 'FObj.Atom 0

  idl
    :: forall a
     . ( Object HomFused a
       , Object HomFused ('FObj.Atom 0)
       , Object HomFused (FObj.Tensor ('FObj.Atom 0) a)
       )
    => HomFused (FObj.Tensor ('FObj.Atom 0) a) a
  -- @FuseRep@ unitors: @FuseSym (Unit ⊗ a) ~ FuseSym a@.
  idl = HomFused (idMorFused @(FuseSym a))

  idr
    :: forall a
     . ( Object HomFused a
       , Object HomFused ('FObj.Atom 0)
       , Object HomFused (FObj.Tensor a ('FObj.Atom 0))
       )
    => HomFused (FObj.Tensor a ('FObj.Atom 0)) a
  idr = HomFused (idMorFused @(FuseSym a))

  coidl
    :: forall a
     . ( Object HomFused a
       , Object HomFused ('FObj.Atom 0)
       , Object HomFused (FObj.Tensor ('FObj.Atom 0) a)
       )
    => HomFused a (FObj.Tensor ('FObj.Atom 0) a)
  coidl = HomFused (idMorFused @(FuseSym a))

  coidr
    :: forall a
     . ( Object HomFused a
       , Object HomFused ('FObj.Atom 0)
       , Object HomFused (FObj.Tensor a ('FObj.Atom 0))
       )
    => HomFused a (FObj.Tensor a ('FObj.Atom 0))
  coidr = HomFused (idMorFused @(FuseSym a))

instance Braided HomFused FObj.Tensor where
  braid = undefined

--------------------------------------------------------------------------------
-- Fused associator primitives (3-leaf) and FuseHom-in-one-leg naturality
--
-- Unfused Mac Lane on four factors factors as:
--
-- @
-- (a⊗b) ⊗ (b⊗c)  ─rassoc→  a ⊗ (b ⊗ (b⊗c))  ─id⊗lassoc→  a ⊗ ((b⊗b) ⊗ c)
-- @
--
-- Fused (no inverse CG / no full tensor product):
--
-- @
-- fmoveComposeFused =
--   fuseMapRight (fmoveInv @b @b @c) ∘ fmove @a @b @(FuseHom b c)
-- @
--
-- 'fuseMapRight' is naturality of @FuseHom a (-)@ on /intertwiners/ (e.g. F-moves),
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
-- Hom-compose still uses 'FuseHom' (@'Prod@ cups); wire 'FuseFlat' there next.
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
-- Flat 'composeMorFused' analogues:
--   tensorComposeTrees → fmoveComposeTrees → cupComposeTrees → unitorComposeTrees
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

-- | 3-leaf F-move on fusion-tree spines.
class CanFmoveTrees (a :: TreeRep) (b :: TreeRep) (c :: TreeRep) where
  fmoveTrees
    :: TreeV (FuseAssocL a b c)
    -> TreeV (FuseAssocR a b c)
  fmoveInvTrees
    :: TreeV (FuseAssocR a b c)
    -> TreeV (FuseAssocL a b c)

-- | Standard basis vector of @C 2@.
c2Basis :: Int -> C 2
c2Basis i =
  unsafeFromArray $
    VS.fromList
      [ if j == i then 1 :+ 0 else 0
      | j <- [0 :: Int, 1]
      ]

c1Basis :: C 1
c1Basis = unsafeFromArray (VS.fromList [1 :+ 0])

c3Basis :: Int -> C 3
c3Basis i =
  unsafeFromArray $
    VS.fromList
      [ if j == i then 1 :+ 0 else 0
      | j <- [0 :: Int, 1, 2]
      ]

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

-- | Left-leg slices of @C 2 ⊗ C d@ (same layout as 'unpackTwoCopy').
contractC2Left
  :: forall d
   . ( KnownNat d
     , KnownNat (2 * d)
     , HilbertSpace (C 2)
     , InnerSpace (C 2)
     , Scalar (C 2) ~ Complex Double
     , TensorSpace (C d)
     , AdditiveGroup (C d)
     )
  => C 2
  -> C 2 ⊗ C d
  -> C d
contractC2Left e sec =
  let (a0, a1) = unpackTwoCopy @d sec
      c0 = e <.> c2Basis 0
      c1 = e <.> c2Basis 1
   in (c0 *^ a0) ^+^ (c1 *^ a1)

-- | @F^{111}_1@ on multiplicity @[0,2]@ (typed @C 2@, no buffers).
fMult111d1 :: Bool -> C 2 +> C 2
fMult111d1 inv =
  arr $ LinearFunction $ \v ->
    let c0 = c2Basis 0 <.> v
        c1 = c2Basis 1 <.> v
     in if inv
          then
            -- domain f=[0,2], codomain e=[0,2]; out_e = Σ_f F⁻¹_ef in_f
            let o0 =
                  fromMaybe 0 (lookup 0 (su2FSymbol True 1 1 1 1 0)) * c0
                    + fromMaybe 0 (lookup 2 (su2FSymbol True 1 1 1 1 0)) * c1
                o1 =
                  fromMaybe 0 (lookup 0 (su2FSymbol True 1 1 1 1 2)) * c0
                    + fromMaybe 0 (lookup 2 (su2FSymbol True 1 1 1 1 2)) * c1
             in (o0 *^ c2Basis 0) ^+^ (o1 *^ c2Basis 1)
          else
            let o0 =
                  fromMaybe 0 (lookup 0 (su2FSymbol False 1 1 1 1 0)) * c0
                    + fromMaybe 0 (lookup 0 (su2FSymbol False 1 1 1 1 2)) * c1
                o1 =
                  fromMaybe 0 (lookup 2 (su2FSymbol False 1 1 1 1 0)) * c0
                    + fromMaybe 0 (lookup 2 (su2FSymbol False 1 1 1 1 2)) * c1
             in (o0 *^ c2Basis 0) ^+^ (o1 *^ c2Basis 1)

-- | @F^{111}_3@ on singleton multiplicity (@C 1@).
fMult111d3 :: Bool -> C 1 +> C 1
fMult111d3 inv =
  arr $ LinearFunction $ \v ->
    let amp =
          if inv
            then fromMaybe 0 (lookup 2 (su2FSymbol True 1 1 1 3 2))
            else fromMaybe 0 (lookup 2 (su2FSymbol False 1 1 1 3 2))
        c = c1Basis <.> v
     in (amp * c) *^ c1Basis

packFlat111 :: (C 2, (C 2, C 4)) -> Flat111
packFlat111 (v0, (v2, v3)) =
  (packTwoCopy @2 v0 v2, c1Basis ⊗ v3)

unpackFlat111 :: Flat111 -> (C 2, (C 2, C 4))
unpackFlat111 (sec1, sec3) =
  case unpackTwoCopy @2 sec1 of
    (v0, v2) -> (v0, (v2, fuseBond @1 @4 $ sec3))

fmoveFlat111 :: Flat111 -> Flat111
fmoveFlat111 (sec1, sec3) =
  ( (fMult111d1 False ⊗^ id) $ sec1
  , (fMult111d3 False ⊗^ id) $ sec3
  )

fmoveInvFlat111 :: Flat111 -> Flat111
fmoveInvFlat111 (sec1, sec3) =
  ( (fMult111d1 True ⊗^ id) $ sec1
  , (fMult111d3 True ⊗^ id) $ sec3
  )

-- | Triple-leaf F-move via typed F-blocks (@F ⊗ id@), no 'VS.Vector'.
fmoveTrees111 :: TreeV AssocL111 -> TreeV AssocR111
fmoveTrees111 =
  vToTreeV @AssocR111
    . unpackFlat111
    . fmoveFlat111
    . packFlat111
    . treeVToV @AssocL111

fmoveInvTrees111 :: TreeV AssocR111 -> TreeV AssocL111
fmoveInvTrees111 =
  vToTreeV @AssocL111
    . unpackFlat111
    . fmoveInvFlat111
    . packFlat111
    . treeVToV @AssocR111

-- | Trivial @0⊗0⊗0@: F is id on the single block.
fmoveTrees000 :: TreeV AssocL000 -> TreeV AssocR000
fmoveTrees000 = vToTreeV @AssocR000 . treeVToV @AssocL000

fmoveInvTrees000 :: TreeV AssocR000 -> TreeV AssocL000
fmoveInvTrees000 = vToTreeV @AssocL000 . treeVToV @AssocR000

instance CanFmoveTrees '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 1] where
  fmoveTrees = fmoveTrees111
  fmoveInvTrees = fmoveInvTrees111

instance CanFmoveTrees '[ 'Leaf 0] '[ 'Leaf 0] '[ 'Leaf 0] where
  fmoveTrees = fmoveTrees000
  fmoveInvTrees = fmoveInvTrees000

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
-- Concrete Leaf-½ Hom-compose ladder (viability destub)
--------------------------------------------------------------------------------

type Leaf1 = '[ 'Leaf 1]

type Leaf0 = '[ 'Leaf 0]

type Hom11 =
  '[ 'Node 0 ('Leaf 1) ('Leaf 1)
   , 'Node 2 ('Leaf 1) ('Leaf 1)
   ]

-- | Trivial Hom on @j=0@ (single singlet channel).
type Hom00 =
  '[ 'Node 0 ('Leaf 0) ('Leaf 0)]

type Dom000 =
  '[ 'Node 0 ('Node 0 ('Leaf 0) ('Leaf 0)) ('Node 0 ('Leaf 0) ('Leaf 0))]

type CupR000 =
  '[ 'Node 0 ('Leaf 0) ('Node 0 ('Node 0 ('Leaf 0) ('Leaf 0)) ('Leaf 0))]

type Dom111 =
  '[ 'Node 0 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Node 0 ('Leaf 1) ('Leaf 1))
   , 'Node 2 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Node 2 ('Leaf 1) ('Leaf 1))
   , 'Node 2 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Node 0 ('Leaf 1) ('Leaf 1))
   , 'Node 0 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Node 2 ('Leaf 1) ('Leaf 1))
   , 'Node 2 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Node 2 ('Leaf 1) ('Leaf 1))
   , 'Node 4 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Node 2 ('Leaf 1) ('Leaf 1))
   ]

type Mid111 =
  '[ 'Node 0 ('Leaf 1) ('Node 1 ('Leaf 1) ('Node 0 ('Leaf 1) ('Leaf 1)))
   , 'Node 2 ('Leaf 1) ('Node 1 ('Leaf 1) ('Node 0 ('Leaf 1) ('Leaf 1)))
   , 'Node 0 ('Leaf 1) ('Node 1 ('Leaf 1) ('Node 2 ('Leaf 1) ('Leaf 1)))
   , 'Node 2 ('Leaf 1) ('Node 1 ('Leaf 1) ('Node 2 ('Leaf 1) ('Leaf 1)))
   , 'Node 2 ('Leaf 1) ('Node 3 ('Leaf 1) ('Node 2 ('Leaf 1) ('Leaf 1)))
   , 'Node 4 ('Leaf 1) ('Node 3 ('Leaf 1) ('Node 2 ('Leaf 1) ('Leaf 1)))
   ]

type CupR111 =
  '[ 'Node 0 ('Leaf 1) ('Node 1 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Leaf 1))
   , 'Node 2 ('Leaf 1) ('Node 1 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Leaf 1))
   , 'Node 0 ('Leaf 1) ('Node 1 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 1))
   , 'Node 2 ('Leaf 1) ('Node 1 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 1))
   , 'Node 2 ('Leaf 1) ('Node 3 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 1))
   , 'Node 4 ('Leaf 1) ('Node 3 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 1))
   ]

type Hom16Rep = '[ '(0, 2), '(2, 3), '(4, 1)]
type Assoc8Rep = '[ '(1, 2), '(3, 1)]

type FlatHom16 =
  (C 2 ⊗ C 1, (C 3 ⊗ C 3, C 1 ⊗ C 5))

type ToVHom16 = (C 1, (C 3, (C 1, (C 3, (C 3, C 5)))))
type ToVDom111 = (C 1, (C 3, (C 3, (C 1, (C 3, C 5)))))

packThreeCopy
  :: forall d
   . ( KnownNat d
     , AdditiveGroup (C 3 ⊗ C d)
     , TensorSpace (C d)
     , TensorSpace (C 3)
     )
  => C d
  -> C d
  -> C d
  -> C 3 ⊗ C d
packThreeCopy v0 v1 v2 =
  (c3Basis 0 ⊗ v0) ^+^ (c3Basis 1 ⊗ v1) ^+^ (c3Basis 2 ⊗ v2)

unpackThreeCopy
  :: forall d
   . ( KnownNat d
     , KnownNat (3 * d)
     , TensorSpace (C d)
     )
  => C 3 ⊗ C d
  -> (C d, C d, C d)
unpackThreeCopy sec =
  let buf = toArray (fuseBond @3 @d $ sec)
      di = fromIntegral (natVal (Proxy @d)) :: Int
   in ( unsafeFromArray (VS.take di buf)
      , unsafeFromArray (VS.take di (VS.drop di buf))
      , unsafeFromArray (VS.drop (2 * di) buf)
      )

-- | Left-leg slices of @C 3 ⊗ C d@ (same layout as 'unpackThreeCopy').
contractC3Left
  :: forall d
   . ( KnownNat d
     , KnownNat (3 * d)
     , HilbertSpace (C 3)
     , InnerSpace (C 3)
     , Scalar (C 3) ~ Complex Double
     , TensorSpace (C d)
     , AdditiveGroup (C d)
     )
  => C 3
  -> C 3 ⊗ C d
  -> C d
contractC3Left e sec =
  let (a0, a1, a2) = unpackThreeCopy @d sec
      c0 = e <.> c3Basis 0
      c1 = e <.> c3Basis 1
      c2 = e <.> c3Basis 2
   in (c0 *^ a0) ^+^ (c1 *^ a1) ^+^ (c2 *^ a2)

packDom111 :: ToVDom111 -> FlatHom16
packDom111 (a0, (a2, (b2, (b0, (c2, c4))))) =
  (packTwoCopy @1 a0 b0, (packThreeCopy @3 a2 b2 c2, c1Basis ⊗ c4))

packMid111 :: ToVHom16 -> FlatHom16
packMid111 (a0, (a2, (b0, (b2, (c2, c4))))) =
  (packTwoCopy @1 a0 b0, (packThreeCopy @3 a2 b2 c2, c1Basis ⊗ c4))

unpackMid111 :: FlatHom16 -> ToVHom16
unpackMid111 (sec0, (sec2, sec4)) =
  case (unpackTwoCopy @1 sec0, unpackThreeCopy @3 sec2) of
    ((a0, b0), (a2, b2, c2)) ->
      (a0, (a2, (b0, (b2, (c2, fuseBond @1 @5 $ sec4)))))

-- | @ToCG@ boundary: sector flats concatenated into @C 16@ (Schur layout).
flattenHom16 :: FlatHom16 -> C 16
flattenHom16 (s0, (s2, s4)) =
  unsafeFromArray (toArray s0 VS.++ toArray s2 VS.++ toArray s4)

unflattenHom16 :: C 16 -> FlatHom16
unflattenHom16 v =
  let buf = toArray v
   in ( unsafeFromArray (VS.take 2 buf)
      , ( unsafeFromArray (VS.slice 2 9 buf)
        , unsafeFromArray (VS.drop 11 buf)
        )
      )

-- | Factor a pure tensor @ℓ ⊗ a@ in @C 2 ⊗ C d@ (scale in @ℓ@, unit @a@).
splitSeparable2
  :: forall d
   . ( KnownNat d
     , KnownNat (2 * d)
     , HilbertSpace (C 2)
     , HilbertSpace (C d)
     , InnerSpace (C 2)
     , InnerSpace (C d)
     , Scalar (C 2) ~ Complex Double
     , Scalar (C d) ~ Complex Double
     , TensorSpace (C d)
     , AdditiveGroup (C 2)
     , AdditiveGroup (C d)
     )
  => C 2 ⊗ C d
  -> (C 2, C d)
splitSeparable2 p =
  let (a0, a1) = unpackTwoCopy @d p
      n0 = magnitude (a0 <.> a0)
      n1 = magnitude (a1 <.> a1)
   in if n0 < 1e-30 && n1 < 1e-30
        then (zeroV, zeroV)
        else if n0 >= n1
          then
            let s = sqrt n0
                assocU = ((1 / s) :+ 0) *^ a0
                leaf =
                  ((s :+ 0) *^ c2Basis 0)
                    ^+^ ((a1 <.> assocU) *^ c2Basis 1)
             in (leaf, assocU)
          else
            let s = sqrt n1
                assocU = ((1 / s) :+ 0) *^ a1
                leaf =
                  ((a0 <.> assocU) *^ c2Basis 0)
                    ^+^ ((s :+ 0) *^ c2Basis 1)
             in (leaf, assocU)

-- | Unfuse Mid by CG-channel adjoints → nested 'TensorTrees Leaf1 AssocR111'.
-- Mid = Fuse(Leaf1, AssocR111): pairs use assoc roots @[1,1,3]@.
-- Shared left leaf is recovered once; each assoc factor is the left-contraction
-- against that leaf (so refuse reconstitutes the pure tensor).
--
-- Only valid for Mid in the image of 'fuseTensorTrees' (rank-1 @Leaf ⊗ Assoc@).
-- General Mid (e.g. after 'fmoveOuter111') needs 'fuseMapRightFinv111'.
unfuseMid111 :: TreeV Mid111 -> TensorTrees Leaf1 AssocR111
unfuseMid111
  (TCons v0 (TCons v2 (TCons w0 (TCons w2 (TCons u2 (TCons u4 TNil)))))) =
    let t0 =
          (unfuseCGChannel @1 @1 @0 $ v0)
            ^+^ (unfuseCGChannel @1 @1 @2 $ v2)
        t1 =
          (unfuseCGChannel @1 @1 @0 $ w0)
            ^+^ (unfuseCGChannel @1 @1 @2 $ w2)
        t2 =
          (unfuseCGChannel @1 @3 @2 $ u2)
            ^+^ (unfuseCGChannel @1 @3 @4 $ u4)
        (leafRaw, _) = splitSeparable2 @2 t0
        n2 = magnitude (leafRaw <.> leafRaw)
        leafU =
          if n2 < 1e-30
            then c2Basis 0
            else ((1 / sqrt n2) :+ 0) *^ leafRaw
        a0 = contractC2Left @2 leafU t0
        a1 = contractC2Left @2 leafU t1
        a2 = contractC2Left @4 leafU t2
     in TensorTrees
          (TCons leafU TNil)
          (TCons a0 (TCons a1 (TCons a2 TNil)))

-- | @Assoc8Rep@ flat (@C 8@) ↔ 'Flat111' (same Kronecker layout as 'fuseSU2Flat').
flat111ToAssoc8 :: Flat111 -> C 8
flat111ToAssoc8 (sec1, sec3) =
  unsafeFromArray (toArray sec1 VS.++ toArray sec3)

assoc8ToFlat111 :: C 8 -> Flat111
assoc8ToFlat111 v =
  let buf = toArray v
   in (unsafeFromArray (VS.take 4 buf), unsafeFromArray (VS.drop 4 buf))

-- | @F⁻¹@ on the Assoc-½⊗½⊗½ factor as @C 8@ (@F ⊗ id@ via 'Flat111').
fmoveInvAssoc8 :: C 8 -> C 8
fmoveInvAssoc8 =
  flat111ToAssoc8 . fmoveInvFlat111 . assoc8ToFlat111

-- | @Fuse(id, F-inv)@ on general Mid: unfuse @½ ⊗ Assoc8@ → @id ⊗ F⁻¹@ → refuse.
--
-- Must not go through rank-1 'TensorTrees' / 'splitSeparable2': Hom-compose Mid
-- (e.g. singlet channel alone) is entangled across the leaf\/assoc cut.
fuseMapRightFinv111 :: TreeV Mid111 -> TreeV CupR111
fuseMapRightFinv111 tv =
  let mid16 = flattenHom16 (packMid111 (treeVToV @Mid111 tv))
      unfused = unfuseLeafAssocHalf $ mid16
      mapped =
        (id ⊗^ arr (LinearFunction fmoveInvAssoc8)) $ unfused
      out16 = fuseLeafAssocHalf $ mapped
   in vToTreeV @CupR111 (unpackMid111 (unflattenHom16 out16))

-- | Rank-1 special case: 'unfuseMid111' → map F-inv → 'fuseTensorTrees'.
fuseMapRightFinvProduct111 :: TreeV Mid111 -> TreeV CupR111
fuseMapRightFinvProduct111 =
  fuseTensorTrees @Leaf1 @AssocL111
    . mapTensorTreesRight fmoveInvTrees111
    . unfuseMid111

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

-- | Outer F via typed Schur @ToCG@ on @C 16@ (@flattenHom16@ is the Schur boundary).
fmoveOuter111 :: TreeV Dom111 -> TreeV Mid111
fmoveOuter111 tv =
  let mor =
        fSymbolHomSU2
          (Proxy @'[ '(1, 1)])
          (Proxy @'[ '(1, 1)])
          (Proxy @'[ '(0, 1), '(2, 1)])
      ToCG out =
        getLinearFunction (intertwinerLinearG mor) $
          ToCG (flattenHom16 (packDom111 (treeVToV @Dom111 tv)))
   in vToTreeV @Mid111 (unpackMid111 (unflattenHom16 out))

--------------------------------------------------------------------------------
-- Tree Hom composition (analogues of 'composeMorFused' steps)
--------------------------------------------------------------------------------

-- | Step 1: CG-fuse two Hom tree-spines via 'fuseTreeRepTerm'.
tensorComposeTrees
  :: forall a b c
   . ( KnownTreeRep (FuseTreeRep a b)
     , KnownTreeRep (FuseTreeRep b c)
     , FuseTreeRepTermC (FuseTreeRep a b) (FuseTreeRep b c)
     )
  => TreeV (FuseTreeRep a b)
  -> TreeV (FuseTreeRep b c)
  -> TreeV (FuseTreeRep (FuseTreeRep a b) (FuseTreeRep b c))
tensorComposeTrees = fuseTreeRepTerm @(FuseTreeRep a b) @(FuseTreeRep b c)

-- | Step 2: cup-ready association. Concrete spines via 'CanFmoveComposeTrees'.
class CanFmoveComposeTrees (a :: TreeRep) (b :: TreeRep) (c :: TreeRep) where
  fmoveComposeTrees
    :: TreeV (FuseTreeRep (FuseTreeRep a b) (FuseTreeRep b c))
    -> TreeV (FuseTreeRep a (FuseTreeRep (FuseTreeRep b b) c))

-- | @fmoveOuter111 ∘ fuseMapRightFinv111@ for Leaf-½ Hom compose.
instance CanFmoveComposeTrees '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 1] where
  fmoveComposeTrees = fmoveComposeTrees111

fmoveComposeTrees111 :: TreeV Dom111 -> TreeV CupR111
fmoveComposeTrees111 = fuseMapRightFinv111 . fmoveOuter111

-- | @0⊗0⊗0@: outer F and Fuse-right are id on the single @C 1@ channel
-- (Dom and CupR forget to the same payload).
instance CanFmoveComposeTrees '[ 'Leaf 0] '[ 'Leaf 0] '[ 'Leaf 0] where
  fmoveComposeTrees = fmoveComposeTrees000

fmoveComposeTrees000 :: TreeV Dom000 -> TreeV CupR000
fmoveComposeTrees000 = vToTreeV @CupR000 . treeVToV @Dom000

-- | Step 3: cup middle singlets. Concrete spines via 'CanCupComposeTrees'.
class CanCupComposeTrees (a :: TreeRep) (b :: TreeRep) (c :: TreeRep) where
  cupComposeTrees
    :: TreeV (FuseTreeRep a (FuseTreeRep (FuseTreeRep b b) c))
    -> TreeV (FuseTreeRep a (FuseTreeRepU TreeUnit c))

instance CanCupComposeTrees '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 1] where
  cupComposeTrees = cupComposeTrees111

instance CanCupComposeTrees '[ 'Leaf 0] '[ 'Leaf 0] '[ 'Leaf 0] where
  cupComposeTrees = cupComposeTrees000

-- | Cup on an explicit 'CupMiddleTrees'-shaped spine (viability probe).
cupMiddleTreesTerm
  :: forall ts
   . CupMiddleTreesTerm ts
  => TreeV ts
  -> TreeV (CupMiddleTrees ts)
cupMiddleTreesTerm = cupMiddleTreesTermGo

class CupMiddleTreesTerm (ts :: TreeRep) where
  cupMiddleTreesTermGo :: TreeV ts -> TreeV (CupMiddleTrees ts)

instance CupMiddleTreesTerm '[] where
  cupMiddleTreesTermGo TNil = TNil

-- Concrete probe: one singlet-middle channel then nil.
instance CupMiddleTreesTerm
  '[ 'Node 1 ('Leaf 1) ('Node 1 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Leaf 1))]
  where
  cupMiddleTreesTermGo (TCons v TNil) =
    TCons @('Node 1 ('Leaf 1) ('Leaf 1)) v TNil

-- | Full cup-ready Leaf-½ spine: keep the two singlet-middle channels.
instance CupMiddleTreesTerm CupR111 where
  cupMiddleTreesTermGo
    (TCons v0 (TCons v2 (TCons _ (TCons _ (TCons _ (TCons _ TNil)))))) =
      TCons @('Node 0 ('Leaf 1) ('Leaf 1)) v0 $
        TCons @('Node 2 ('Leaf 1) ('Leaf 1)) v2 TNil

-- | Cup singlet middles on 'CupR111' → 'Hom11'.
--
-- Middle cup on @½⊗½ → 0@ evaluates to @FS(½)·dim(½) = (-1)·2 = -2@
-- (same factor on every outer channel; middle is always the trivial @b⊗b@).
cupComposeTrees111 :: TreeV CupR111 -> TreeV Hom11
cupComposeTrees111 tv =
  case cupMiddleTreesTerm @CupR111 tv of
    TCons v0 (TCons v2 TNil) ->
      let s = ((-2) :+ 0)
       in TCons @('Node 0 ('Leaf 1) ('Leaf 1)) (s *^ v0) $
            TCons @('Node 2 ('Leaf 1) ('Leaf 1)) (s *^ v2) TNil
    _ -> error "cupComposeTrees111: CupMiddleTrees CupR111 shape"

-- | Cup on trivial @j=0@: @FS(0)·dim(0) = 1@.
cupComposeTrees000 :: TreeV CupR000 -> TreeV Hom00
cupComposeTrees000 (TCons v TNil) =
  TCons @('Node 0 ('Leaf 0) ('Leaf 0)) v TNil

-- | Full Leaf-0 Hom compose.
composeMorTrees000
  :: TreeV Hom00
  -> TreeV Hom00
  -> TreeV Hom00
composeMorTrees000 f g =
  cupComposeTrees000 $
    fmoveComposeTrees000 $
      fuseTreeRepTerm @Hom00 @Hom00 f g

idHom00 :: TreeV Hom00
idHom00 = TCons @('Node 0 ('Leaf 0) ('Leaf 0)) (konst 1) TNil

checkComposeMorTrees000 :: Bool
checkComposeMorTrees000 =
  let f = TCons @('Node 0 ('Leaf 0) ('Leaf 0)) (konst 0.4) TNil
      close u v =
        let d = treeVToV @Hom00 u ^-^ treeVToV @Hom00 v
         in magnitude (d <.> d) < 1e-12
   in close (composeMorTrees000 idHom00 idHom00) idHom00
        && close (composeMorTrees000 f idHom00) f
        && close (composeMorTrees000 idHom00 f) f

unitorComposeTrees
  :: forall a c
   . (FuseTreeRepU TreeUnit c ~ c)
  => TreeV (FuseTreeRep a (FuseTreeRepU TreeUnit c))
  -> TreeV (FuseTreeRep a c)
unitorComposeTrees = id

-- | Hom compose on spines with concrete F-move \/ cup instances.
composeMorTrees
  :: forall a b c
   . ( KnownTreeRep (FuseTreeRep a b)
     , KnownTreeRep (FuseTreeRep b c)
     , FuseTreeRepTermC (FuseTreeRep a b) (FuseTreeRep b c)
     , FuseTreeRepU TreeUnit c ~ c
     , CanFmoveComposeTrees a b c
     , CanCupComposeTrees a b c
     )
  => TreeV (FuseTreeRep a b)
  -> TreeV (FuseTreeRep b c)
  -> TreeV (FuseTreeRep a c)
composeMorTrees f g =
  unitorComposeTrees @a @c
    ( cupComposeTrees @a @b @c
        ( fmoveComposeTrees @a @b @c
            (tensorComposeTrees @a @b @c f g)
        )
    )

-- | Full Leaf-½ Hom compose on concrete spines (no open 'FuseTreeRep' in the body).
composeMorTrees111
  :: TreeV Hom11
  -> TreeV Hom11
  -> TreeV Hom11
composeMorTrees111 f g =
  cupComposeTrees111 $
    fmoveComposeTrees111 $
      fuseTreeRepTerm @Hom11 @Hom11 f g

-- | Singlet-only identity in 'Hom11' (@j=0@ channel).
idHom11 :: TreeV Hom11
idHom11 =
  TCons @('Node 0 ('Leaf 1) ('Leaf 1)) (konst 1) $
    TCons @('Node 2 ('Leaf 1) ('Leaf 1)) zeroV TNil

approxHom11 :: TreeV Hom11 -> TreeV Hom11 -> Bool
approxHom11 u v =
  case (treeVToV @Hom11 u, treeVToV @Hom11 v) of
    ((a0, a2), (b0, b2)) ->
      let close x y =
            let d = x ^-^ y
             in magnitude (d <.> d) < 1e-12
       in close a0 b0 && close a2 b2

-- | 'composeMorTrees111': @id∘id ≈ id@ and left/right units on a sample Hom.
checkComposeMorTrees111 :: Bool
checkComposeMorTrees111 =
  let f =
        TCons @('Node 0 ('Leaf 1) ('Leaf 1)) (konst 0.3) $
          TCons @('Node 2 ('Leaf 1) ('Leaf 1)) (konst 0.7) TNil
      idid = composeMorTrees111 idHom11 idHom11
      fid = composeMorTrees111 f idHom11
      idf = composeMorTrees111 idHom11 f
   in approxHom11 idid idHom11
        && approxHom11 fid f
        && approxHom11 idf f

fuseMapRight
  :: forall a q q'
   . (ToVSpine q -> ToVSpine q')
  -> ToVSpine (FuseHom a q)
  -> ToVSpine (FuseHom a q')
fuseMapRight = undefined

fuseMapLeft
  :: forall a a' b
   . (ToVSpine a -> ToVSpine a')
  -> ToVSpine (FuseHom a b)
  -> ToVSpine (FuseHom a' b)
fuseMapLeft = undefined

--------------------------------------------------------------------------------
-- Fused composition on coalesced 'Rep' spines (@ToVSpine (FuseHom · ·)@)
--
--   composeMorFused f g =
--     unitor ∘ cup ∘ fmoveComposeFused ∘ fuseExpr(f, g)
--
-- Status:
--   1. tensorComposeFused — done ('fuseExpr')
--   2. fmoveComposeFused  — 'fuseMapRight fmoveInv ∘ fmove' (primitives stubbed)
--   3. cupComposeFused    — stub (middle cup after cup-ready association)
--   4. unitorComposeFused — done ('FuseRep' @Unit ⊗ c = c@)
--------------------------------------------------------------------------------

-- | Step 1: CG-fuse the two Hom spines
-- @FuseHom (FuseHom a b) (FuseHom b c)@.
tensorComposeFused
  :: forall a b c
   . ( KnownAtomRep (FuseHom a b)
     , KnownAtomRep (FuseHom b c)
     , FuseAtomSpinesTerm (FuseHom a b) (FuseHom b c)
     , KnownSymRep (FuseAtomSpines (FuseHom a b) (FuseHom b c))
     , CoalesceSpine (FuseAtomSpines (FuseHom a b) (FuseHom b c))
     , KnownSymRep (FuseHom (FuseHom a b) (FuseHom b c))
     )
  => ToVSpine (FuseHom a b)
  -> ToVSpine (FuseHom b c)
  -> ToVSpine (FuseHom (FuseHom a b) (FuseHom b c))
tensorComposeFused f g =
  repVToV @(FuseHom (FuseHom a b) (FuseHom b c)) $
    fuseExpr
      @(FuseHom a b)
      @(FuseHom b c)
      (vToRepV @(FuseHom a b) f)
      (vToRepV @(FuseHom b c) g)

-- | Step 2: cup-ready association (no R-move). Factors as Mac Lane on four legs:
--
-- @
-- Fuse(Fuse(a,b), Fuse(b,c))
--   ─fmove @a @b @(FuseHom b c)→  Fuse(a, Fuse(b, Fuse(b,c)))
--   ─fuseMapRight (fmoveInv @b @b @c)→  Fuse(a, Fuse(Fuse(b,b), c))
-- @
--
-- Blocker: Hom-compose pipeline is still on 'FuseHom' (@'Prod@ cups); atom
-- 'fmove' lives on 'FuseFlat'. Reconcile before de-stubbing.
fmoveComposeFused
  :: forall a b c
   . ToVSpine (FuseHom (FuseHom a b) (FuseHom b c))
  -> ToVSpine (FuseHom a (FuseHom (FuseHom b b) c))
fmoveComposeFused = undefined

-- | Step 3: cup the middle @FuseHom b b → Unit@:
-- @Fuse(a, Fuse(Fuse(b,b), c)) → Fuse(a, FuseRep(Unit, c))@.
--
-- Blocker: 'FuseHom'\/'Coalesce' forget the fusion tree into a flat 'Rep', so
-- there is no nested middle factor to hand to 'cupMiddleFused'. Filling this
-- needs either a structured (non-flat) intermediate from the F-move, or a
-- singlet projection expressed in the coalesced multiplicity basis.
cupComposeFused
  :: forall a b c
   . ToVSpine (FuseHom a (FuseHom (FuseHom b b) c))
  -> ToVSpine (FuseHom a (FuseRep Unit c))
cupComposeFused = undefined

-- | Step 4: 'FuseRep' left unitor on the right factor
-- @Fuse(a, FuseRep(Unit, c)) → Fuse(a, c)@.
unitorComposeFused
  :: forall a c
   . (FuseRep Unit c ~ c)
  => ToVSpine (FuseHom a (FuseRep Unit c))
  -> ToVSpine (FuseHom a c)
unitorComposeFused = id

-- | Fused Hom composition:
-- @unitor ∘ cup ∘ fmove ∘ fuseExpr(f, g)@.
composeMorFused
  :: forall a b c
   . ( KnownAtomRep (FuseHom a b)
     , KnownAtomRep (FuseHom b c)
     , FuseAtomSpinesTerm (FuseHom a b) (FuseHom b c)
     , KnownSymRep (FuseAtomSpines (FuseHom a b) (FuseHom b c))
     , CoalesceSpine (FuseAtomSpines (FuseHom a b) (FuseHom b c))
     , KnownSymRep (FuseHom (FuseHom a b) (FuseHom b c))
     , FuseRep Unit c ~ c
     )
  => ToVSpine (FuseHom a b)
  -> ToVSpine (FuseHom b c)
  -> ToVSpine (FuseHom a c)
composeMorFused f g =
  unitorComposeFused @a @c
    ( cupComposeFused @a @b @c
        ( fmoveComposeFused @a @b @c
            (tensorComposeFused @a @b @c f g)
        )
    )

-- | Obj-indexed wrapper around 'composeMorFused'.
composeHomFused
  :: forall a b c
   . ( Object HomFused a
     , Object HomFused b
     , Object HomFused c
     , KnownAtomRep (FuseHom (FuseSym a) (FuseSym b))
     , KnownAtomRep (FuseHom (FuseSym b) (FuseSym c))
     , FuseAtomSpinesTerm
         (FuseHom (FuseSym a) (FuseSym b))
         (FuseHom (FuseSym b) (FuseSym c))
     , KnownSymRep
         ( FuseAtomSpines
             (FuseHom (FuseSym a) (FuseSym b))
             (FuseHom (FuseSym b) (FuseSym c))
         )
     , CoalesceSpine
         ( FuseAtomSpines
             (FuseHom (FuseSym a) (FuseSym b))
             (FuseHom (FuseSym b) (FuseSym c))
         )
     , KnownSymRep
         ( FuseHom
             (FuseHom (FuseSym a) (FuseSym b))
             (FuseHom (FuseSym b) (FuseSym c))
         )
     , FuseRep Unit (FuseSym c) ~ FuseSym c
     )
  => HomFused b c
  -> HomFused a b
  -> HomFused a c
composeHomFused (HomFused g) (HomFused f) =
  HomFused (composeMorFused @(FuseSym a) @(FuseSym b) @(FuseSym c) f g)

--------------------------------------------------------------------------------
-- Fused cups on @FilterTrivial (FuseHom r r)@ (dual≅primal; not Hom packing)
--------------------------------------------------------------------------------

-- | Cup the CG-fused middle @FuseHom b b@ after projecting to singlets.
cupMiddleFused
  :: forall b
   . ( KnownAtomRep b
     , ProjectToSymmetric (FuseHom b b)
     , CupTrivial (FilterTrivial (FuseHom b b))
     , KnownSymRep (FuseHom b b)
     , KnownSymRep (FilterTrivial (FuseHom b b))
     )
  => ToVSpine (FuseHom b b)
  -> ToVSpine Unit
cupMiddleFused mid =
  cupFusedOnSpine @b $
    repVToV @(FilterTrivial (FuseHom b b)) $
      projectToSymmetric $
        vToRepV @(FuseHom b b) mid

-- | Middle step retained from the old fused-cup-on-unfused path.
fuseMiddleOnCup
  :: forall r
   . ( KnownAtomRep r
     , FuseAtomSpinesTerm r r
     , KnownSymRep (FuseAtomSpines r r)
     , CoalesceSpine (FuseAtomSpines r r)
     , KnownSymRep (FuseHom r r)
     , ProjectToSymmetric (FuseHom r r)
     , KnownSymRep (FilterTrivial (FuseHom r r))
     , LinearSpace (ToVSpine r)
     , LinearSpace (DualVector (ToVSpine r))
     , LinearSpace (ToVSpine (FuseHom r r))
     , Scalar (ToVSpine r) ~ Complex Double
     , Scalar (DualVector (ToVSpine r)) ~ Complex Double
     , Scalar (ToVSpine (FuseHom r r))
         ~ Complex Double
     , TensorSpace (DualVector (ToVSpine r))
     )
  => (ToVSpine r ⊗ DualVector (ToVSpine r))
  -> ToVSpine (FilterTrivial (FuseHom r r))
fuseMiddleOnCup t =
  let undualMap =
        arr (LinearFunction (undualSpine @r))
          :: DualVector (ToVSpine r) +> ToVSpine r
      ηPrimal = (id ⊗^ undualMap) $ t
   in repVToV @(FilterTrivial (FuseHom r r)) $
        projectToSymmetric (fuseExprTensor @r ηPrimal)

-- | Fused cup on a projected singlet spine → @Unit@.
cupFusedOnSpine
  :: forall r
   . ( KnownAtomRep r
     , CupTrivial (FilterTrivial (FuseHom r r))
     , KnownSymRep (FilterTrivial (FuseHom r r))
     )
  => ToVSpine (FilterTrivial (FuseHom r r))
  -> ToVSpine Unit
cupFusedOnSpine s =
  repVToV @Unit (cupFused @r (vToRepV @(FilterTrivial (FuseHom r r)) s))

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
