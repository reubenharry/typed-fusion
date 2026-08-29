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
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Term-level symbolic SU(2) reps: singletons, 'RepV', fuse / coalesce / cup.
--
-- Type kinds and families live in 'Experiments.Symbolic.Expr' /
-- 'Experiments.Symbolic.TypeLevel'. Flat-buffer oracles:
-- 'Experiments.Symbolic.Reference'. Examples: 'Experiments.SymbolicExamples'.
--
-- Sectors are atom-keyed. Unfused tensor / dual spaces are 'RepExpr' values
-- ('rtensor' / 'rdual' / 'rmor'), reduced by 'fuseExpr' or paired by
-- 'cupUnfused' / 'cupRdual' (object @r ⊗ r*@); fused 'cupFused' / 'capFused'
-- on singlets after dual≅primal. Unfused Hom composition: 'composeMor'
-- (monoidal assoc + cup⊗id + unitor). 'repVToV' / 'vToRepV' round-trip a
-- 'KnownSymRep' spine through 'ToVSpine'.
module Experiments.Symbolic.Core where

import Data.Complex (Complex ((:+)))
import Data.Coerce (coerce)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (InnerSpace ((<.>)), Scalar, VectorSpace ((*^)))
import qualified Data.Vector.Storable as VS
import GHC.TypeLits (CmpNat, KnownNat, Nat, natVal, type (*), type (+))
import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..))
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
import Math.LinearMap.Coercion (uncurryLinearMap, (-+$=>))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, konst)
import Symmetry.Utils (Append)
import Symmetry.CG.SU2 (fuseCGChannel)
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

-- | Singleton for 'IrrepExpr' (bespoke; refines skolem irreps in spine walks).
data SIrrep (e :: IrrepExpr) where
  SAtomI
    :: forall j
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SIrrep ('Atom j)

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
  KnownSymRep ('( 'Atom j, 'AtomM m) ': rest)
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
  KnownSymRep ('( 'Atom j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
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
  KnownAtomRep ('( 'Atom j, 'AtomM m) ': rest)

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
  :: () => (e ~ 'Atom j, μ ~ 'AtomM m)
  => ToVSector ('Atom j) ('AtomM m)
  -> RepV rest
  -> RepV ('( 'Atom j, 'AtomM m) ': rest)
pattern RConsAtomAtomM v rs = RCons @('Atom j) @('AtomM m) v rs

pattern RConsAtomProd
  :: () => (e ~ 'Atom j, μ ~ 'Prod ('AtomM m) ('AtomM n))
  => ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n))
  -> RepV rest
  -> RepV ('( 'Atom j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
pattern RConsAtomProd v rs =
  RCons @('Atom j) @('Prod ('AtomM m) ('AtomM n)) v rs

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
      RCons @('Atom j) @('AtomM m) v RNil
    go (SRepCons (SAtomI @j) (SMultAtom @m) sRest@(SRepCons {})) (v, rest) =
      RCons @('Atom j) @('AtomM m) v (go sRest rest)
    go
      (SRepCons (SAtomI @j) (SMultProd (SMultAtom @m) (SMultAtom @n)) SRepNil)
      v =
        RCons @('Atom j) @('Prod ('AtomM m) ('AtomM n)) v RNil
    go
      (SRepCons (SAtomI @j) (SMultProd (SMultAtom @m) (SMultAtom @n)) sRest@(SRepCons {}))
      (v, rest) =
        RCons @('Atom j) @('Prod ('AtomM m) ('AtomM n)) v (go sRest rest)
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
  -> ToV ('RTensor ('RSum r) ('RSum q))
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
  -> ToVSector ('Atom j) ('AtomM m)
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
  -> ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n))
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
    repCons @('Atom j) @('AtomM m)
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
    repCons @('Atom j) @('Prod ('AtomM m) ('AtomM n))
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
  => DualVector (ToVSector ('Atom j) ('AtomM m))
  -> ToVSector ('Atom j) ('AtomM m)
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

-- | Sector algebra for CG fuse (spine walk is a plain fold over 'FuseRawSpine').
class FuseOneSector (e :: IrrepExpr) (μ :: MultExpr) where
  fuseOneSector :: ToVSector e μ -> RepV (FuseSector '(e, μ))

instance FuseOneSector ('Atom j) ('AtomM m) where
  fuseOneSector v = RCons @('Atom j) @('AtomM m) v RNil

instance FuseOneSector ('Atom j) ('Prod ('AtomM m) ('AtomM n)) where
  fuseOneSector v = RCons @('Atom j) @('Prod ('AtomM m) ('AtomM n)) v RNil

-- | Insert one sector into a coalesced spine (sort + merge on equal keys).
-- Instance heads stay concrete so 'CmpIrrep' reduces; bodies match 'RCons'.
class InsertSpine (e :: IrrepExpr) (μ :: MultExpr) (rs :: Rep) where
  insertSpine
    :: ToVSector e μ
    -> RepV rs
    -> RepV (InsertSector e μ rs)

instance InsertSpine e μ '[] where
  insertSpine sv RNil = RCons @e @μ sv RNil

instance
  ( CmpIrrep e ('Atom j) ~ ord
  , InsertCompared ord e μ ('Atom j) ('AtomM m) rest
  ) =>
  InsertSpine e μ ('( 'Atom j, 'AtomM m) ': rest)
  where
  insertSpine sv (RCons sv2 restR) =
    insertCompared @ord @e @μ @('Atom j) @('AtomM m) sv sv2 restR

instance
  ( CmpIrrep e ('Atom j) ~ ord
  , InsertCompared ord e μ ('Atom j) ('Prod ('AtomM m) ('AtomM n)) rest
  ) =>
  InsertSpine e μ ('( 'Atom j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  insertSpine sv (RCons sv2 restR) =
    insertCompared @ord @e @μ @('Atom j) @('Prod ('AtomM m) ('AtomM n)) sv sv2 restR

-- | Compare incoming sector @e@ against spine head @e2@ (@ord ~ CmpIrrep e e2@).
-- LT/GT are polymorphic; EQ merges the copy axes.
class InsertCompared
  (ord :: Ordering)
  (e :: IrrepExpr) (μ :: MultExpr)
  (e2 :: IrrepExpr) (μ2 :: MultExpr)
  (rest :: Rep)
 where
  insertCompared
    :: ToVSector e μ
    -> ToVSector e2 μ2
    -> RepV rest
    -> RepV (InsertSectorOrd ord e μ e2 μ2 rest)

instance InsertCompared 'LT e μ e2 μ2 rest where
  insertCompared sv sv2 restR =
    RCons @e @μ sv (RCons @e2 @μ2 sv2 restR)

instance (InsertSpine e μ rest) => InsertCompared 'GT e μ e2 μ2 rest where
  insertCompared sv sv2 restR =
    RCons @e2 @μ2 sv2 (insertSpine @e @μ sv restR)

-- | Flatten a sector's copy axis to @'AtomM (EvalMult μ)@.
class FlattenCopy (e :: IrrepExpr) (μ :: MultExpr) where
  flattenCopy
    :: ToVSector e μ
    -> ToVSector e ('AtomM (EvalMult μ))

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  ) =>
  FlattenCopy ('Atom j) ('AtomM m)
  where
  flattenCopy = id

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (m * n)
  , KnownNat (IrrepDim j)
  ) =>
  FlattenCopy ('Atom j) ('Prod ('AtomM m) ('AtomM n))
  where
  flattenCopy = flattenCopyProd @m @n @(IrrepDim j)

-- | Merge two already-flat @'AtomM@ sectors of equal irrep.
class MergeFlat (e :: IrrepExpr) (m1 :: Nat) (m2 :: Nat) where
  mergeFlat
    :: ToVSector e ('AtomM m1)
    -> ToVSector e ('AtomM m2)
    -> ToVSector e ('AtomM (m1 + m2))

instance
  ( KnownNat j
  , KnownNat m1
  , KnownNat m2
  , KnownNat (m1 + m2)
  , KnownNat (IrrepDim j)
  ) =>
  MergeFlat ('Atom j) m1 m2
  where
  mergeFlat = mergeCopyAxis @m1 @m2 @(IrrepDim j)

-- | Direct-sum same-'IrrepExpr' sectors along the copy axis (coalesce).
-- Flatten each side to @'AtomM@, then 'MergeFlat'.
class MergeSector (e :: IrrepExpr) (μ1 :: MultExpr) (μ2 :: MultExpr) (μOut :: MultExpr) where
  mergeSector
    :: ToVSector e μ1
    -> ToVSector e μ2
    -> ToVSector e μOut

instance
  ( FlattenCopy e μ1
  , FlattenCopy e μ2
  , EvalMult μ1 ~ m1
  , EvalMult μ2 ~ m2
  , mOut ~ m1 + m2
  , μOut ~ 'AtomM mOut
  , KnownNat m1
  , KnownNat m2
  , KnownNat mOut
  , MergeFlat e m1 m2
  ) =>
  MergeSector e μ1 μ2 μOut
  where
  mergeSector v1 v2 =
    mergeFlat @e @m1 @m2
      (flattenCopy @e @μ1 v1)
      (flattenCopy @e @μ2 v2)

instance
  ( j ~ k
  , AddMult μ μ2 ~ μOut
  , MergeSector ('Atom j) μ μ2 μOut
  ) =>
  InsertCompared 'EQ ('Atom j) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR =
    RCons @('Atom j) @μOut
      (mergeSector @('Atom j) @μ @μ2 @μOut sv sv2)
      restR

-- | Constraints for CG-fusing every sector (@FuseOneSector@ per head).
-- Plain fold matches @RCons @e @μ@; no spine walk class.
type family FuseRawSpine (rs :: Rep) :: Constraint where
  FuseRawSpine '[] = ()
  FuseRawSpine ('(e, μ) ': rest) =
    ( FuseOneSector e μ
    , FuseRawSpine rest
    )

-- | CG-fuse every sector in a spine, append (no coalesce).
fuseRaw
  :: FuseRawSpine rs
  => RepV rs
  -> RepV (FuseRepRaw rs)
fuseRaw RNil = RNil
fuseRaw (RCons @e @μ sv rs) =
  appendRepV (fuseOneSector @e @μ sv) (fuseRaw rs)

-- | Constraints for coalescing: 'InsertSpine' into the coalesced tail.
type family CoalesceSpine (rs :: Rep) :: Constraint where
  CoalesceSpine '[] = ()
  CoalesceSpine ('(e, μ) ': rest) =
    ( InsertSpine e μ (Coalesce rest)
    , CoalesceSpine rest
    )

-- | Sort + merge equal @'IrrepExpr'@ keys on a spine ('SRep' fold).
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

-- | CG fuse every sector, append, coalesce.
fuse :: ( FuseRawSpine rs
     , KnownSymRep (FuseRepRaw rs)
     , CoalesceSpine (FuseRepRaw rs)
     )
  => RepV rs
  -> RepV (Fuse rs)
fuse rv =
  coalesce (fuseRaw rv)

-- | Fuse @'RTensor ('RSum r) ('RSum q)@ by CG on each atom pair.
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
  -> RepV (FuseExpr ('RTensor ('RSum r) ('RSum q)))
fuseExpr x y =
  coalesce (fuseAtomSpinesTerm (symRepSing @r) x (symRepSing @q) y)

-- | Term-level constraints for walking @FuseAtomSpines@.
type family FuseAtomSpinesTerm (r :: Rep) (q :: Rep) :: Constraint where
  FuseAtomSpinesTerm '[] _ = ()
  FuseAtomSpinesTerm ('( 'Atom j1, 'AtomM m1) ': rest) q =
    ( FuseAtomSpineOneTerm j1 ('AtomM m1) q
    , FuseAtomSpinesTerm rest q
    )

type family FuseAtomSpineOneTerm (j1 :: Nat) (μ1 :: MultExpr) (q :: Rep) :: Constraint where
  FuseAtomSpineOneTerm _ _ '[] = ()
  FuseAtomSpineOneTerm j1 ('AtomM m1) ('( 'Atom j2, 'AtomM m2) ': rest) =
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
  => SIrrep ('Atom j1)
  -> SMult μ1
  -> ToVSector ('Atom j1) μ1
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
  :: SIrrep e
  -> SMult μ
  -> SU2Element
  -> ToVSector e μ +> ToVSector e μ
sectorMap (SAtomI @j) SMultAtom g =
  id ⊗^ wignerD @j g
sectorMap (SAtomI @j) (SMultProd SMultAtom SMultAtom) g =
  id ⊗^ wignerD @j g
sectorMap _ _ _ =
  error "Experiments.Symbolic.sectorMap: unsupported multiplicity shape"

-- | Apply 'sectorMap' to a sector payload.
actSector
  :: SIrrep e
  -> SMult μ
  -> SU2Element
  -> ToVSector e μ
  -> ToVSector e μ
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
-- Dual / cup on 'RepExpr' spaces
--
-- @'RDual ('RSum rs)@ is @DualVector (ToVSpine rs)@ — no formal dual sector.
--------------------------------------------------------------------------------

-- | Unit amplitude as @ToV ('RSum Unit)@ (@C 1 ⊗ C 1@).
unitToVFromScalar :: Complex Double -> ToV ('RSum Unit)
unitToVFromScalar s = s *^ (konst 1 ⊗ konst 1)

-- | Read the amplitude from @ToV ('RSum Unit)@.
unitToVScalar :: ToV ('RSum Unit) -> Complex Double
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
     , InnerSpace (ToVSector ('Atom j) ('AtomM m))
     , Scalar (ToVSector ('Atom j) ('AtomM m)) ~ Complex Double
     )
  => ToVSector ('Atom j) ('AtomM m)
  -> DualVector (ToVSector ('Atom j) ('AtomM m))
dualAtomAtomM v =
  fromLinearForm
    -+$> ( arr (LinearFunction ((v <.>)))
             :: ToVSector ('Atom j) ('AtomM m) +> Complex Double
         )

-- | Dual of an atom spine as @DualVector (ToVSpine rs)@.
rdual
  :: forall rs
   . KnownAtomRep rs
  => RepV rs
  -> ToV ('RDual ('RSum rs))
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
  -> ToV (MorExpr r q)
rmor x y = rdual x ⊗ repVToV y

--------------------------------------------------------------------------------
-- Cup / cap (compact closed)
--
-- Unfused: closed in 'ToV' (@RepExpr@ spaces, including @'RSum Unit@).
-- Fused: 'RepV' on singlet spines after dual≅primal + 'FuseExpr'.
-- Cap on ⊕ is the diagonal coevaluation (biproduct natural η).
--------------------------------------------------------------------------------

-- | Unfused evaluation @ε : r ⊗ r* → 𝟙@ (both sides 'ToV').
cupUnfused
  :: forall r
   . ( KnownAtomRep r
     , LinearSpace (ToVSpine r)
     , LinearSpace (DualVector (ToVSpine r))
     , Scalar (ToVSpine r) ~ Complex Double
     , Scalar (DualVector (ToVSpine r)) ~ Complex Double
     )
  => ToV (CupUnfusedExpr r)
  -> ToV ('RSum Unit)
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
  => ToV ('RSum Unit)
  -> ToV (CapUnfusedExpr r)
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
  => ToVSector ('Atom 0) ('AtomM m)
  -> Complex Double
cupHomScalarAtomM hom =
  let flat = fuseBond @m @1 $ hom
   in flat <.> flat

-- | Hom scalar from @'Atom 0@ / @'Prod m m@ (copy-leg trace).
cupHomScalar
  :: forall m
   . ( KnownNat m
     , KnownNat (m * 1)
     , HilbertSpace (C m)
     , InnerSpace (C m)
     , Scalar (C m) ~ Complex Double
     )
  => ToVSector ('Atom 0) ('Prod ('AtomM m) ('AtomM m))
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
  CupTrivial '[ '( 'Atom 0, 'AtomM m)]
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
  CupTrivial '[ '( 'Atom 0, 'Prod ('AtomM m) ('AtomM n))]
  where
  cupTrivial (RCons t RNil) =
    unitFromScalar (cupHomScalar @m t)

-- | Fused evaluation on singlets of @Fuse(r ⊗ r)@ (dual≅primal).
cupFused
  :: forall r
   . ( KnownAtomRep r
     , CupTrivial (CupFusedRep r)
     )
  => RepV (CupFusedRep r)
  -> RepV Unit
cupFused = cupTrivial

-- | Linear extension of 'fuseExpr' @r ⊗ r → FuseExpr (r ⊗ r)@.
fuseExprTensor
  :: forall r
   . ( KnownAtomRep r
     , FuseAtomSpinesTerm r r
     , KnownSymRep (FuseAtomSpines r r)
     , CoalesceSpine (FuseAtomSpines r r)
     , KnownSymRep (FuseExpr ('RTensor ('RSum r) ('RSum r)))
     , LinearSpace (ToVSpine r)
     , LinearSpace (ToVSpine (FuseExpr ('RTensor ('RSum r) ('RSum r))))
     , Scalar (ToVSpine r) ~ Complex Double
     , Scalar (ToVSpine (FuseExpr ('RTensor ('RSum r) ('RSum r))))
         ~ Complex Double
     )
  => ToVSpine r ⊗ ToVSpine r
  -> RepV (FuseExpr ('RTensor ('RSum r) ('RSum r)))
fuseExprTensor t =
  vToRepV @(FuseExpr ('RTensor ('RSum r) ('RSum r))) $
    (uncurryLinearMap -+$=> fuseCurried) $ t
  where
    fuseCurried ::
      ToVSpine r
        +> ( ToVSpine r
               +> ToVSpine (FuseExpr ('RTensor ('RSum r) ('RSum r)))
           )
    fuseCurried =
      arr . LinearFunction $ \x ->
        arr . LinearFunction $ \y ->
          repVToV $ fuseExpr @r @r (vToRepV @r x) (vToRepV @r y)

-- | Fused coevaluation: diagonal @η@ into singlets of @Fuse(r ⊗ r)@.
--
-- @projectToSymmetric ∘ fuse ∘ (id ⊗ undual) ∘ idTensor@ — biproduct-natural
-- (off-diagonal blocks vanish under 'FilterTrivial' for SU(2)).
capFused
  :: forall r
   . ( KnownAtomRep r
     , FuseAtomSpinesTerm r r
     , KnownSymRep (FuseAtomSpines r r)
     , CoalesceSpine (FuseAtomSpines r r)
     , KnownSymRep (FuseExpr ('RTensor ('RSum r) ('RSum r)))
     , ProjectToSymmetric (FuseExpr ('RTensor ('RSum r) ('RSum r)))
     , LinearSpace (ToVSpine r)
     , LinearSpace (DualVector (ToVSpine r))
     , LinearSpace (ToVSpine (FuseExpr ('RTensor ('RSum r) ('RSum r))))
     , Scalar (ToVSpine r) ~ Complex Double
     , Scalar (DualVector (ToVSpine r)) ~ Complex Double
     , Scalar (ToVSpine (FuseExpr ('RTensor ('RSum r) ('RSum r))))
         ~ Complex Double
     , TensorSpace (DualVector (ToVSpine r))
     )
  => RepV Unit
  -> RepV (CapFusedRep r)
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
-- Hom elements live in 'ToV' of 'MorExpr' (Dual-left). Identity is coevaluation
-- braided into Dual-left packing. 'assocCompose' is monoidal @α@ (no F-move).
--------------------------------------------------------------------------------

-- | Morphisms @a → b@ as Hom-elements @ToV (MorExpr a b)@.
newtype Sym (a :: Rep) (b :: Rep) = Sym {unSym :: ToV (MorExpr a b)}

-- | Identity: @η@ from 'capUnfused', swapped into Dual-left ('MorExpr').
idMor
  :: forall a
   . ( KnownAtomRep a
     , LinearSpace (ToVSpine a)
     , LinearSpace (DualVector (ToVSpine a))
     , Scalar (ToVSpine a) ~ Complex Double
     , Scalar (DualVector (ToVSpine a)) ~ Complex Double
     )
  => ToV (MorExpr a a)
idMor = swapMap $ capUnfused @a (unitToVFromScalar 1)

-- | Step 1: @f ⊗ g@.
tensorCompose
  :: forall a b c
   . ( TensorSpace (ToV (MorExpr a b))
     , TensorSpace (ToV (MorExpr b c))
     , Scalar (ToV (MorExpr a b)) ~ Complex Double
     , Scalar (ToV (MorExpr b c)) ~ Complex Double
     )
  => ToV (MorExpr a b)
  -> ToV (MorExpr b c)
  -> ToV (ComposeTensorExpr a b c)
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
  => ToV (ComposeTensorExpr a b c)
  -> ToV (ComposeAssocExpr a b c)
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
     , TensorSpace (ToV (CupUnfusedExpr b))
     , TensorSpace (ToV ('RSum Unit))
     )
  => ToV (ComposeAssocExpr a b c)
  -> ToV (ComposeCuppedExpr a b c)
cupTensorIdCompose t =
  ( id
      ⊗^ ( arr (LinearFunction (cupUnfused @b))
             ⊗^ id
         )
  )
    $ t

-- | Step 4: left unitor on the right factor @Unit ⊗ c → c@.
unitorCompose
  :: forall a b c
   . ( LinearSpace (DualVector (ToVSpine a))
     , LinearSpace (ToVSpine c)
     , Scalar (DualVector (ToVSpine a)) ~ Complex Double
     , Scalar (ToVSpine c) ~ Complex Double
     , TensorSpace (DualVector (ToVSpine a))
     , TensorSpace (ToVSpine c)
     )
  => ToV (ComposeCuppedExpr a b c)
  -> ToV (MorExpr a c)
unitorCompose t =
  (id ⊗^ unitLunit @(ToVSpine c)) $ t

-- | Unfused Hom composition:
-- @unitor ∘ (cup ⊗ id) ∘ assoc ∘ (f ⊗ g)@.
composeMor
  :: forall a b c
   . ( TensorSpace (ToV (MorExpr a b))
     , TensorSpace (ToV (MorExpr b c))
     , Scalar (ToV (MorExpr a b)) ~ Complex Double
     , Scalar (ToV (MorExpr b c)) ~ Complex Double
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
     , TensorSpace (ToV (CupUnfusedExpr b))
     , TensorSpace (ToV ('RSum Unit))
     )
  => ToV (MorExpr a b)
  -> ToV (MorExpr b c)
  -> ToV (MorExpr a c)
composeMor f g =
  unitorCompose @a @b @c
    ( cupTensorIdCompose @a @b @c
        ( assocCompose @a @b @c
            (tensorCompose @a @b @c f g)
        )
    )

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

-- | Braid an unfused atom pair: @r ⊗ q → q ⊗ r@ (term-level 'BraidExpr').
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

-- | Sector-level braid payload (@BraidIrrep@ / @BraidMult@).
braidSector
  :: SIrrep e
  -> SMult μ
  -> ToVSector e μ
  -> ToVSector (BraidIrrep e) (BraidMult μ)
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

-- | Project a spine onto its trivial (@'Atom 0@) sectors.
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
  ProjectToSymmetric ('( 'Atom j, 'AtomM m) ': rest)
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
  ProjectToSymmetric ('( 'Atom j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
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
    :: ToVSector ('Atom j) μ
    -> RepV (FilterTrivial rest)
    -> RepV (FilterTrivial ('( 'Atom j, μ) ': rest))

instance
  ( j ~ 0
  ) =>
  ProjectAtomOrd 'EQ j μ rest
  where
  projectAtomOrd v rs = RCons @('Atom 0) @μ v rs

instance
  ( FilterTrivial ('( 'Atom j, μ) ': rest) ~ FilterTrivial rest
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
     , VectorSpace (ToVSector ('Atom j) μ)
     , Scalar (ToVSector ('Atom j) μ) ~ Complex Double
     )
  => ToVSector ('Atom j) μ
  -> ToVSector ('Atom j) μ
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
  :: forall j1 j2 e μ
   . ( KnownNat j1
     , KnownNat j2
     )
  => SIrrep e
  -> SMult μ
  -> ToVSector e μ
  -> ToVSector e (RmoveMult μ)
rmoveSector (SAtomI @j) (SMultAtom @m) v =
  rPhaseSector @j1 @j2 @j @('AtomM m) v
rmoveSector (SAtomI @j) (SMultProd (SMultAtom @m) (SMultAtom @n)) v =
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
-- (@fuseExpr ∘ braidExpr ≅ rmove ∘ fuseExpr@).
rmove
  :: forall j1 j2 r s
   . ( KnownNat j1
     , KnownNat j2
     , KnownSymRep (FuseExpr ('RTensor ('RSum r) ('RSum s)))
     , RmoveTarget j1 j2 (FuseExpr ('RTensor ('RSum r) ('RSum s)))
         ~ FuseExpr (BraidExpr ('RTensor ('RSum r) ('RSum s)))
     )
  => RepV (FuseExpr ('RTensor ('RSum r) ('RSum s)))
  -> RepV (FuseExpr (BraidExpr ('RTensor ('RSum r) ('RSum s))))
rmove = rmoveSpine @j1 @j2 @(FuseExpr ('RTensor ('RSum r) ('RSum s)))
