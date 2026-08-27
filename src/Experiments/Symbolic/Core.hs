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
module Experiments.Symbolic.Core where

import Data.AdditiveGroup (AdditiveGroup ((^+^), zeroV))
import Data.Complex (Complex ((:+)))
import Data.Coerce (coerce)
import Data.Kind (Constraint)
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (..))
import Data.VectorSpace (InnerSpace ((<.>)), Scalar, VectorSpace ((*^)))
import qualified Data.Vector.Storable as VS
import GHC.TypeLits (CmpNat, KnownNat, Nat, natVal, sameNat, type (*), type (+))
import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..))
import Experiments.SU2 (TensorIrrepRepSU2)
import Experiments.Symbolic.Expr
import Experiments.Symbolic.TypeLevel
import Math.LinearMap.Category
  ( DualVector
  , HilbertSpace
  , (-+$>)
  , fromLinearForm
  , pattern LinearFunction
  , trace
  , type (+>)
  , type (⊗)
  , (⊗)
  )
import qualified Math.LinearMap.Category as LM (Tensor (Tensor))
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Class (LinearSpace, asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
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
  , mergeCopyAxisTensorLeft
  , rassocMap
  , splitBond
  , swapMap
  , tensorProdLeft
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
  STensorI
    :: SIrrep e1
    -> SIrrep e2
    -> SIrrep ('Tensor e1 e2)
  SDualI
    :: SIrrep e
    -> SIrrep ('Dual e)

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
  SMultDual
    :: SMult μ
    -> SMult ('DualM μ)

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

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , KnownSymRep rest
  ) =>
  KnownSymRep ('( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m) ': rest)
  where
  symRepSing =
    SRepCons
      (STensorI (SAtomI @j1) (SAtomI @j2))
      (SMultAtom @m)
      (symRepSing @rest)

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , KnownSymRep rest
  ) =>
  KnownSymRep ('( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  symRepSing =
    SRepCons
      (STensorI (SAtomI @j1) (SAtomI @j2))
      (SMultProd (SMultAtom @m) (SMultAtom @n))
      (symRepSing @rest)

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownSymRep rest
  ) =>
  KnownSymRep ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)
  where
  symRepSing =
    SRepCons
      (SDualI (SAtomI @j))
      (SMultDual (SMultAtom @m))
      (symRepSing @rest)

-- | Atom-only spine (subset of 'KnownSymRep'). Walks use 'symRepSing'.
class KnownSymRep rs => KnownAtomRep (rs :: Rep)

instance KnownAtomRep '[]

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownAtomRep rest
  ) =>
  KnownAtomRep ('( 'Atom j, 'AtomM m) ': rest)

-- | Dual-atom-only spine (subset of 'KnownSymRep'). Walks use 'symRepSing'.
class KnownSymRep rs => KnownDualAtomRep (rs :: Rep)

instance KnownDualAtomRep '[]

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownDualAtomRep rest
  ) =>
  KnownDualAtomRep ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)

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

pattern RConsTensorAtomM
  :: () => (e ~ 'Tensor ('Atom j1) ('Atom j2), μ ~ 'AtomM m)
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m)
  -> RepV rest
  -> RepV ('( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m) ': rest)
pattern RConsTensorAtomM v rs =
  RCons @('Tensor ('Atom j1) ('Atom j2)) @('AtomM m) v rs

pattern RConsTensorProd
  :: () => (e ~ 'Tensor ('Atom j1) ('Atom j2), μ ~ 'Prod ('AtomM m) ('AtomM n))
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n))
  -> RepV rest
  -> RepV ('( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)) ': rest)
pattern RConsTensorProd v rs =
  RCons @('Tensor ('Atom j1) ('Atom j2)) @('Prod ('AtomM m) ('AtomM n)) v rs

pattern RConsDualAtomDualAtomM
  :: () => (e ~ 'Dual ('Atom j), μ ~ 'DualM ('AtomM m))
  => ToVSector ('Dual ('Atom j)) ('DualM ('AtomM m))
  -> RepV rest
  -> RepV ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)
pattern RConsDualAtomDualAtomM v rs =
  RCons @('Dual ('Atom j)) @('DualM ('AtomM m)) v rs

pattern RConsTensorAtomDualAtom
  :: () => ( e ~ 'Tensor ('Atom j1) ('Dual ('Atom j2))
     , μ ~ 'Prod ('AtomM m) ('DualM ('AtomM n))
     )
  => ToVSector
       ('Tensor ('Atom j1) ('Dual ('Atom j2)))
       ('Prod ('AtomM m) ('DualM ('AtomM n)))
  -> RepV rest
  -> RepV
       ( '( 'Tensor ('Atom j1) ('Dual ('Atom j2))
          , 'Prod ('AtomM m) ('DualM ('AtomM n))
          )
           ': rest
       )
pattern RConsTensorAtomDualAtom v rs =
  RCons
    @('Tensor ('Atom j1) ('Dual ('Atom j2)))
    @('Prod ('AtomM m) ('DualM ('AtomM n)))
    v
    rs

pattern RConsTensorDualAtomAtom
  :: () => ( e ~ 'Tensor ('Dual ('Atom j1)) ('Atom j2)
     , μ ~ 'Prod ('DualM ('AtomM m)) ('AtomM n)
     )
  => ToVSector
       ('Tensor ('Dual ('Atom j1)) ('Atom j2))
       ('Prod ('DualM ('AtomM m)) ('AtomM n))
  -> RepV rest
  -> RepV
       ( '( 'Tensor ('Dual ('Atom j1)) ('Atom j2)
          , 'Prod ('DualM ('AtomM m)) ('AtomM n)
          )
           ': rest
       )
pattern RConsTensorDualAtomAtom v rs =
  RCons
    @('Tensor ('Dual ('Atom j1)) ('Atom j2))
    @('Prod ('DualM ('AtomM m)) ('AtomM n))
    v
    rs

{-# COMPLETE RNil, RCons :: RepV #-}
-- Pattern synonyms remain for call sites; production walks use 'RCons'.

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
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m)
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
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n))
  -> ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n))
fuseOneChannelProd sec =
  ( (id ⊗^ fuseCGChannel @j1 @j2 @j)
      . (splitBond @m @n ⊗^ id)
      . arr (LinearFunction flattenTensorProdCopy)
  )
    $ sec

-- | Walk @'TensorIrrepRepSU2'@ channels, building a tagged atom spine.
class FuseTensorSpine (j1 :: Nat) (j2 :: Nat) (μ :: MultExpr) (cg :: [(Nat, Nat)]) where
  fuseTensorSpine
    :: ToVSector ('Tensor ('Atom j1) ('Atom j2)) μ
    -> RepV (TagMult μ (AtomsFromCG cg))

instance FuseTensorSpine j1 j2 μ '[] where
  fuseTensorSpine _ = RNil

instance
  ( FuseTensorSpine j1 j2 ('AtomM m) rest
  , KnownNat j
  , KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , KnownNat (IrrepDim j)
  ) =>
  FuseTensorSpine j1 j2 ('AtomM m) ('(j, mOut) ': rest)
  where
  fuseTensorSpine v =
    repCons @('Atom j) @('AtomM m)
      (fuseOneChannelAtomM @j1 @j2 @j @m v)
      (fuseTensorSpine @j1 @j2 @('AtomM m) @rest v)

instance
  ( FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) rest
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
  FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) ('(j, mOut) ': rest)
  where
  fuseTensorSpine v =
    repCons @('Atom j) @('Prod ('AtomM m) ('AtomM n))
      (fuseOneChannelProd @j1 @j2 @j @m @n v)
      (fuseTensorSpine @j1 @j2 @('Prod ('AtomM m) ('AtomM n)) @rest v)

-- | CG-fuse one tensor sector to a (possibly longer) atom spine.
fuseOneSectorTensorAtomM
  :: forall j1 j2 m
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat m
     , FuseTensorSpine j1 j2 ('AtomM m) (TensorIrrepRepSU2 j1 j2)
     )
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m)
  -> RepV (FuseSector '( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m))
fuseOneSectorTensorAtomM =
  fuseTensorSpine @j1 @j2 @('AtomM m) @(TensorIrrepRepSU2 j1 j2)

fuseOneSectorTensorProd
  :: forall j1 j2 m n
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat m
     , KnownNat n
     , FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) (TensorIrrepRepSU2 j1 j2)
     )
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n))
  -> RepV (FuseSector '( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)))
fuseOneSectorTensorProd =
  fuseTensorSpine @j1 @j2 @('Prod ('AtomM m) ('AtomM n)) @(TensorIrrepRepSU2 j1 j2)

--------------------------------------------------------------------------------
-- Undual (Fuse identification): DualVector → primal atom payload
--
-- Type-level 'UndualIrrep' / 'UndualMult' strip Dual labels. Term-level undual
-- is Riesz inverse ('asTensor' + Hilbert coerce), then Condon–Shortley on the
-- irrep leg, then scale by @√(j+1)@ so the CG singlet matches the DualVector
-- Hilbert cup (@1/√(2j+1)@ from CG × @√(2j+1)@ here).
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

-- | Inverse of 'dualAtomAtomM', then CS + @√(j+1)@ for Fuse/cup coherence.
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
  => ToVSector ('Dual ('Atom j)) ('DualM ('AtomM m))
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
      -- Pivotal: CG singlet has @1/√(2j+1)@; cancel it so @cup ∘ fuse ≅ cupUnfused@.
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

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , FuseTensorSpine j1 j2 ('AtomM m) (TensorIrrepRepSU2 j1 j2)
  ) =>
  FuseOneSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m)
  where
  fuseOneSector = fuseOneSectorTensorAtomM

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) (TensorIrrepRepSU2 j1 j2)
  ) =>
  FuseOneSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n))
  where
  fuseOneSector = fuseOneSectorTensorProd

-- | Dual leaf: undual payload, land on @'Atom j@ / @'AtomM m@.
instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , HilbertSpace (C m)
  , HilbertSpace (C (IrrepDim j))
  ) =>
  FuseOneSector ('Dual ('Atom j)) ('DualM ('AtomM m))
  where
  fuseOneSector φ =
    RCons @('Atom j) @('AtomM m) (undualAtomAtomM @j @m φ) RNil

-- | @Atom ⊗ Dual Atom@: undual the right factor, then CG as primal tensor.
instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , HilbertSpace (C n)
  , HilbertSpace (C (IrrepDim j2))
  , FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) (TensorIrrepRepSU2 j1 j2)
  ) =>
  FuseOneSector
    ('Tensor ('Atom j1) ('Dual ('Atom j2)))
    ('Prod ('AtomM m) ('DualM ('AtomM n)))
  where
  fuseOneSector t =
    let undualed =
          (id ⊗^ arr (LinearFunction (undualAtomAtomM @j2 @n))) $ t
            :: ToVSector
                 ('Tensor ('Atom j1) ('Atom j2))
                 ('Prod ('AtomM m) ('AtomM n))
     in fuseOneSectorTensorProd @j1 @j2 @m @n undualed

-- | @Dual Atom ⊗ Atom@: undual the left factor, then CG as primal tensor.
instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , HilbertSpace (C m)
  , HilbertSpace (C (IrrepDim j1))
  , FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) (TensorIrrepRepSU2 j1 j2)
  ) =>
  FuseOneSector
    ('Tensor ('Dual ('Atom j1)) ('Atom j2))
    ('Prod ('DualM ('AtomM m)) ('AtomM n))
  where
  fuseOneSector t =
    let undualed =
          (arr (LinearFunction (undualAtomAtomM @j1 @m)) ⊗^ id) $ t
            :: ToVSector
                 ('Tensor ('Atom j1) ('Atom j2))
                 ('Prod ('AtomM m) ('AtomM n))
     in fuseOneSectorTensorProd @j1 @j2 @m @n undualed

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

instance
  ( CmpIrrep e ('Tensor ('Atom j1) ('Atom j2)) ~ ord
  , InsertCompared ord e μ ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m) rest
  ) =>
  InsertSpine e μ ('( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m) ': rest)
  where
  insertSpine sv (RCons sv2 restR) =
    insertCompared @ord @e @μ @('Tensor ('Atom j1) ('Atom j2)) @('AtomM m) sv sv2 restR

instance
  ( CmpIrrep e ('Tensor ('Atom j1) ('Atom j2)) ~ ord
  , InsertCompared ord e μ ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n)) rest
  ) =>
  InsertSpine e μ ('( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  insertSpine sv (RCons sv2 restR) =
    insertCompared @ord @e @μ @('Tensor ('Atom j1) ('Atom j2)) @('Prod ('AtomM m) ('AtomM n)) sv sv2 restR

instance
  ( CmpIrrep e ('Dual ('Atom j)) ~ ord
  , InsertCompared ord e μ ('Dual ('Atom j)) ('DualM ('AtomM m)) rest
  ) =>
  InsertSpine e μ ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)
  where
  insertSpine sv (RCons sv2 restR) =
    insertCompared @ord @e @μ @('Dual ('Atom j)) @('DualM ('AtomM m)) sv sv2 restR

instance
  ( CmpIrrep e ('Tensor ('Atom j1) ('Dual ('Atom j2))) ~ ord
  , InsertCompared
      ord
      e
      μ
      ('Tensor ('Atom j1) ('Dual ('Atom j2)))
      ('Prod ('AtomM m) ('DualM ('AtomM n)))
      rest
  ) =>
  InsertSpine
    e
    μ
    ( '( 'Tensor ('Atom j1) ('Dual ('Atom j2))
       , 'Prod ('AtomM m) ('DualM ('AtomM n))
       )
        ': rest
    )
  where
  insertSpine sv (RCons sv2 restR) =
    insertCompared
      @ord
      @e
      @μ
      @('Tensor ('Atom j1) ('Dual ('Atom j2)))
      @('Prod ('AtomM m) ('DualM ('AtomM n)))
      sv
      sv2
      restR

instance
  ( CmpIrrep e ('Tensor ('Dual ('Atom j1)) ('Atom j2)) ~ ord
  , InsertCompared
      ord
      e
      μ
      ('Tensor ('Dual ('Atom j1)) ('Atom j2))
      ('Prod ('DualM ('AtomM m)) ('AtomM n))
      rest
  ) =>
  InsertSpine
    e
    μ
    ( '( 'Tensor ('Dual ('Atom j1)) ('Atom j2)
       , 'Prod ('DualM ('AtomM m)) ('AtomM n)
       )
        ': rest
    )
  where
  insertSpine sv (RCons sv2 restR) =
    insertCompared
      @ord
      @e
      @μ
      @('Tensor ('Dual ('Atom j1)) ('Atom j2))
      @('Prod ('DualM ('AtomM m)) ('AtomM n))
      sv
      sv2
      restR

-- | Compare incoming sector @e@ against spine head @e2@ (@ord ~ CmpIrrep e e2@).
-- LT/GT are polymorphic; EQ keeps merge-specific Atom/Tensor instances.
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

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  ) =>
  FlattenCopy ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m)
  where
  flattenCopy = id

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , KnownNat (m * n)
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  ) =>
  FlattenCopy ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n))
  where
  flattenCopy v =
    tensorProdLeft (flattenTensorProdCopy @m @n @(IrrepDim j1) @(IrrepDim j2) v)

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

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m1
  , KnownNat m2
  , KnownNat (m1 + m2)
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  ) =>
  MergeFlat ('Tensor ('Atom j1) ('Atom j2)) m1 m2
  where
  mergeFlat = mergeCopyAxisTensorLeft @m1 @m2 @(IrrepDim j1) @(IrrepDim j2)

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

instance
  ( j1 ~ k1
  , j2 ~ k2
  , AddMult μ μ2 ~ μOut
  , MergeSector ('Tensor ('Atom j1) ('Atom j2)) μ μ2 μOut
  ) =>
  InsertCompared 'EQ ('Tensor ('Atom j1) ('Atom j2)) μ ('Tensor ('Atom k1) ('Atom k2)) μ2 rest
  where
  insertCompared sv sv2 restR =
    RCons @('Tensor ('Atom j1) ('Atom j2)) @μOut
      (mergeSector @('Tensor ('Atom j1) ('Atom j2)) @μ @μ2 @μOut sv sv2)
      restR

-- EQ Dual↔Dual merge omitted: AddMult → 'AtomM conflicts with Dual ToVSector
-- expecting 'DualM. Coalesce of equal Dual keys is intentionally unsupported until
-- Dual copy-merge is designed.

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

-- | CG fuse a distributed tensor rep (@'Tensor'@).
fuseTensor
  :: ( FuseRawSpine (Tensor r s)
     , KnownSymRep (FuseRepRaw (Tensor r s))
     , CoalesceSpine (FuseRepRaw (Tensor r s))
     )
  => RepV (Tensor r s)
  -> RepV (Fuse (Tensor r s))
fuseTensor = fuse

-- | Build unfused @'Tensor'@ from two atom sectors (pair layout).
tensorAtoms
  :: forall j1 m1 j2 m2
   . ( KnownNat j1
     , KnownNat m1
     , KnownNat j2
     , KnownNat m2
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     )
  => C m1 ⊗ C (IrrepDim j1)
  -> C m2 ⊗ C (IrrepDim j2)
  -> RepV
       ( Tensor
           '[ '( 'Atom j1, 'AtomM m1)]
           '[ '( 'Atom j2, 'AtomM m2)]
       )
tensorAtoms s1 s2 =
  tensor
    (RCons @('Atom j1) @('AtomM m1) s1 RNil)
    (RCons @('Atom j2) @('AtomM m2) s2 RNil)

-- | Pair one left sector with every sector of a right spine (@s1 ⊗ s2@).
tensorOne
  :: forall e μ q
   . KnownSymRep q
  => SIrrep e
  -> SMult μ
  -> ToVSector e μ
  -> RepV q
  -> RepV (TensorOne '(e, μ) q)
tensorOne se sm s1 = go (symRepSing @q)
  where
    go :: forall q'. SRep q' -> RepV q' -> RepV (TensorOne '(e, μ) q')
    go SRepNil RNil = RNil
    go (SRepCons se2 sm2 rest) (RCons s2 qRest) =
      RCons (tensorPairPayload se sm se2 sm2 s1 s2) (go rest qRest)

-- | Payload for one 'TensorPair' cell (singleton-refined @⊗@).
tensorPairPayload
  :: SIrrep e
  -> SMult μ
  -> SIrrep e2
  -> SMult μ2
  -> ToVSector e μ
  -> ToVSector e2 μ2
  -> ToVSector ('Tensor e e2) ('Prod μ μ2)
tensorPairPayload (SAtomI @j1) (SMultAtom @m) (SAtomI @j2) (SMultAtom @n) a b =
  a ⊗ b
tensorPairPayload
  (SAtomI @j1)
  (SMultAtom @m)
  (SDualI (SAtomI @j2))
  (SMultDual (SMultAtom @n))
  a
  b =
  a ⊗ b
tensorPairPayload
  (SDualI (SAtomI @j1))
  (SMultDual (SMultAtom @m))
  (SAtomI @j2)
  (SMultAtom @n)
  a
  b =
  a ⊗ b
tensorPairPayload _ _ _ _ _ _ =
  error "Experiments.Symbolic.tensorPairPayload: unsupported sector pair"

-- | Cartesian tensor of two spines ('Tensor' type family / 'SRep' fold).
tensor
  :: forall r q
   . ( KnownSymRep r
     , KnownSymRep q
     )
  => RepV r
  -> RepV q
  -> RepV (Tensor r q)
tensor r q = go (symRepSing @r) r
  where
    go :: forall r'. SRep r' -> RepV r' -> RepV (Tensor r' q)
    go SRepNil RNil = RNil
    go (SRepCons se sm rest) (RCons s1 rRest) =
      appendRepV (tensorOne se sm s1 q) (go rest rRest)

-- | Historical aliases (domain proofs via 'KnownAtomRep' / 'KnownDualAtomRep').
tensorAtom
  :: (KnownAtomRep r, KnownAtomRep q)
  => RepV r -> RepV q -> RepV (Tensor r q)
tensorAtom = tensor

tensorDualAtom
  :: (KnownDualAtomRep r, KnownAtomRep q)
  => RepV r -> RepV q -> RepV (Tensor r q)
tensorDualAtom = tensor

tensorAtomDual
  :: (KnownAtomRep r, KnownDualAtomRep q)
  => RepV r -> RepV q -> RepV (Tensor r q)
tensorAtomDual = tensor

--------------------------------------------------------------------------------
-- SU(2) group action (Wigner on irrep legs)
--
-- @g ↦ (RepV rs → RepV rs)@: identity on copy axes, @D^{j/2}(g)@ on each
-- irrep factor (Kronecker on unfused @'Tensor@). Dual / mixed dual tensors
-- are not wired yet.
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

-- | Sector morphism: @id@ on multiplicity, Wigner on irrep factor(s).
sectorMap
  :: SIrrep e
  -> SMult μ
  -> SU2Element
  -> ToVSector e μ +> ToVSector e μ
sectorMap (SAtomI @j) SMultAtom g =
  id ⊗^ wignerD @j g
sectorMap (SAtomI @j) (SMultProd SMultAtom SMultAtom) g =
  id ⊗^ wignerD @j g
sectorMap (STensorI (SAtomI @j1) (SAtomI @j2)) SMultAtom g =
  (id ⊗^ wignerD @j1 g) ⊗^ wignerD @j2 g
sectorMap
  (STensorI (SAtomI @j1) (SAtomI @j2))
  (SMultProd SMultAtom SMultAtom)
  g =
  (id ⊗^ wignerD @j1 g) ⊗^ (id ⊗^ wignerD @j2 g)
sectorMap _ _ _ =
  error "Experiments.Symbolic.sectorMap: dual / unsupported sector (blocker)"

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
actSector se@(STensorI SAtomI SAtomI) sm@SMultAtom g v =
  sectorMap se sm g $ v
actSector se@(STensorI SAtomI SAtomI) sm@(SMultProd SMultAtom SMultAtom) g v =
  sectorMap se sm g $ v
actSector se sm g _ =
  sectorMap se sm g `seq` error "Experiments.Symbolic.actSector: dual / unsupported sector (blocker)"

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
    go _ _ = error "actRep: spine / singleton mismatch"

--------------------------------------------------------------------------------
-- Application (compact closed evaluation)
--
-- Given @f ∈ Mor r q = Dual r ⊗ q@ and @x ∈ r@:
--
--   1. inject:   r ⊗ (Dual r ⊗ q)     — fuse @f@ first so 'Tensor' stays leaf×leaf
--   2. assoc:    (r ⊗ Dual r) ⊗ q     — F-move / associator (blocker: no Symbolic fmove yet)
--   3. cup:      Unit ⊗ q             — evaluation @r ⊗ Dual r → Unit@ on the left
--   4. unitor:   q                    — left unitor @Unit ⊗ q → q@
--
-- | Bodies for @assocApply@ are intentionally @undefined@ (Symbolic F-move).
-- @injectApply@, 'cup', 'cupApply', and @lunitApply@ are implemented.
--------------------------------------------------------------------------------

-- | Step 1 target: @r ⊗ Fuse(Mor r q)@ (Mor fused to atoms so 'Tensor' applies).
type ApplyInject (r :: Rep) (q :: Rep) = Tensor r (Fuse (Mor r q))

-- | Step 2 target: @(Fuse (r ⊗ Dual r)) ⊗ q@.
type ApplyAssoc (r :: Rep) (q :: Rep) = Tensor (Fuse (Tensor r (Dual r))) q

-- | Step 3 target: @Unit ⊗ q@.
type ApplyCupped (r :: Rep) (q :: Rep) = Tensor Unit q

-- | Left-inject the object into the morphism: @x ⊗ f@.
injectApply
  :: forall r q
   . ( FuseRawSpine (Mor r q)
     , KnownSymRep (FuseRepRaw (Mor r q))
     , CoalesceSpine (FuseRepRaw (Mor r q))
     , KnownAtomRep r
     , KnownAtomRep (Fuse (Mor r q))
     )
  => RepV r
  -> RepV (Mor r q)
  -> RepV (ApplyInject r q)
injectApply x f = tensor x (fuse f)

-- | Reassociate toward cup-ready parenthesization @(r ⊗ Dual r) ⊗ q@.
-- Blocker: Symbolic F-move / associator on fused spines.
assocApply
  :: forall r q
   . RepV (ApplyInject r q)
  -> RepV (ApplyAssoc r q)
assocApply = undefined

-- | Cup (evaluation / counit): @Fuse (r ⊗ Dual r) → Unit@.
--
-- After Fuse undual (Riesz + CS + @√(j+1)@) + CG, keep the trivial channel and
-- contract its copy space (Hom) to a scalar. Coherent with 'cupUnfused' on
-- atom leaves (including spin-½).
cup
  :: forall r
   . ( ProjectToSymmetric (Fuse (Tensor r (Dual r)))
     , CupTrivial (FilterTrivial (Fuse (Tensor r (Dual r))))
     )
  => RepV (Fuse (Tensor r (Dual r)))
  -> RepV Unit
cup = cupTrivial . projectToSymmetric

-- | Contract a trivial-only spine (@FilterTrivial@) down to 'Unit'.
class CupTrivial (rs :: Rep) where
  cupTrivial :: RepV rs -> RepV Unit

unitFromScalar :: Complex Double -> RepV Unit
unitFromScalar s =
  RCons @('Atom 0) @('AtomM 1) (s *^ (konst 1 ⊗ konst 1)) RNil

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
  , KnownNat (n * 1)
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

-- | Hom scalar from @'Atom 0@ / @'Prod m m@ (same contraction as 'CupTrivial').
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
   in trace -+$> (fromTensor -+$=> (swapMap $ paired))

-- | @(cup ⊗ id)@ on one Hom/@q@ tensor row: contract Hom, land in @Tensor Unit q@.
cupHomOnTensorUnit
  :: forall μ j n
   . ( KnownNat j
     , KnownNat n
     , KnownNat (IrrepDim j)
     , LinearSpace (ToVSector ('Atom 0) μ)
     , ToVSector ('Tensor ('Atom 0) ('Atom j)) ('Prod μ ('AtomM n))
         ~ (ToVSector ('Atom 0) μ ⊗ ToVSector ('Atom j) ('AtomM n))
     , ToVSector ('Tensor ('Atom 0) ('Atom j)) ('Prod ('AtomM 1) ('AtomM n))
         ~ ((C 1 ⊗ C 1) ⊗ ToVSector ('Atom j) ('AtomM n))
     , Scalar (ToVSector ('Atom 0) μ) ~ Complex Double
     )
  => (ToVSector ('Atom 0) μ -> Complex Double)
  -> ToVSector
       ('Tensor ('Atom 0) ('Atom j))
       ('Prod μ ('AtomM n))
  -> ToVSector
       ('Tensor ('Atom 0) ('Atom j))
       ('Prod ('AtomM 1) ('AtomM n))
cupHomOnTensorUnit formScalar t =
  let hom_q =
        t
          :: ToVSector ('Atom 0) μ
               ⊗ ToVSector ('Atom j) ('AtomM n)
      form =
        arr (LinearFunction formScalar)
          :: ToVSector ('Atom 0) μ +> Complex Double
      scaled =
        (form ⊗^ id) $ hom_q
          :: Complex Double ⊗ ToVSector ('Atom j) ('AtomM n)
      -- @TensorProduct (Complex Double) q = q@; avoid @fromFlatTensor@ on @q@.
      LM.Tensor qv = scaled
   in ((konst 1 ⊗ konst 1) :: C 1 ⊗ C 1) ⊗ qv

cupHomTensorUnit
  :: forall m j n
   . ( KnownNat m
     , KnownNat j
     , KnownNat n
     , KnownNat (IrrepDim j)
     , KnownNat (m * 1)
     , HilbertSpace (C m)
     , InnerSpace (C m)
     , Scalar (C m) ~ Complex Double
     )
  => ToVSector
       ('Tensor ('Atom 0) ('Atom j))
       ('Prod ('Prod ('AtomM m) ('AtomM m)) ('AtomM n))
  -> ToVSector
       ('Tensor ('Atom 0) ('Atom j))
       ('Prod ('AtomM 1) ('AtomM n))
cupHomTensorUnit = cupHomOnTensorUnit @('Prod ('AtomM m) ('AtomM m)) @j @n (cupHomScalar @m)

cupHomAtomMTensorUnit
  :: forall m j n
   . ( KnownNat m
     , KnownNat j
     , KnownNat n
     , KnownNat (IrrepDim j)
     , KnownNat (m * 1)
     , HilbertSpace (C m)
     , InnerSpace (C m)
     , Scalar (C m) ~ Complex Double
     )
  => ToVSector
       ('Tensor ('Atom 0) ('Atom j))
       ('Prod ('AtomM m) ('AtomM n))
  -> ToVSector
       ('Tensor ('Atom 0) ('Atom j))
       ('Prod ('AtomM 1) ('AtomM n))
cupHomAtomMTensorUnit =
  cupHomOnTensorUnit @('AtomM m) @j @n (cupHomScalarAtomM @m)

-- | Zero spine of @Tensor Unit q@ (same shape as @tensorOne@ of a zero unit).
zeroTensorUnit
  :: forall q
   . SRep q
  -> RepV (Tensor Unit q)
zeroTensorUnit SRepNil = RNil
zeroTensorUnit (SRepCons (SAtomI @j) (SMultAtom @n) rest) =
  RCons (zeroV :: ToVSector ('Tensor ('Atom 0) ('Atom j)) ('Prod ('AtomM 1) ('AtomM n)))
    (zeroTensorUnit rest)
zeroTensorUnit _ = error "zeroTensorUnit: expected atom spine"

-- | Pointwise sum of two @Tensor Unit q@ spines (driven by @q@ singleton).
addTensorUnit
  :: forall q
   . SRep q
  -> RepV (Tensor Unit q)
  -> RepV (Tensor Unit q)
  -> RepV (Tensor Unit q)
addTensorUnit SRepNil RNil RNil = RNil
addTensorUnit (SRepCons SAtomI SMultAtom qRest) (RCons a as) (RCons b bs) =
  RCons (a ^+^ b) (addTensorUnit qRest as bs)
addTensorUnit _ _ _ = error "addTensorUnit: expected atom spine"

-- | Peel one @TensorOne@ row guided by an atom spine @q@.
peelTensorOneAtom
  :: forall s q ys
   . SRep q
  -> RepV (Append (TensorOne s q) ys)
  -> (RepV (TensorOne s q), RepV ys)
peelTensorOneAtom SRepNil rv = (RNil, rv)
peelTensorOneAtom (SRepCons _ _ qRest) (RCons v rv) =
  let (xs, ys) = peelTensorOneAtom @s qRest rv
   in (RCons v xs, ys)
peelTensorOneAtom _ _ = error "peelTensorOneAtom: spine/value mismatch"

-- | Contract one Hom/@q@ @TensorOne@ row (@'Prod m m@ trivial channel).
cupApplyRowProd
  :: forall m q
   . ( KnownNat m
     , KnownNat (m * 1)
     , HilbertSpace (C m)
     , InnerSpace (C m)
     , Scalar (C m) ~ Complex Double
     )
  => SRep q
  -> RepV (TensorOne '( 'Atom 0, 'Prod ('AtomM m) ('AtomM m)) q)
  -> RepV (Tensor Unit q)
cupApplyRowProd SRepNil RNil = RNil
cupApplyRowProd (SRepCons (SAtomI @j) (SMultAtom @n) qRest) (RCons t tRest) =
  RCons (cupHomTensorUnit @m @j @n t) (cupApplyRowProd @m qRest tRest)
cupApplyRowProd _ _ = error "cupApplyRowProd: expected atom spine"

-- | Contract one Hom/@q@ @TensorOne@ row (flat @'AtomM m@ trivial channel).
cupApplyRowAtomM
  :: forall m q
   . ( KnownNat m
     , KnownNat (m * 1)
     , HilbertSpace (C m)
     , InnerSpace (C m)
     , Scalar (C m) ~ Complex Double
     )
  => SRep q
  -> RepV (TensorOne '( 'Atom 0, 'AtomM m) q)
  -> RepV (Tensor Unit q)
cupApplyRowAtomM SRepNil RNil = RNil
cupApplyRowAtomM (SRepCons (SAtomI @j) (SMultAtom @n) qRest) (RCons t tRest) =
  RCons (cupHomAtomMTensorUnit @m @j @n t) (cupApplyRowAtomM @m qRest tRest)
cupApplyRowAtomM _ _ = error "cupApplyRowAtomM: expected atom spine"

-- | Leaf pairing @v ⊗ DualVector v → ℂ@ (braid + fromTensor + trace).
cupUnfusedLeaf
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , InnerSpace (ToVSector ('Atom j) ('AtomM m))
     , Scalar (ToVSector ('Atom j) ('AtomM m)) ~ Complex Double
     )
  => ToVSector
       ('Tensor ('Atom j) ('Dual ('Atom j)))
       ('Prod ('AtomM m) ('DualM ('AtomM m)))
  -> Complex Double
cupUnfusedLeaf t =
  let v =
        t
          :: ToVSector ('Atom j) ('AtomM m)
               ⊗ DualVector (ToVSector ('Atom j) ('AtomM m))
   in trace -+$> (fromTensor -+$=> (swapMap $ v))

-- | Atom-spine singleton ↦ dual-atom singleton (@Dual@ on keys).
dualAtomSing :: SRep rs -> SRep (Dual rs)
dualAtomSing SRepNil = SRepNil
dualAtomSing (SRepCons (SAtomI @j) (SMultAtom @m) rest) =
  SRepCons (SDualI (SAtomI @j)) (SMultDual (SMultAtom @m)) (dualAtomSing rest)
dualAtomSing _ = error "dualAtomSing: expected atom spine"

-- | Peel one @TensorOne@ row using a dual-atom guide (same length); @TensorOne@
-- reduces under the 'SRepCons' refinement so no 'PeelAppend' on an unreduced
-- @Dual r@ is required.
peelTensorOneAtomDual
  :: forall j m q ys
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     )
  => SRep q
  -> RepV (Append (TensorOne '( 'Atom j, 'AtomM m) q) ys)
  -> (RepV (TensorOne '( 'Atom j, 'AtomM m) q), RepV ys)
peelTensorOneAtomDual SRepNil rv = (RNil, rv)
peelTensorOneAtomDual
  (SRepCons (SDualI (SAtomI @k)) (SMultDual (SMultAtom @n)) qRest)
  (RCons v rv) =
    let (xs, ys) = peelTensorOneAtomDual @j @m qRest rv
     in (RCons v xs, ys)
peelTensorOneAtomDual _ _ =
  error "peelTensorOneAtomDual: expected dual-atom spine"

-- | Unfused cup on a full atom spine: sum over diagonal leaf cups in
-- @Tensor r (Dual r)@ (off-diagonal sectors contribute 0).
cupUnfusedRep
  :: forall r
   . KnownAtomRep r
  => RepV (Tensor r (Dual r))
  -> RepV Unit
cupUnfusedRep rv =
  RCons @('Atom 0) @('AtomM 1) (s *^ (konst 1 ⊗ konst 1)) RNil
  where
    dFull = dualAtomSing (symRepSing @r)
    s = goRows (symRepSing @r) rv

    goRows
      :: forall r'
       . SRep r'
      -> RepV (Tensor r' (Dual r))
      -> Complex Double
    goRows SRepNil RNil = 0
    goRows (SRepCons (SAtomI @j) (SMultAtom @m) rRest) rv' =
      goRowsCons @j @m rRest rv'
    goRows _ _ = error "cupUnfusedRep: expected atom spine"

    goRowsCons
      :: forall j m rest
       . ( KnownNat j
         , KnownNat m
         , KnownNat (IrrepDim j)
         )
      => SRep rest
      -> RepV (Tensor ('( 'Atom j, 'AtomM m) ': rest) (Dual r))
      -> Complex Double
    goRowsCons rRest rv' =
      let (row, restRv) = peelTensorOneAtomDual @j @m @(Dual r) @(Tensor rest (Dual r)) dFull rv'
       in goCols @j @m dFull row + goRows rRest restRv

    goCols
      :: forall j m q'
       . ( KnownNat j
         , KnownNat m
         , KnownNat (IrrepDim j)
         )
      => SRep q'
      -> RepV (TensorOne '( 'Atom j, 'AtomM m) q')
      -> Complex Double
    goCols SRepNil RNil = 0
    goCols
      (SRepCons (SDualI (SAtomI @k)) (SMultDual (SMultAtom @n)) qRest)
      (RCons t tRest) =
        let sCol = case (sameNat (Proxy @j) (Proxy @k), sameNat (Proxy @m) (Proxy @n)) of
              (Just Refl, Just Refl) -> cupUnfusedLeaf @j @m t
              _ -> 0
         in sCol + goCols @j @m qRest tRest
    goCols _ _ = error "cupUnfusedRep.goCols: expected dual-atom spine"

-- | Unfused leaf cup: @Atom ⊗ Dual Atom → Unit@ (special case of 'cupUnfusedRep').
cupUnfused
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , InnerSpace (ToVSector ('Atom j) ('AtomM m))
     , Scalar (ToVSector ('Atom j) ('AtomM m)) ~ Complex Double
     )
  => RepV
       '[ '( 'Tensor ('Atom j) ('Dual ('Atom j))
           , 'Prod ('AtomM m) ('DualM ('AtomM m))
           )
        ]
  -> RepV Unit
cupUnfused = cupUnfusedRep @'[ '( 'Atom j, 'AtomM m)]

-- | Apply cup on the left factor of @ApplyAssoc@: @(cup ⊗ id)@.
--
-- Walk @Fuse (r ⊗ Dual r)@; keep only @'Atom 0@ TensorOne rows, contract Hom,
-- sum into @Tensor Unit q@. Non-trivial left sectors contribute @0@.
cupApply
  :: forall r q
   . ( KnownAtomRep q
     , KnownSymRep (Fuse (Tensor r (Dual r)))
     )
  => RepV (ApplyAssoc r q)
  -> RepV (ApplyCupped r q)
cupApply = goFuse (symRepSing @(Fuse (Tensor r (Dual r))))
  where
    qSing = symRepSing @q

    goFuse
      :: forall fuse
       . SRep fuse
      -> RepV (Tensor fuse q)
      -> RepV (Tensor Unit q)
    goFuse SRepNil RNil = zeroTensorUnit qSing
    goFuse (SRepCons (SAtomI @j) (SMultProd (SMultAtom @m) (SMultAtom @n)) fuseRest) rv =
      case (sameNat (Proxy @j) (Proxy @0), sameNat (Proxy @m) (Proxy @n)) of
        (Just Refl, Just Refl) ->
          let (row, restRv) =
                peelTensorOneAtom
                  @'( 'Atom 0, 'Prod ('AtomM m) ('AtomM m))
                  qSing
                  rv
              contrib = cupApplyRowProd @m qSing row
           in addTensorUnit qSing contrib (goFuse fuseRest restRv)
        _ ->
          let (_, restRv) =
                peelTensorOneAtom
                  @'( 'Atom j, 'Prod ('AtomM m) ('AtomM n))
                  qSing
                  rv
           in goFuse fuseRest restRv
    goFuse (SRepCons (SAtomI @j) (SMultAtom @m) fuseRest) rv =
      case sameNat (Proxy @j) (Proxy @0) of
        Just Refl ->
          let (row, restRv) =
                peelTensorOneAtom @'( 'Atom 0, 'AtomM m) qSing rv
              contrib = cupApplyRowAtomM @m qSing row
           in addTensorUnit qSing contrib (goFuse fuseRest restRv)
        Nothing ->
          let (_, restRv) =
                peelTensorOneAtom @'( 'Atom j, 'AtomM m) qSing rv
           in goFuse fuseRest restRv
    goFuse _ _ = error "cupApply: expected fused atom spine"

-- | One sector: fuse @0 ⊗ j → j@, then flatten @'Prod ('AtomM 1) ('AtomM n) → 'AtomM n@.
lunitSector
  :: forall j n
   . ( KnownNat j
     , KnownNat n
     , KnownNat (IrrepDim j)
     , KnownNat (1 * n)
     )
  => ToVSector ('Tensor ('Atom 0) ('Atom j)) ('Prod ('AtomM 1) ('AtomM n))
  -> ToVSector ('Atom j) ('AtomM n)
lunitSector sec =
  flattenCopyProd @1 @n @(IrrepDim j)
    (fuseOneChannelProd @0 @j @j @1 @n sec)

-- | Left unitor on @Tensor Unit q@, driven by 'SRep' (atom spine).
-- Matching 'SAtomI'/'SMultAtom' refines @q@ so @Tensor Unit q@ reduces.
lunitSpine
  :: forall q
   . KnownAtomRep q
  => RepV (Tensor Unit q)
  -> RepV q
lunitSpine = go (symRepSing @q)
  where
    go :: forall q'. SRep q' -> RepV (Tensor Unit q') -> RepV q'
    go SRepNil RNil = RNil
    go (SRepCons (SAtomI @j) (SMultAtom @n) rest) (RCons v tRest) =
      RCons (lunitSector @j @n v) (go rest tRest)
    go _ _ = error "lunitSpine: expected atom spine"

-- | Left unitor: @Unit ⊗ q → q@.
lunitApply
  :: forall r q
   . KnownAtomRep q
  => RepV (ApplyCupped r q)
  -> RepV q
lunitApply = lunitSpine @q

-- | Categorical application @Mor r q → r → q@ via inject / assoc / cup / unitor.
apply
  :: forall r q
   . ( FuseRawSpine (Mor r q)
     , KnownSymRep (FuseRepRaw (Mor r q))
     , CoalesceSpine (FuseRepRaw (Mor r q))
     , KnownAtomRep r
     , KnownAtomRep (Fuse (Mor r q))
     , KnownAtomRep q
     , KnownSymRep (Fuse (Tensor r (Dual r)))
     )
  => RepV (Mor r q)
  -> RepV r
  -> RepV q
apply f x =
  lunitApply @r @q
    (cupApply @r @q (assocApply @r @q (injectApply @r @q x f)))

--------------------------------------------------------------------------------
-- Category (constrained-categories): morphisms as Hom-elements
--
-- @Sym a b@ wraps @RepV (Mor a b) = RepV (Dual a ⊗ b)@. Identity is coevaluation
-- @η ∈ Dual a ⊗ a@; composition cups the middle @b ⊗ Dual b@ (same blockers as
-- 'apply': F-move / fused cup). Objects are leaf atom spines ('AtomSpine').
--------------------------------------------------------------------------------

-- | Morphisms @a → b@ as elements of the internal Hom @Dual a ⊗ b@.
newtype Sym (a :: Rep) (b :: Rep) = Sym { unSym :: RepV (Mor a b) }

-- | Identity morphism: coevaluation @η ∈ Dual a ⊗ a@ (diagonal @asTensor id@).
idMor :: forall a. KnownAtomRep a => RepV (Mor a a)
idMor = goRows (dualAtomSing (symRepSing @a))
  where
    aSing = symRepSing @a

    goRows
      :: forall d
       . SRep d
      -> RepV (Tensor d a)
    goRows SRepNil = RNil
    goRows (SRepCons (SDualI (SAtomI @j)) (SMultDual (SMultAtom @m)) dRest) =
      appendRepV (idOneRow @j @m aSing) (goRows dRest)
    goRows _ = error "idMor: expected dual-atom spine"

    idOneRow
      :: forall j m
       . ( KnownNat j
         , KnownNat m
         , KnownNat (IrrepDim j)
         )
      => SRep a
      -> RepV (TensorOne '( 'Dual ('Atom j), 'DualM ('AtomM m)) a)
    idOneRow = goCols
      where
        goCols :: forall q. SRep q -> RepV (TensorOne '( 'Dual ('Atom j), 'DualM ('AtomM m)) q)
        goCols SRepNil = RNil
        goCols (SRepCons (SAtomI @k) (SMultAtom @n) qRest) =
          let cell =
                case (sameNat (Proxy @j) (Proxy @k), sameNat (Proxy @m) (Proxy @n)) of
                  (Just Refl, Just Refl) ->
                    asTensor
                      -+$=> ( id
                                :: ToVSector ('Atom j) ('AtomM m)
                                     +> ToVSector ('Atom j) ('AtomM m)
                             )
                  _ -> zeroV
           in RCons cell (goCols qRest)
        goCols _ = error "idMor.idOneRow: expected atom spine"

--------------------------------------------------------------------------------
-- Composition (compact closed)
--
-- Given @f ∈ Mor a b = Dual a ⊗ b@ and @g ∈ Mor b c = Dual b ⊗ c@:
--
--   1. tensor:  Fuse(Mor a b) ⊗ Fuse(Mor b c)     — fuse so 'Tensor' stays leaf×leaf
--   2. assoc:   Dual a ⊗ (Fuse(b ⊗ Dual b) ⊗ c)   — F-move / associator
--   3. cup:     Dual a ⊗ (Unit ⊗ c)               — cup middle @b ⊗ Dual b@
--   4. unitor:  Dual a ⊗ c = Mor a c              — lunit on the right factor
--
-- @assocCompose@ waits on the Symbolic F-move (same as 'assocApply').
-- @tensorCompose@ needs @Tensor@ on fused Mor spines that still carry @'Prod@
-- tags (@KnownAtomRep@ is AtomM-only).
--------------------------------------------------------------------------------

-- | Step 1 target: @Fuse(Mor a b) ⊗ Fuse(Mor b c)@.
type ComposeTensor (a :: Rep) (b :: Rep) (c :: Rep) =
  Tensor (Fuse (Mor a b)) (Fuse (Mor b c))

-- | Step 2 target: @Dual a ⊗ (Fuse (b ⊗ Dual b) ⊗ c)@.
type ComposeAssoc (a :: Rep) (b :: Rep) (c :: Rep) =
  Tensor (Dual a) (Tensor (Fuse (Tensor b (Dual b))) c)

-- | Step 3 target: @Dual a ⊗ (Unit ⊗ c)@.
type ComposeCupped (a :: Rep) (b :: Rep) (c :: Rep) =
  Tensor (Dual a) (Tensor Unit c)

-- | Tensor the two Hom-elements (after fusing each to an atom spine).
-- Blocker: 'Fuse' of Mor leaves @'Prod@ multiplicities; 'tensorAtom' needs
-- @KnownAtomRep@ (AtomM-only). Flatten-Prod-then-tensor, or extend tensor.
tensorCompose
  :: forall a b c
   . RepV (Mor a b)
  -> RepV (Mor b c)
  -> RepV (ComposeTensor a b c)
tensorCompose = undefined

-- | Reassociate toward cup-ready @Dual a ⊗ (b ⊗ Dual b) ⊗ c@.
-- Blocker: Symbolic F-move / associator (same as 'assocApply').
assocCompose
  :: forall a b c
   . RepV (ComposeTensor a b c)
  -> RepV (ComposeAssoc a b c)
assocCompose = undefined

-- | Cup the middle @Fuse (b ⊗ Dual b) → Unit@: @(id ⊗ (cup ⊗ id))@.
-- Same contraction as 'cupApply', but under an outer @Dual a@ factor: needs a
-- typed walk of @Dual a ⊗ ApplyAssoc b c@ (Fuse/@c@ grid inside each cell).
cupCompose
  :: forall a b c
   . RepV (ComposeAssoc a b c)
  -> RepV (ComposeCupped a b c)
cupCompose = undefined

-- | Left-unitor on the right factor: @Dual a ⊗ (Unit ⊗ c) → Dual a ⊗ c@.
lunitCompose
  :: forall a b c
   . ( KnownDualAtomRep (Dual a)
     , KnownAtomRep c
     )
  => RepV (ComposeCupped a b c)
  -> RepV (Mor a c)
lunitCompose = go (symRepSing @(Dual a))
  where
    cSing = symRepSing @c

    go
      :: forall d
       . SRep d
      -> RepV (Tensor d (Tensor Unit c))
      -> RepV (Tensor d c)
    go SRepNil RNil = RNil
    go (SRepCons @_ @_ @dRest (SDualI (SAtomI @j)) (SMultDual (SMultAtom @m)) dRest) rv =
      let (row, restRv) =
            peelTensorOneAtomUnit @j @m @c @(Tensor dRest (Tensor Unit c)) cSing rv
       in appendRepV (lunitComposeRow @j @m cSing row) (go dRest restRv)
    go _ _ = error "lunitCompose: expected dual-atom spine"

-- | Peel @TensorOne@ of @Dual leaf × (Tensor Unit c)@ (length guided by @c@).
peelTensorOneAtomUnit
  :: forall j m c ys
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     )
  => SRep c
  -> RepV (Append (TensorOne '( 'Dual ('Atom j), 'DualM ('AtomM m)) (Tensor Unit c)) ys)
  -> ( RepV (TensorOne '( 'Dual ('Atom j), 'DualM ('AtomM m)) (Tensor Unit c))
     , RepV ys
     )
peelTensorOneAtomUnit SRepNil rv = (RNil, rv)
peelTensorOneAtomUnit (SRepCons SAtomI SMultAtom cRest) (RCons v rv) =
  let (xs, ys) = peelTensorOneAtomUnit @j @m cRest rv
   in (RCons v xs, ys)
peelTensorOneAtomUnit _ _ = error "peelTensorOneAtomUnit: expected atom spine"

-- | Apply 'lunitSector' on the right factor of each @Dual ⊗ (Unit ⊗ Atom)@ cell.
lunitComposeRow
  :: forall j m c
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     )
  => SRep c
  -> RepV (TensorOne '( 'Dual ('Atom j), 'DualM ('AtomM m)) (Tensor Unit c))
  -> RepV (TensorOne '( 'Dual ('Atom j), 'DualM ('AtomM m)) c)
lunitComposeRow SRepNil RNil = RNil
lunitComposeRow (SRepCons (SAtomI @k) (SMultAtom @n) cRest) (RCons t tRest) =
  let cell =
        t
          :: ToVSector ('Dual ('Atom j)) ('DualM ('AtomM m))
               ⊗ ToVSector ('Tensor ('Atom 0) ('Atom k)) ('Prod ('AtomM 1) ('AtomM n))
      out =
        (id ⊗^ arr (LinearFunction (lunitSector @k @n))) $ cell
   in RCons out (lunitComposeRow @j @m cRest tRest)
lunitComposeRow _ _ = error "lunitComposeRow: expected atom spine"

-- | Compact-closed composition @Hom(b,c) × Hom(a,b) → Hom(a,c)@.
composeMor
  :: forall a b c
   . ( KnownAtomRep a
     , KnownAtomRep b
     , KnownAtomRep c
     , KnownDualAtomRep (Dual a)
     )
  => RepV (Mor b c)
  -> RepV (Mor a b)
  -> RepV (Mor a c)
composeMor g f =
  lunitCompose @a @b @c
    (cupCompose @a @b @c
      (assocCompose @a @b @c (tensorCompose @a @b @c f g)))

instance Category Sym where
  type Object Sym a = (KnownAtomRep a, KnownDualAtomRep (Dual a))

  id :: forall a. Object Sym a => Sym a a
  id = Sym (idMor @a)

  (.) :: forall a b c
      . ( Object Sym a
        , Object Sym b
        , Object Sym c
        )
     => Sym b c
     -> Sym a b
     -> Sym a c
  Sym g . Sym f = Sym (composeMor @a @b @c g f)

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

-- | Swap irrep legs on @((C m ⊗ C j₁) ⊗ C j₂)@ (copy leg fixed).
swapIrrepTensorSector
  :: forall m j1 j2
   . ( KnownNat m
     , KnownNat j1
     , KnownNat j2
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     )
  => ((C m ⊗ C (IrrepDim j1)) ⊗ C (IrrepDim j2))
  -> ((C m ⊗ C (IrrepDim j2)) ⊗ C (IrrepDim j1))
swapIrrepTensorSector sec =
  (lassocMap . (id ⊗^ swapMap) . rassocMap) $ sec

-- | Swap both copy×irrep blocks @((C m₁ ⊗ C j₁) ⊗ (C m₂ ⊗ C j₂))@.
swapTensorProductSector
  :: forall m n j1 j2
   . ( KnownNat m
     , KnownNat n
     , KnownNat j1
     , KnownNat j2
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     )
  => (C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2))
  -> (C n ⊗ C (IrrepDim j2)) ⊗ (C m ⊗ C (IrrepDim j1))
swapTensorProductSector sec = swapMap $ sec

--------------------------------------------------------------------------------
-- Dual (term-level)
--
-- Map primal sectors into 'DualVector' payloads matching
-- @ToVSector ('Dual e) ('DualM μ)@. CS + @√(j+1)@ identification back to
-- primal atoms is 'undualAtomAtomM' in Fuse — not here.
--------------------------------------------------------------------------------

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
  -> ToVSector ('Dual ('Atom j)) ('DualM ('AtomM m))
dualAtomAtomM v =
  fromLinearForm
    -+$> ( arr (LinearFunction ((v <.>)))
             :: ToVSector ('Atom j) ('AtomM m) +> Complex Double
         )

-- | Dual of an atom spine (@r ↦ Dual r@), driven by 'SRep'.
dual
  :: forall rs
   . KnownAtomRep rs
  => RepV rs
  -> RepV (Dual rs)
dual = go (symRepSing @rs)
  where
    go :: forall rs'. SRep rs' -> RepV rs' -> RepV (Dual rs')
    go SRepNil RNil = RNil
    go (SRepCons (SAtomI @j) (SMultAtom @m) rest) (RCons v rs) =
      RCons (dualAtomAtomM @j @m v) (go rest rs)
    go _ _ = error "dual: expected atom spine"

-- | Sector-level braid payload (@BraidIrrep@ / @BraidMult@).
braidSector
  :: SIrrep e
  -> SMult μ
  -> ToVSector e μ
  -> ToVSector (BraidIrrep e) (BraidMult μ)
braidSector SAtomI SMultAtom v = v
braidSector (SAtomI @j) (SMultProd (SMultAtom @m) (SMultAtom @n)) v =
  swapCopyProductSector @m @n @(IrrepDim j) v
braidSector (STensorI (SAtomI @j1) (SAtomI @j2)) (SMultAtom @m) v =
  swapIrrepTensorSector @m @j1 @j2 v
braidSector (STensorI (SAtomI @j1) (SAtomI @j2)) (SMultProd (SMultAtom @m) (SMultAtom @n)) v =
  swapTensorProductSector @m @n @j1 @j2 v
braidSector (SDualI SAtomI) (SMultDual SMultAtom) v = v
braidSector _ _ _ =
  error "braidSector: unsupported irrep/mult shape"

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
-- @j@ is in an instance head. Non-atom sectors are dropped via an overlappable
-- catch-all; atom instances are overlapping.
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

-- | Braid a distributed tensor rep (@'Tensor'@).
braidTensor
  :: forall r s
   . KnownSymRep (Tensor r s)
  => RepV (Tensor r s)
  -> RepV (Braid (Tensor r s))
braidTensor = braid

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

-- | Leaf braiding @r ⊗ s → s ⊗ r@ on a fused pair (@fuse ∘ braid ≅ rmove ∘ fuse@).
rmove
  :: forall j1 j2 r s
   . ( KnownNat j1
     , KnownNat j2
     , KnownSymRep (Fuse (Tensor r s))
     , RmoveTarget j1 j2 (Fuse (Tensor r s)) ~ Fuse (Braid (Tensor r s))
     )
  => RepV (Fuse (Tensor r s))
  -> RepV (Fuse (Braid (Tensor r s)))
rmove = rmoveSpine @j1 @j2 @(Fuse (Tensor r s))

-- | Same as 'rmove' on a distributed tensor rep (@'Tensor'@).
rmoveTensor
  :: forall j1 j2 r s
   . ( KnownNat j1
     , KnownNat j2
     , KnownSymRep (Fuse (Tensor r s))
     , RmoveTarget j1 j2 (Fuse (Tensor r s)) ~ Fuse (Braid (Tensor r s))
     )
  => RepV (Fuse (Tensor r s))
  -> RepV (Fuse (Braid (Tensor r s)))
rmoveTensor = rmove @j1 @j2 @r @s
