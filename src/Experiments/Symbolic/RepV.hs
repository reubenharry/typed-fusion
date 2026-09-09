{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Term-level 'RepV' spines and CG fuse ('fuseRepTerm').
module Experiments.Symbolic.RepV
  ( RepV (..)
  , repVToV
  , vToRepV
  , appendRepV
  , FuseTreesGo (..)
  , fuseTrees
  , UnfuseTreesGo (..)
  , unfuseTrees
  , FuseRepTermC
  , FuseRepOneTermC
  , fuseRepTerm
  , scaleRepV
  , approxRepV
  , FilterTrivialC (..)
  ) where

import Control.Arrow.Constrained (($))
import Data.Complex (Complex, magnitude)
import Data.Kind (Constraint)
import Data.VectorSpace
  ( AdditiveGroup (zeroV, (^+^))
  , Scalar
  , VectorSpace ((*^))
  )
import qualified Data.Vector.Storable as VS
import Experiments.SU2 (TensorIrrepRepSU2)
import Experiments.Symbolic.Expr
import Experiments.Symbolic.Singletons
import Experiments.Symbolic.TypeLevel
import GHC.TypeLits (CmpNat, KnownNat, Nat)
import Math.LinearMap.Category (TensorSpace, type (⊗), (⊗))
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static (C)
import Symmetry.CG.SU2 (fuseCGChannel, unfuseCGChannel)
import Symmetry.Utils (Append)

import Prelude hiding (($))

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

-- | Walk CG channels for a pair of trees → 'RepV' of @'From@ outcomes.
class FuseTreesGo (t1 :: Irrep) (t2 :: Irrep) (cg :: [(Nat, Nat)]) where
  fuseTreesGo
    :: C (IrrepDim (Root t1)) ⊗ C (IrrepDim (Root t2))
    -> RepV (FromCG t1 t2 cg)

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
    RCons @('From j '(t1, t2))
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

-- | Inverse of 'fuseTrees' on the CG image: sum channel embeddings.
class UnfuseTreesGo (t1 :: Irrep) (t2 :: Irrep) (cg :: [(Nat, Nat)]) where
  unfuseTreesGo
    :: RepV (FromCG t1 t2 cg)
    -> C (IrrepDim (Root t1)) ⊗ C (IrrepDim (Root t2))

instance
  ( KnownNat (Root t1)
  , KnownNat (Root t2)
  , KnownNat (IrrepDim (Root t1))
  , KnownNat (IrrepDim (Root t2))
  , AdditiveGroup
      ( C (IrrepDim (Root t1)) ⊗ C (IrrepDim (Root t2)) )
  ) =>
  UnfuseTreesGo t1 t2 '[]
  where
  unfuseTreesGo RNil = zeroV

instance
  ( UnfuseTreesGo t1 t2 rest
  , KnownNat j
  , KnownNat (Root t1)
  , KnownNat (Root t2)
  , KnownNat (IrrepDim (Root t1))
  , KnownNat (IrrepDim (Root t2))
  , KnownNat (IrrepDim j)
  , AdditiveGroup
      ( C (IrrepDim (Root t1)) ⊗ C (IrrepDim (Root t2)) )
  ) =>
  UnfuseTreesGo t1 t2 ('(j, m) ': rest)
  where
  unfuseTreesGo (RCons v rest) =
    (unfuseCGChannel @(Root t1) @(Root t2) @j $ v)
      ^+^ unfuseTreesGo @t1 @t2 @rest rest

-- | Unfuse a 'FuseTrees' spine back to the product of root spaces.
unfuseTrees
  :: forall t1 t2
   . ( KnownIrrep t1
     , KnownIrrep t2
     , UnfuseTreesGo t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))
     )
  => RepV (FuseTrees t1 t2)
  -> ToVTree t1 ⊗ ToVTree t2
unfuseTrees =
  unfuseTreesGo @t1 @t2 @(TensorIrrepRepSU2 (Root t1) (Root t2))

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
  go (repSing @rs) rs (repSing @qs) qs
  where
    go
      :: forall rs' qs'
       . FuseRepTermC rs' qs'
      => SRep rs'
      -> RepV rs'
      -> SRep qs'
      -> RepV qs'
      -> RepV (FuseRep rs' qs')
    go SRepNil RNil _ _ = RNil
    go
      (SRepCons (_ :: SIrrepTree t1) rRest)
      (RCons v1 rRestV)
      qSing
      q =
      appendRepV
        (fuseRepOneTerm @t1 v1 qSing q)
        (go rRest rRestV qSing q)

    fuseRepOneTerm
      :: forall t1 qs'
       . FuseRepOneTermC t1 qs'
      => ToVTree t1
      -> SRep qs'
      -> RepV qs'
      -> RepV (FuseRepOne t1 qs')
    fuseRepOneTerm _ SRepNil RNil = RNil
    fuseRepOneTerm v1 (SRepCons (_ :: SIrrepTree t2) qRest) (RCons v2 rest) =
      appendRepV
        (fuseTrees @t1 @t2 (v1 ⊗ v2))
        (fuseRepOneTerm @t1 v1 qRest rest)

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
        SI {} -> RCons (s *^ v) (go rest rs)
        SFrom {} -> RCons (s *^ v) (go rest rs)

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
        SI {} -> closeVec a b && go rest as bs
        SFrom {} -> closeVec a b && go rest as bs
    go _ _ _ = False


-- | Term-level filter / embed for 'FilterTrivial'.
--
-- Non-trivial roots use @CmpNat j 0 ~ GT@ so 'FilterTrivial' reduces.
-- Zero-root instances are OVERLAPPING; non-zero are OVERLAPPABLE.
class FilterTrivialC (ts :: Rep) where
  filterTrivialRepV :: RepV ts -> RepV (FilterTrivial ts)
  embedTrivialRepV :: RepV (FilterTrivial ts) -> RepV ts

instance FilterTrivialC '[] where
  filterTrivialRepV RNil = RNil
  embedTrivialRepV RNil = RNil

instance {-# OVERLAPPING #-} FilterTrivialC rest => FilterTrivialC ('I 0 ': rest) where
  filterTrivialRepV (RCons v rs) =
    RCons @('I 0) v (filterTrivialRepV @rest rs)
  embedTrivialRepV (RCons v rs) =
    RCons @('I 0) v (embedTrivialRepV @rest rs)

instance {-# OVERLAPPABLE #-}
  ( KnownNat j
  , CmpNat j 0 ~ 'GT
  , KnownNat (IrrepDim j)
  , FilterTrivialC rest
  ) =>
  FilterTrivialC ('I j ': rest)
  where
  filterTrivialRepV (RCons _ rs) = filterTrivialRepV @rest rs
  embedTrivialRepV fr =
    RCons @('I j) zeroV (embedTrivialRepV @rest fr)

instance {-# OVERLAPPING #-}
  ( KnownIrrep ('From 0 '(l, r))
  , FilterTrivialC rest
  ) =>
  FilterTrivialC ('From 0 '(l, r) ': rest)
  where
  filterTrivialRepV (RCons v rs) =
    RCons @('From 0 '(l, r)) v (filterTrivialRepV @rest rs)
  embedTrivialRepV (RCons v rs) =
    RCons @('From 0 '(l, r)) v (embedTrivialRepV @rest rs)

instance {-# OVERLAPPABLE #-}
  ( KnownNat j
  , CmpNat j 0 ~ 'GT
  , KnownNat (IrrepDim j)
  , KnownIrrep l
  , KnownIrrep r
  , FilterTrivialC rest
  ) =>
  FilterTrivialC ('From j '(l, r) ': rest)
  where
  filterTrivialRepV (RCons _ rs) = filterTrivialRepV @rest rs
  embedTrivialRepV fr =
    RCons @('From j '(l, r)) zeroV (embedTrivialRepV @rest fr)
