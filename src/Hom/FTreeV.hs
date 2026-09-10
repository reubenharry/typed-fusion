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

-- | Term-level 'FTreeV' spines and CG fuse ('fuseFTreesTerm').
module Hom.FTreeV
  ( FTreeV (..)
  , fTreeVToV
  , makeFTrees
  , appendFTreeV
  , FuseTreesGo (..)
  , fuseTrees
  , UnfuseTreesGo (..)
  , unfuseTrees
  , FuseFTreesTermC
  , FuseFTreesOneTermC
  , KnownHomTrees
  , fuseFTreesTerm
  , FuseFTreesIdC
  , FuseFTreesOneIdC
  , idHomFTrees
  , scaleFTreeV
  , approxFTreeV
  , filterTrivialFTreeV
  , embedTrivialFTreeV
  ) where

import Control.Arrow.Constrained (($))
import Data.Complex (Complex, magnitude)
import Data.Kind (Constraint)
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.Type.Ord (OrderingI (..))
import Data.VectorSpace
  ( AdditiveGroup (zeroV, (^+^))
  , Scalar
  , VectorSpace ((*^))
  )
import qualified Data.Vector.Storable as VS
import Symmetry.Tensor (TensorIrrepRepSU2)
import Hom.Expr
import Hom.Singletons
import Hom.TypeLevel
import GHC.TypeLits (KnownNat, Nat, sameNat)
import GHC.TypeNats (cmpNat)
import Math.LinearMap.Category (TensorSpace, type (⊗), (⊗))
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static (C, konst)
import Symmetry.CG.SU2 (fuseCGChannel, unfuseCGChannel)
import Symmetry.Utils (Append)

import Prelude hiding (($))

-- | Spine of root vectors, indexed by type-level 'FTrees'.
data FTreeV (ts :: FTrees Nat) where
  FNil :: FTreeV '[]
  FCons
    :: forall t rest
     . ToVTree t
    -> FTreeV rest
    -> FTreeV (t ': rest)

-- | Forgetful map: nonempty 'FTreeV' → 'ToVFTrees'.
fTreeVToV :: forall ts. KnownFTrees ts => FTreeV ts -> ToVFTrees ts
fTreeVToV = go (fTreesSing @ts)
  where
    go :: forall ts'. SFTrees ts' -> FTreeV ts' -> ToVFTrees ts'
    go (SFTreesCons _ SFTreesNil) (FCons v FNil) = v
    go (SFTreesCons _ sRest@(SFTreesCons {})) (FCons v rest) =
      (v, go sRest rest)
    go _ _ = error "fTreeVToV: expected nonempty KnownFTrees"

-- | Inverse of 'fTreeVToV'.
makeFTrees :: forall ts. KnownFTrees ts => ToVFTrees ts -> FTreeV ts
makeFTrees = go (fTreesSing @ts)
  where
    go :: forall ts'. SFTrees ts' -> ToVFTrees ts' -> FTreeV ts'
    go (SFTreesCons (_ :: SFTree t) SFTreesNil) v =
      FCons @t v FNil
    go (SFTreesCons (_ :: SFTree t) sRest@(SFTreesCons {})) (v, rest) =
      FCons @t v (go sRest rest)
    go _ _ = error "makeFTrees: expected nonempty KnownFTrees"

-- | Append two tree spines.
appendFTreeV
  :: FTreeV ts1
  -> FTreeV ts2
  -> FTreeV (Append ts1 ts2)
appendFTreeV FNil r2 = r2
appendFTreeV (FCons v rest) r2 =
  FCons v (appendFTreeV rest r2)

-- | Walk CG channels for a pair of trees → 'FTreeV' of @'From@ outcomes.
class FuseTreesGo (t1 :: FTree Nat) (t2 :: FTree Nat) (cg :: [(Nat, Nat)]) where
  fuseTreesGo
    :: C (IrrepDim (Root t1)) ⊗ C (IrrepDim (Root t2))
    -> FTreeV (FromCG t1 t2 cg)

instance FuseTreesGo t1 t2 '[] where
  fuseTreesGo _ = FNil

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
    FCons @('From j '(t1, t2))
      (fuseCGChannel @(Root t1) @(Root t2) @j $ v)
      (fuseTreesGo @t1 @t2 @rest v)

-- | CG-fuse two fusion trees into the channel list 'FuseTrees'.
fuseTrees
  :: forall t1 t2
   . ( KnownFTree t1
     , KnownFTree t2
     , FuseTreesGo t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))
     )
  => ToVTree t1 ⊗ ToVTree t2
  -> FTreeV (FuseTrees t1 t2)
fuseTrees =
  fuseTreesGo @t1 @t2 @(TensorIrrepRepSU2 (Root t1) (Root t2))

-- | Inverse of 'fuseTrees' on the CG image: sum channel embeddings.
class UnfuseTreesGo (t1 :: FTree Nat) (t2 :: FTree Nat) (cg :: [(Nat, Nat)]) where
  unfuseTreesGo
    :: FTreeV (FromCG t1 t2 cg)
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
  unfuseTreesGo FNil = zeroV

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
  unfuseTreesGo (FCons v rest) =
    (unfuseCGChannel @(Root t1) @(Root t2) @j $ v)
      ^+^ unfuseTreesGo @t1 @t2 @rest rest

-- | Unfuse a 'FuseTrees' spine back to the product of root spaces.
unfuseTrees
  :: forall t1 t2
   . ( KnownFTree t1
     , KnownFTree t2
     , UnfuseTreesGo t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))
     )
  => FTreeV (FuseTrees t1 t2)
  -> ToVTree t1 ⊗ ToVTree t2
unfuseTrees =
  unfuseTreesGo @t1 @t2 @(TensorIrrepRepSU2 (Root t1) (Root t2))

-- | Constraints for walking 'FuseFTrees' at the term level.
type family FuseFTreesTermC (rs :: FTrees Nat) (qs :: FTrees Nat) :: Constraint where
  FuseFTreesTermC '[] _ = ()
  FuseFTreesTermC (t1 ': rest) qs =
    ( FuseFTreesOneTermC t1 qs
    , FuseFTreesTermC rest qs
    )

-- | Forward bundle: Hom spine @FuseFTrees a b@ is known and fusible.
-- (Does not imply Mac Lane intermediates such as @FuseFTrees b (FuseFTrees b c)@.)
type KnownHomTrees (a :: FTrees Nat) (b :: FTrees Nat) =
  ( KnownFTrees a
  , KnownFTrees b
  , KnownFTrees (FuseFTrees a b)
  , FuseFTreesTermC a b
  )

type family FuseFTreesOneTermC (t1 :: FTree Nat) (qs :: FTrees Nat) :: Constraint where
  FuseFTreesOneTermC _ '[] = ()
  FuseFTreesOneTermC t1 (t2 ': rest) =
    ( KnownFTree t1
    , KnownFTree t2
    , KnownNat (Root t1)
    , KnownNat (Root t2)
    , KnownNat (IrrepDim (Root t1))
    , KnownNat (IrrepDim (Root t2))
    , TensorSpace (C (IrrepDim (Root t1)))
    , TensorSpace (C (IrrepDim (Root t2)))
    , Scalar (C (IrrepDim (Root t1))) ~ Complex Double
    , Scalar (C (IrrepDim (Root t2))) ~ Complex Double
    , FuseTreesGo t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))
    , FuseFTreesOneTermC t1 rest
    )

-- | Constraints to build the identity on @'FuseFTrees' ls rs@ (position-diagonal).
type family FuseFTreesIdC (ls :: FTrees Nat) (rs :: FTrees Nat) :: Constraint where
  FuseFTreesIdC '[] _ = ()
  FuseFTreesIdC (t1 ': rest) rs =
    ( FuseFTreesOneIdC t1 rs
    , FuseFTreesIdC rest rs
    )

type family FuseFTreesOneIdC (t1 :: FTree Nat) (qs :: FTrees Nat) :: Constraint where
  FuseFTreesOneIdC _ '[] = ()
  FuseFTreesOneIdC t1 (t2 ': rest) =
    ( KnownFTrees (FuseTrees t1 t2)
    , FuseFTreesOneIdC t1 rest
    )

-- | Hom channels for one leaf pair: singlet (@root = 0@) = 1, else 0.
homChannelsDiag
  :: forall t1 t2
   . KnownFTrees (FuseTrees t1 t2)
  => FTreeV (FuseTrees t1 t2)
homChannelsDiag = go (fTreesSing @(FuseTrees t1 t2))
  where
    go :: forall ts. SFTrees ts -> FTreeV ts
    go SFTreesNil = FNil
    go (SFTreesCons (t :: SFTree u) rest) =
      case t of
        SFrom @d _l _r ->
          case sameNat (Proxy @d) (Proxy @0) of
            Just Refl -> FCons @u (konst 1) (go rest)
            Nothing -> FCons @u zeroV (go rest)
        SIrrepTree {} ->
          error "homChannelsDiag: expected Hom From channels"

-- | Zero Hom channels for an off-diagonal leaf pair.
homChannelsZero
  :: forall t1 t2
   . KnownFTrees (FuseTrees t1 t2)
  => FTreeV (FuseTrees t1 t2)
homChannelsZero = go (fTreesSing @(FuseTrees t1 t2))
  where
    go :: forall ts. SFTrees ts -> FTreeV ts
    go SFTreesNil = FNil
    go (SFTreesCons t rest) =
      case t of
        SIrrepTree {} -> FCons zeroV (go rest)
        SFrom {} -> FCons zeroV (go rest)

-- | Identity on @'FuseFTrees' rs rs@: diagonal leaf-pair singlets = 1, zero
-- on cross blocks (cartesian 'FuseFTrees' layout).
idHomFTrees
  :: forall rs
   . ( KnownFTrees rs
     , FuseFTreesIdC rs rs
     )
  => FTreeV (FuseFTrees rs rs)
idHomFTrees = goLeft (fTreesSing @rs) 0
  where
    goLeft
      :: forall ls
       . FuseFTreesIdC ls rs
      => SFTrees ls
      -> Int
      -> FTreeV (FuseFTrees ls rs)
    goLeft SFTreesNil _ = FNil
    goLeft (SFTreesCons (_ :: SFTree t1) rest) i =
      appendFTreeV
        (goOne @t1 (fTreesSing @rs) i 0)
        (goLeft rest (i + 1))

    goOne
      :: forall t1 qs
       . FuseFTreesOneIdC t1 qs
      => SFTrees qs
      -> Int
      -> Int
      -> FTreeV (FuseFTreesOne t1 qs)
    goOne SFTreesNil _ _ = FNil
    goOne (SFTreesCons (_ :: SFTree t2) rest) i j =
      appendFTreeV
        ( if i == j
            then homChannelsDiag @t1 @t2
            else homChannelsZero @t1 @t2
        )
        (goOne @t1 rest i (j + 1))

-- | Cartesian fuse of two 'FTreeV' spines (matches 'FuseFTrees').
fuseFTreesTerm
  :: forall rs qs
   . ( KnownFTrees rs
     , KnownFTrees qs
     , FuseFTreesTermC rs qs
     )
  => FTreeV rs
  -> FTreeV qs
  -> FTreeV (FuseFTrees rs qs)
fuseFTreesTerm rs qs =
  go (fTreesSing @rs) rs (fTreesSing @qs) qs
  where
    go
      :: forall rs' qs'
       . FuseFTreesTermC rs' qs'
      => SFTrees rs'
      -> FTreeV rs'
      -> SFTrees qs'
      -> FTreeV qs'
      -> FTreeV (FuseFTrees rs' qs')
    go SFTreesNil FNil _ _ = FNil
    go
      (SFTreesCons (_ :: SFTree t1) rRest)
      (FCons v1 rRestV)
      qSing
      q =
      appendFTreeV
        (fuseRepOneTerm @t1 v1 qSing q)
        (go rRest rRestV qSing q)

    fuseRepOneTerm
      :: forall t1 qs'
       . FuseFTreesOneTermC t1 qs'
      => ToVTree t1
      -> SFTrees qs'
      -> FTreeV qs'
      -> FTreeV (FuseFTreesOne t1 qs')
    fuseRepOneTerm _ SFTreesNil FNil = FNil
    fuseRepOneTerm v1 (SFTreesCons (_ :: SFTree t2) qRest) (FCons v2 rest) =
      appendFTreeV
        (fuseTrees @t1 @t2 (v1 ⊗ v2))
        (fuseRepOneTerm @t1 v1 qRest rest)

scaleFTreeV
  :: forall ts
   . KnownFTrees ts
  => Complex Double
  -> FTreeV ts
  -> FTreeV ts
scaleFTreeV s = go (fTreesSing @ts)
  where
    go :: SFTrees ts' -> FTreeV ts' -> FTreeV ts'
    go SFTreesNil FNil = FNil
    go (SFTreesCons t rest) (FCons v rs) =
      case t of
        SIrrepTree {} -> FCons (s *^ v) (go rest rs)
        SFrom {} -> FCons (s *^ v) (go rest rs)

approxFTreeV
  :: forall ts
   . KnownFTrees ts
  => FTreeV ts
  -> FTreeV ts
  -> Bool
approxFTreeV = go (fTreesSing @ts)
  where
    closeVec a b =
      let da = toArray a
          db = toArray b
       in VS.all (\z -> magnitude z < 1e-9) (VS.zipWith (-) da db)
    go :: SFTrees ts' -> FTreeV ts' -> FTreeV ts' -> Bool
    go SFTreesNil FNil FNil = True
    go (SFTreesCons t rest) (FCons a as) (FCons b bs) =
      case t of
        SIrrepTree {} -> closeVec a b && go rest as bs
        SFrom {} -> closeVec a b && go rest as bs
    go _ _ _ = False


-- | Keep trivial-root channels of a 'FTreeV' spine ('FilterTrivial').
--
-- Singleton walk + 'cmpNat': refines @CmpNat j 0@ so 'FilterTrivial' reduces
-- in each branch (no method class / overlapping instances).
filterTrivialFTreeV
  :: forall ts
   . KnownFTrees ts
  => FTreeV ts
  -> FTreeV (FilterTrivial ts)
filterTrivialFTreeV = go (fTreesSing @ts)
  where
    go :: forall ts'. SFTrees ts' -> FTreeV ts' -> FTreeV (FilterTrivial ts')
    go SFTreesNil FNil = FNil
    go (SFTreesCons t rest) (FCons v rs) =
      case t of
        SIrrepTree @j ->
          case cmpNat (Proxy @j) (Proxy @0) of
            EQI -> FCons @('IrrepTree 0) v (go rest rs)
            GTI -> go rest rs
            LTI -> go rest rs
        SFrom @j (_ :: SFTree l) (_ :: SFTree r) ->
          case cmpNat (Proxy @j) (Proxy @0) of
            EQI -> FCons @('From 0 '(l, r)) v (go rest rs)
            GTI -> go rest rs
            LTI -> go rest rs

-- | Embed a trivial-sector spine back into the full 'FuseFTrees' (zeros elsewhere).
embedTrivialFTreeV
  :: forall ts
   . KnownFTrees ts
  => FTreeV (FilterTrivial ts)
  -> FTreeV ts
embedTrivialFTreeV = go (fTreesSing @ts)
  where
    go :: forall ts'. SFTrees ts' -> FTreeV (FilterTrivial ts') -> FTreeV ts'
    go SFTreesNil FNil = FNil
    go (SFTreesCons t rest) fr =
      case t of
        SIrrepTree @j ->
          case cmpNat (Proxy @j) (Proxy @0) of
            EQI ->
              case fr of
                FCons v rs -> FCons @('IrrepTree 0) v (go rest rs)
            GTI -> FCons @('IrrepTree j) zeroV (go rest fr)
            LTI -> FCons @('IrrepTree j) zeroV (go rest fr)
        SFrom @j (_ :: SFTree l) (_ :: SFTree r) ->
          case cmpNat (Proxy @j) (Proxy @0) of
            EQI ->
              case fr of
                FCons v rs -> FCons @('From 0 '(l, r)) v (go rest rs)
            GTI -> FCons @('From j '(l, r)) zeroV (go rest fr)
            LTI -> FCons @('From j '(l, r)) zeroV (go rest fr)
