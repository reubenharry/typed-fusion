{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoStarIsType #-}

module SU2 where



import Data.Kind (Type)
import GHC.TypeLits
import Numeric.LinearAlgebra.Static (M, Sized (..), C)
import Orphans (SU2Irreps, IrrepSU2)
import Linear.V (V)
import Utils (HList)


-- todo: the Sector type should really have an abstract notion of a linear map

--------------------------------------------------------------------------------
-- Representation type
--------------------------------------------------------------------------------

type Irrep = Nat
type Multiplicity = Nat

type family Dim (m :: Multiplicity) :: Nat where
  Dim p = p

type Mat = M
type Vector = C
type Product = V

type family RepToVectors
  (r :: [(Irrep, Multiplicity)])
  :: [Type] where

  RepToVectors '[] =
    '[]

  RepToVectors ('(i,m) ': rs) =
    Product (Dim m) (IrrepSU2 i) ': RepToVectors rs

newtype Representation (r :: [(SU2Irreps, Multiplicity)]) = Representation (HList (RepToVectors r))

deriving instance Show (HList (RepToVectors r)) => Show (Representation r)


--------------------------------------------------------------------------------
-- Tensor product rule
--
-- j1 ⊗ j2 = |j1-j2| ⊕ |j1-j2|+2 ⊕ ... ⊕ j1+j2
--
-- where j is encoded as twice the physical spin.
--------------------------------------------------------------------------------

type family TensorIrrepRepSU2
  (j1 :: SU2Irreps)
  (j2 :: SU2Irreps)
  :: [(SU2Irreps, Multiplicity)] where

  TensorIrrepRepSU2 j1 j2 =
    ToMultiplicityOneList
      (RangeStep2 (AbsDiff j1 j2) (j1 + j2))

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

type family ToMultiplicityOneList
  (js :: [SU2Irreps])
  :: [(SU2Irreps, Multiplicity)] where

  ToMultiplicityOneList '[] =
    '[]

  ToMultiplicityOneList (j ': js) =
    '(j, 1) ': ToMultiplicityOneList js

type family AbsDiff (a :: Nat) (b :: Nat) :: Nat where
  AbsDiff a b =
    AbsDiffCmp (CmpNat a b) a b

type family AbsDiffCmp
  (o :: Ordering)
  (a :: Nat)
  (b :: Nat)
  :: Nat where

  AbsDiffCmp 'LT a b = b - a
  AbsDiffCmp 'EQ a b = 0
  AbsDiffCmp 'GT a b = a - b

type family RangeStep2
  (lo :: Nat)
  (hi :: Nat)
  :: [Nat] where

  RangeStep2 lo hi =
    RangeStep2Cmp (CmpNat lo hi) lo hi

type family RangeStep2Cmp
  (o :: Ordering)
  (lo :: Nat)
  (hi :: Nat)
  :: [Nat] where

  RangeStep2Cmp 'GT lo hi =
    '[]

  RangeStep2Cmp 'EQ lo hi =
    '[lo]

  RangeStep2Cmp 'LT lo hi =
    lo ': RangeStep2 (lo + 2) hi


type family
  (a :: Type)
  ⊗
  (b :: Type)
  :: Type where

   (IrrepSU2 j1) ⊗ (IrrepSU2 j2) =
    Representation (TensorIrrepRepSU2 j1 j2)

foo :: IrrepSU2 2 ⊗ IrrepSU2 4
foo = Representation undefined


