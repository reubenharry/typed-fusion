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
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}

module Experiments.General where
import Control.Functor.Constrained (Functor(fmap))
import Orphans (U1Irreps, SU2Irreps)
import Data.Kind (Type)
import GHC.TypeLits (Nat, type (+), KnownNat)
import Numeric.LinearAlgebra.Static (C, Sized (unwrap, fromList))
import Experiments.Experiment2 (Multiplicity, Product, Dim)
import Experiments.SU2 (TensorIrrepRepSU2)
import Utils (Add, HList (..), Z(..), getZ, KnownZ, Negate, Append, Scale)
import Data.Singletons (Sing)
import Data.Data (Proxy)
import Data.Singletons.TH (genSingletons)
import Data.VectorSpace ((*^))
import Data.Complex (Complex(..))
import Data.Vector.Storable ((!))
import Control.Category.Constrained (Category)
import Control.Category.Constrained.Prelude (Category(..))
import Prelude hiding ((.))
import Math.LinearMap.Category hiding (type Tensor, type (⊗))

data Group = U1 | SU2
$(genSingletons [''Group])

type family GroupElement (g :: Group) :: Type where
  GroupElement U1 = Double
  GroupElement SU2 = (Double, Double)

type family Irreps (g :: Group) :: Type where
  Irreps U1 = Z
  Irreps SU2 = Nat

type IrrepDim :: forall (g :: Group) -> Irreps g -> Nat
type family IrrepDim (g :: Group) (p :: Irreps g) :: Nat where
  IrrepDim U1 p = 1
  IrrepDim SU2 p = p + 1
newtype Irrep (g :: Group) (p :: Irreps g) = Irrep { unGIrrep :: C (IrrepDim g p) }

newtype Representation (g :: Group) (r :: [(Irreps g, Multiplicity)]) = Representation (HList (RepToVectors g r))

deriving instance KnownNat (IrrepDim g p) => Show (Irrep g p)



type TensorIrrepRep :: forall (g :: Group) -> Irreps g -> Irreps g -> [(Irreps g, Multiplicity)]
type family TensorIrrepRep (g :: Group) (j1 :: Irreps g)
  (j2 :: Irreps g)
  :: [(Irreps g, Multiplicity)] where

  TensorIrrepRep SU2 (j1 :: Irreps SU2) j2 = TensorIrrepRepSU2 j1 j2
  TensorIrrepRep U1 (j1 :: Irreps U1) j2 = '[ '(Add j1 j2, 1) ]

type RepToVectors :: forall (g :: Group) -> [(Irreps g, Multiplicity)] -> [Type]
type family RepToVectors
  (g :: Group) (r :: [(Irreps g, Multiplicity)])
  :: [Type] where

  RepToVectors SU2 '[] =
    '[]

  RepToVectors SU2 ('(i,m) ': rs) =
    Product (Dim m) (Irrep SU2 i) ': RepToVectors SU2 rs

  RepToVectors U1 '[] =
    '[]

  RepToVectors U1 ('(i,m) ': rs) =
    Product (Dim m) (Irrep U1 i) ': RepToVectors U1 rs


foo :: Irrep SU2 2 ⊗ Irrep SU2 4
foo = Representation undefined

foo' :: Irrep U1 (Pos 2) ⊗ Irrep U1 (Pos 2)
foo' = Representation undefined


type DualIrrep :: forall (g :: Group) -> Irreps g -> Irreps g
type family DualIrrep (g :: Group) (p :: Irreps g) where
  DualIrrep U1 q  = Negate q
  DualIrrep SU2 j = j

type DualRep :: forall (g :: Group) -> [(Irreps g, Multiplicity)] -> [(Irreps g, Multiplicity)]
type family DualRep (g :: Group) (r :: [(Irreps g, Multiplicity)]) where
  DualRep U1 '[] = '[]
  DualRep U1 ('(i,m) ': rs) =
    '(DualIrrep U1 i, m) ': DualRep U1 rs
  DualRep SU2 '[] = '[]
  DualRep SU2 ('(i,m) ': rs) =
    '(DualIrrep SU2 i, m) ': DualRep SU2 rs


type Tensor :: forall (g :: Group) -> [(Irreps g, Multiplicity)] -> [(Irreps g, Multiplicity)] -> [(Irreps g, Multiplicity)]
type family Tensor
  (g :: Group)
  (r :: [(Irreps g, Multiplicity)])
  (q :: [(Irreps g, Multiplicity)])
  :: [(Irreps g, Multiplicity)] where

  Tensor U1 '[] q =
    '[]

  Tensor SU2 '[] q =
    '[]


  Tensor U1 ('(i,m) ': rs) q =
    Append
      (TensorOne U1 '(i,m) q)
      (Tensor U1 rs q)

  Tensor SU2 ('(i,m) ': rs) q =
    Append
      (TensorOne SU2 '(i,m) q)
      (Tensor SU2 rs q)


type TensorOne :: forall (g :: Group) -> (Irreps g, Multiplicity) -> [(Irreps g, Multiplicity)] -> [(Irreps g, Multiplicity)]
type family TensorOne
  (g :: Group)
  (x :: (Irreps g, Multiplicity))
  (q :: [(Irreps g, Multiplicity)])
  :: [(Irreps g, Multiplicity)] where

  TensorOne U1 x '[] =
    '[]

  TensorOne U1 '(i,m) ('(j,n) ': qs) =

    Append
    '[ '( Add i j
     , Scale m n
     )]
    (TensorOne U1 '(i,m) qs)

  TensorOne SU2 x '[] =
    '[]

  TensorOne SU2 '(i,m) ('(j,n) ': qs) =
    Append
    (TensorIrrepRepSU2 i j) -- wrong! fix multiplicities!
    (TensorOne SU2 '(i,m) qs)



type family
  (a :: Type)
  ⊗
  (b :: Type)
  :: Type where

   (Irrep g j1) ⊗ (Irrep g j2) =
    Representation g (  TensorIrrepRep g j1 j2)

   Representation g r ⊗ Representation g q =
    Representation g (Tensor g r q)




type FilterNonTrivial :: forall (g :: Group) -> [(Irreps g, Multiplicity)] -> [(Irreps g, Multiplicity)]
type family FilterNonTrivial
  (g :: Group)
  (r :: [(Irreps g, Multiplicity)])
  :: [(Irreps g, Multiplicity)] where

  FilterNonTrivial U1 '[] =
    '[]

  FilterNonTrivial U1 ('( 'Zero,m) ': rs) =
    '( 'Zero,m) ': FilterNonTrivial U1 rs

  FilterNonTrivial U1 ('(i,m) ': rs) =
    FilterNonTrivial U1 rs

  FilterNonTrivial SU2 '[] =
    '[]

  FilterNonTrivial SU2 ('( 0,m) ': rs) =
    '( 0,m) ': FilterNonTrivial SU2 rs

  FilterNonTrivial SU2 ('(i,m) ': rs) =
    FilterNonTrivial SU2 rs



type family
  (a :: Type)
  `Intertwiner`
  (b :: Type)
  :: Type where

   (Representation g r) `Intertwiner` (Representation g q) =
    HList (RepToVectors g (FilterNonTrivial g
      (
        Tensor g (DualRep g r) q)))

tstR :: Representation U1 '[ '(Pos 1, 2)] ⊗ Representation U1 '[ '(Pos 2, 1)]
tstR = undefined

tstR' :: Representation SU2 '[ '( 1, 2), '( 2, 1)] ⊗ Representation SU2 '[ '( 2, 1), '( 3, 1)]
tstR' = undefined
-- type Re g 

newtype MultiIrreps (g :: Group) = MultiIrreps { getMultiIrreps :: [(Irreps g, Nat)] }
-- type MultiIrreps (g :: Group) = '[ '(Irreps g, Nat)]

type family GetGroup ( r :: MultiIrreps g) :: Group where
  GetGroup (r :: MultiIrreps g) = g

type family GetIrreps ( r :: MultiIrreps g) :: [(Irreps g, Nat)] where
--   GetIrreps (MultiIrreps r :: MultiIrreps g) = r

newtype 
  (a :: MultiIrreps g)
  `IntertwinerA`
  (b :: MultiIrreps g)
  = Sectors (HList (RepToVectors (GetGroup a) (Tensor (GetGroup a) (GetIrreps a) (GetIrreps b))))

-- type family
--   (a :: MultiIrreps g)
--   `IntertwinerA`
--   (b :: MultiIrreps g)
--   :: Type where

--    a `IntertwinerA` b = HList (RepToVectors (GetGroup a) (Tensor (GetGroup a) (GetIrreps a) (GetIrreps b)))
    
    -- Tensor (GetGroup a) (DualRep (GetGroup a) a) b
    -- HList (RepToVectors (FilterNonTrivial a (Tensor a (DualRep a a) b)))


type family
  (a :: Type)
  `Map`
  (b :: Type)
  :: Type where

   (Representation g r) `Map` (Representation g q) =
    HList (RepToVectors g
      (
        Tensor g (DualRep g r) q))

testIntertwinerU1 :: Representation U1 '[ '(Pos 1, 2)] `Intertwiner` Representation U1 '[ '(Pos 3, 1)]
testIntertwinerU1 = HNil

testIntertwinerSU2 :: Representation SU2 '[ '(1, 2)] `Intertwiner` Representation SU2 '[ '( 3, 1)]
testIntertwinerSU2 = HNil

x1 :: Irrep U1 (Pos 2)
x1 = Irrep $ fromList [5]

x2 :: Irrep U1 (Pos 1)
x2 =  Irrep $ fromList [6]

x3 :: Irrep U1 (Pos 3)
x3 = (tensor x2) x1

x4 :: Irrep U1 (Pos 2)
x4 = action 1 x1

x5 :: Irrep U1 (Pos 3)
x5 = (action 1 . (tensor x2)) x1


x5' :: Irrep U1 (Pos 3)
x5' = (tensor x2 . action 1) x1

class  (g :: Group) `ActsOn` (p :: Irreps g) where
  action :: GroupElement g -> Irrep g p -> Irrep g p

instance forall q. KnownZ q =>  U1 `ActsOn` q where
  action theta (Irrep v) =
    let 
        n = getZ @q
        n' = fromIntegral n
        scalar = exp ((0 :+ 1) * (theta * n' :+ 0))
    in Irrep (scalar *^ v) 


tensor :: forall a b . Irrep U1 a -> Irrep U1 b -> Irrep U1 (Add a b)
tensor (Irrep a) (Irrep b) = Irrep $ fromList [c * d] where 
  c = unwrap a ! 0
  d = unwrap b ! 0

-- get intertwiners to act on vector spaces
-- todo: get intertwiner and work out how to unproject from intertwiner to full space

-- ok so i have a map \rho_1 -> \rho_2, which should be \rho_{-1} \otimes \rho_2 = \rho_1. I'd like to get the explicit linear map from this data. Algebraically: \rho_1 , \rho_{-1} \otimes \rho_2 = \rho_1 , \rho_1 

  -- = \rho_2: but what is the map that witnesses these tensor product isomorphisms?

-- type  Foo g r q = FilterNonTrivial g
--       (
--         Tensor g (DualRep g r) q)

instance Category (IntertwinerA) where 
  id :: forall (g :: Group) (a :: MultiIrreps g). Object IntertwinerA a => IntertwinerA a a
  id = Sectors ((undefined) :: HList (RepToVectors g (Tensor g (GetIrreps a) (GetIrreps a))))

-- type A = Control.Functor.Constrained.Functor 

data RepToVectorsA (r :: MultiIrreps g) = RepToVectorsA (HList (RepToVectors (GetGroup r) (GetIrreps r)))


instance Control.Functor.Constrained.Functor RepToVectorsA IntertwinerA (LinearFunction Double) where
  fmap (Sectors f) = LinearFunction (\x -> undefined)