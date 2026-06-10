{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}


module ITensor.Typed where


import Data.Kind (Type, Constraint)
import GHC.TypeLits (Symbol, Nat)
import Numeric.LinearAlgebra.Static (C)
import Math.LinearMap.Category
import GHC.TypeError (ErrorMessage (..), TypeError)
import Data.Type.Equality (type (==))

-- from linearmap-category, schematically:
-- type (⊗) a b
-- type (+>) a b

--------------------------------------------------------------------------------
-- Labelled legs

newtype Labelled (name :: Symbol) v =
  Labelled { unLabelled :: v }

type family LegName leg :: Symbol where
  LegName (Labelled name v) = name

type family Unlabel leg :: Type where
  Unlabel (Labelled name v) = v

--------------------------------------------------------------------------------
-- Lower a labelled leg list to an ordinary linearmap-category tensor product

type family TensorOf (legs :: [Type]) :: Type where
  TensorOf '[]       = C 1
  TensorOf '[x]      = Unlabel x
  TensorOf (x ': xs) = Unlabel x ⊗ TensorOf xs

newtype LTens (legs :: [Type]) =
  LTens { unLTens :: TensorOf legs }

--------------------------------------------------------------------------------
-- Type-level list utilities

type family If (b :: Bool) (t :: k) (f :: k) :: k where
  If 'True  t f = t
  If 'False t f = f

type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
  '[] ++ ys       = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

type family ElemName (name :: Symbol) (xs :: [Type]) :: Bool where
  ElemName name '[] = 'False
  ElemName name (Labelled name v ': xs) = 'True
  ElemName name (_ ': xs) = ElemName name xs

type family Difference (xs :: [Type]) (ys :: [Type]) :: [Type] where
  Difference '[] ys = '[]
  Difference (Labelled name v ': xs) ys =
    If (ElemName name ys)
       (Difference xs ys)
       (Labelled name v ': Difference xs ys)

type family Intersection (xs :: [Type]) (ys :: [Type]) :: [Type] where
  Intersection '[] ys = '[]
  Intersection (Labelled name v ': xs) ys =
    If (ElemName name ys)
       (Labelled name v ': Intersection xs ys)
       (Intersection xs ys)

-- type family Contracted (xs :: [Type]) (ys :: [Type]) :: [Type] where
--   Contracted xs ys =
--     Difference xs ys ++ Difference ys xs

type Contracted xs ys =
  Difference xs ys ++ Difference ys xs

--------------------------------------------------------------------------------
-- No duplicate labels

type family Assert (b :: Bool) (msg :: ErrorMessage) :: Constraint where
  Assert 'True  msg = ()
  Assert 'False msg = TypeError msg

type family Not (b :: Bool) :: Bool where
  Not 'True  = 'False
  Not 'False = 'True

type family NoDups (xs :: [Type]) :: Constraint where
  NoDups '[] = ()
  NoDups (Labelled name v ': xs) =
    ( Assert
        (Not (ElemName name xs))
        ('Text "Duplicate tensor leg label: " ':<>: 'Text name)
    , NoDups xs
    )

--------------------------------------------------------------------------------
-- Permutation evidence

data Take x xs rest where
  Here  :: Take x (x ': xs) xs
  There :: Take x xs rest -> Take x (y ': xs) (y ': rest)

-- data Perm xs ys where
--   PNil  :: Perm '[] '[]
--   PCons :: Take y xs rest -> Perm rest ys -> Perm xs (y ': ys)

--------------------------------------------------------------------------------
-- Typeclass construction of Take evidence

--------------------------------------------------------------------------------
-- Permutation evidence, by label name rather than exact type equality

data TakeName (name :: Symbol) x xs rest where
  HereName
    :: TakeName name (Labelled name v) (Labelled name v ': xs) xs

  ThereName
    :: TakeName name x xs rest
    -> TakeName name x (y ': xs) (y ': rest)

data Perm xs ys where
  PNil  :: Perm '[] '[]
  PCons :: TakeName (LegName y) y xs rest -> Perm rest ys -> Perm xs (y ': ys)

--------------------------------------------------------------------------------
-- Typeclass construction of TakeName evidence

--------------------------------------------------------------------------------
-- Typeclass construction of TakeName evidence, using Bool dispatch

class TakeNameClass
  (name :: Symbol)
  (xs   :: [Type])
  y
  rest
  | name xs -> y rest where

  takeNameProof :: TakeName name y xs rest

instance
  TakeNameCons (name == LegName z) name z xs y rest
  => TakeNameClass name (z ': xs) y rest where

  takeNameProof =
    takeNameCons @(name == LegName z) @name @z @xs @y @rest


class TakeNameCons
  (matches :: Bool)
  (name    :: Symbol)
  z
  (xs      :: [Type])
  y
  rest
  | matches name z xs -> y rest where

  takeNameCons :: TakeName name y (z ': xs) rest


instance
  TakeNameCons
    'True
    name
    (Labelled name v)
    xs
    (Labelled name v)
    xs where

  takeNameCons =
    HereName


instance
  TakeNameClass name xs y rest
  => TakeNameCons
       'False
       name
       z
       xs
       y
       (z ': rest) where

  takeNameCons =
    ThereName (takeNameProof @name @xs @y @rest)

--------------------------------------------------------------------------------
-- Typeclass construction of permutation evidence

class MakePerm xs ys where
  makePerm :: Perm xs ys

instance MakePerm '[] '[] where
  makePerm = PNil

instance
  ( TakeNameClass (LegName y) xs y rest
  , MakePerm rest ys
  ) => MakePerm xs (y ': ys) where

  makePerm =
    PCons
      (takeNameProof @(LegName y) @xs @y @rest)
      (makePerm @rest @ys)
--------------------------------------------------------------------------------
-- Typeclass construction of permutation evidence

-- class MakePerm xs ys where
--   makePerm :: Perm xs ys

-- instance MakePerm '[] '[] where
--   makePerm = PNil

-- instance
--   ( TakeClass y xs rest
--   , MakePerm rest ys
--   ) => MakePerm xs (y ': ys) where
--   makePerm = PCons takeProof makePerm

--------------------------------------------------------------------------------
-- Permuting underlying tensors
--
-- This is the hard implementation part.
-- It should use repeated swaps plus coerce for associators.

permute
  :: Perm xs ys
  -> TensorOf xs
  -> TensorOf ys
permute =
  error "TODO: implement with swaps + associators"

--------------------------------------------------------------------------------
-- Canonical raw contraction
--
-- Assumes inputs are already ordered as:
--
--   x :: TensorOf (as ++ cs)
--   y :: TensorOf (cs ++ bs)
--
-- and contracts all cs legs.

-- rawContract
--   :: TensorOf (as ++ cs)
--   -> TensorOf (cs ++ bs)
--   -> TensorOf (as ++ bs)
-- rawContract =
--   error "TODO: implement using linearmap-category evaluation / contraction"

rawContract
  :: forall as cs bs.
     TensorOf (as ++ cs)
  -> TensorOf (cs ++ bs)
  -> TensorOf (as ++ bs)
rawContract =
  error "TODO"

--------------------------------------------------------------------------------
-- Label-aware contraction

-- contract
--   :: forall xs ys.
--      ( NoDups xs
--      , NoDups ys
--      , MakePerm xs (Difference xs ys ++ Intersection xs ys)
--      , MakePerm ys (Intersection xs ys ++ Difference ys xs)
--      )
--   => LTens xs
--   -> LTens ys
--   -> LTens (Contracted xs ys)
-- contract (LTens x) (LTens y) =
--   LTens $
--     rawContract
--       (permute
--         (makePerm @xs @(Difference xs ys ++ Intersection xs ys))
--         x)
--       (permute
--         (makePerm @ys @(Intersection xs ys ++ Difference ys xs))
--         y)

contract
  :: forall xs ys.
     ( NoDups xs
     , NoDups ys
     , MakePerm xs (Difference xs ys ++ Intersection xs ys)
     , MakePerm ys (Intersection xs ys ++ Difference ys xs)
     )
  => LTens xs
  -> LTens ys
  -> LTens (Contracted xs ys)
contract (LTens x) (LTens y) =
  LTens $
    rawContract
      @(Difference xs ys)
      @(Intersection xs ys)
      @(Difference ys xs)
      (permute
        (makePerm @xs @(Difference xs ys ++ Intersection xs ys))
        x)
      (permute
        (makePerm @ys @(Intersection xs ys ++ Difference ys xs))
        y)

infixl 6 @
(@) :: forall xs ys.
     ( NoDups xs
     , NoDups ys
     , MakePerm xs (Difference xs ys ++ Intersection xs ys)
     , MakePerm ys (Intersection xs ys ++ Difference ys xs)
     )
  => LTens xs
  -> LTens ys
  -> LTens (Contracted xs ys)
(@) = contract

--------------------------------------------------------------------------------
-- Examples

type (#) a b = Labelled b a

type I = Labelled "i" (C 2)
type J = Labelled "j" (C 3)
type K = Labelled "k" (C 4)

type A = LTens '[I, J]
type B = LTens '[J, K]

example :: LTens '[I, K]
example =
  contract
    (undefined :: A)
    (undefined :: B)

type A2 = Labelled "a" (C 5)
type B2 = Labelled "b" (C 6)

exampleMulti
  :: LTens '[I, J, K]
exampleMulti =
  contract
    (undefined :: LTens '[I, A2, J, B2])
    (undefined :: LTens '[B2, K, A2])

ex :: C 2 ⊗ C 3
ex = undefined where
    l1 :: LTens '[C 2 # "j", C 4 # "i"]
    l1 = LTens ex'

    l2 :: LTens '[C 3 # "k", C 4 # "i"]
    l2 = LTens ex''

    -- ex :: LTens '[C 2 # "j", C 3 # "k"]
    ex = l1 @ l2

ex' :: C 2 ⊗ C 4
ex' = undefined

ex'' :: C 3 ⊗ C 4
ex'' = undefined