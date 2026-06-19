{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Heterogeneous lists and generic spine shuffle operations for DMRG zippers.
module TensorNetwork.DMRG.Spine
  ( HList (..)
  , SpineHead
  , HasHead (..)
  , SpineTail
  , HasTail (..)
  , Snoc
  , CanSnoc (..)
  , consSpine
  , PopLeftCentre
  , PopLeftRest
  , CanPopLeft (..)
  ) where

import Data.Kind (Type)

infixr 5 :&

data HList (xs :: [Type]) where
  HNil :: HList '[]
  (:&) :: x -> HList xs -> HList (x ': xs)

type family SpineHead (xs :: [Type]) :: Type where
  SpineHead (x ': _) = x

class HasHead (xs :: [Type]) where
  spineHead :: HList xs -> SpineHead xs

instance HasHead (x ': xs) where
  spineHead (x :& _) = x

type family SpineTail (xs :: [Type]) :: [Type] where
  SpineTail (_ ': xs) = xs

class HasTail (xs :: [Type]) where
  spineTail :: HList xs -> HList (SpineTail xs)

instance HasTail (x ': xs) where
  spineTail (_ :& xs) = xs

type family Snoc (xs :: [Type]) (x :: Type) :: [Type] where
  Snoc '[] y = '[y]
  Snoc (y ': ys) x = y ': Snoc ys x

class CanSnoc (xs :: [Type]) (x :: Type) where
  snocSpine :: HList xs -> x -> HList (Snoc xs x)

instance CanSnoc '[] x where
  snocSpine HNil y = y :& HNil

instance CanSnoc ys x => CanSnoc (y ': ys) x where
  snocSpine (y :& ys') z = y :& snocSpine ys' z

consSpine :: x -> HList xs -> HList (x ': xs)
consSpine x xs = x :& xs

type family PopLeftCentre (xs :: [Type]) :: Type where
  PopLeftCentre (x ': '[]) = x
  PopLeftCentre (_ ': xs) = PopLeftCentre xs

type family PopLeftRest (xs :: [Type]) :: [Type] where
  PopLeftRest (x ': '[]) = '[]
  PopLeftRest (x ': xs) = x ': PopLeftRest xs

class CanPopLeft (xs :: [Type]) where
  popLeftSpine :: HList xs -> (PopLeftCentre xs, HList (PopLeftRest xs))

instance CanPopLeft (x ': '[]) where
  popLeftSpine (x :& HNil) = (x, HNil)

instance CanPopLeft (x ': xs) => CanPopLeft (y ': x ': xs) where
  popLeftSpine (y :& rest) =
    let (centre, rest') = popLeftSpine rest
    in (centre, y :& rest')
