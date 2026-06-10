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

module Symmetry.Utils where 


import Data.Kind (Type, Constraint)
import GHC.TypeLits
import Numeric.LinearAlgebra.Static (M, Sized (..), C)
import Linear.V (V)
import Data.AdditiveGroup (AdditiveGroup)
import Data.VectorSpace (AdditiveGroup(..))
import Math.LinearMap.Category (DimensionAware (..))
import Data.Data (Proxy(..))

--------------------------------------------------------------------------------
-- Integer type at the type level
--------------------------------------------------------------------------------

data Z
  = Neg Nat
  | Zero
  | Pos Nat


class KnownZ (z :: Z) where
  zVal :: proxy z -> Integer

instance KnownZ 'Zero where
  zVal _ = 0

instance KnownNat n => KnownZ ('Pos n) where
  zVal _ = natVal (Proxy @n)


instance KnownNat n => KnownZ ('Neg n) where
  zVal _ = negate (natVal (Proxy @n))

getZ :: forall z. KnownZ z => Integer
getZ = zVal (Proxy @z)
--------------------------------------------------------------------------------
-- Type-level integer arithmetic
--------------------------------------------------------------------------------

type family Negate (z :: Z) :: Z where
  Negate 'Zero   = 'Zero
  Negate ('Pos n) = 'Neg n
  Negate ('Neg n) = 'Pos n

-- natVal :: forall (n :: Nat) (proxy :: Nat -> Type). KnownNat n => proxy n -> Integer
-- zVal :: forall (n :: Z) (proxy :: Z -> Type). proxy n -> Integer
-- zVal = undefined 
--------------------------------------------------------------------------------
-- Comparison of Nats
--------------------------------------------------------------------------------

type family CmpNat' (a :: Nat) (b :: Nat) :: Ordering where
  CmpNat' a b = CmpNat a b

--------------------------------------------------------------------------------
-- Nat subtraction assuming a >= b
--------------------------------------------------------------------------------

type family Sub (a :: Nat) (b :: Nat) :: Nat where
  Sub a 0 = a
  Sub a a = 0
  Sub a b = a - b

--------------------------------------------------------------------------------
-- Integer addition
--------------------------------------------------------------------------------

type family Add (a :: Z) (b :: Z) :: Z where

  Add 'Zero b = b
  Add a 'Zero = a

  Add ('Pos a) ('Pos b) =
    'Pos (a + b)

  Add ('Neg a) ('Neg b) =
    'Neg (a + b)

  Add ('Pos a) ('Neg b) =
    AddPosNeg (CmpNat a b) a b

  Add ('Neg a) ('Pos b) =
    AddPosNeg (CmpNat b a) b a

type family AddPosNeg
  (o :: Ordering)
  (a :: Nat)
  (b :: Nat)
  :: Z where

  AddPosNeg 'EQ a b =
    'Zero

  AddPosNeg 'GT a b =
    'Pos (Sub a b)

  AddPosNeg 'LT a b =
    'Neg (Sub b a)


-- One irrep sector with multiplicity
--
-- (charge, multiplicity)
--

type family Scale
  (m :: Nat)
  (n :: Nat)
  :: Nat where

  Scale m n = m  * n

--------------------------------------------------------------------------------
-- HList
--------------------------------------------------------------------------------

data HList (xs :: [Type]) where
  HNil :: HList '[]
  (:&) :: x -> HList xs -> HList (x ': xs)

infixr 5 :&

deriving instance Show (HList '[])

deriving instance
  (Show x, Show (HList xs))
  => Show (HList (x ': xs))


class HListAdditive xs where
  hzeroV   :: HList xs
  haddV    :: HList xs -> HList xs -> HList xs
  hnegateV :: HList xs -> HList xs

instance HListAdditive '[] where
  hzeroV = HNil

  haddV HNil HNil = HNil

  hnegateV HNil = HNil

instance
  ( AdditiveGroup x
  , HListAdditive xs
  ) => HListAdditive (x ': xs) where

type family All (c :: Type -> Constraint) (xs :: [Type]) :: Constraint where
  All c '[]       = ()
  All c (x ': xs) = (c x, All c xs)

class HPure c xs where
  hpureC :: proxy c
         -> (forall x. c x => x)
         -> HList xs

instance HPure c '[] where
  hpureC _ _ = HNil

instance (c x, HPure c xs) => HPure c (x ': xs) where
  hpureC p x =
    x :& hpureC p x

class HMap c xs where
  hmapC :: proxy c
        -> (forall x. c x => x -> x)
        -> HList xs
        -> HList xs

instance HMap c '[] where
  hmapC _ _ HNil = HNil

instance (c x, HMap c xs) => HMap c (x ': xs) where
  hmapC p f (x :& xs) =
    f x :& hmapC p f xs

class HZipWith c xs where
  hzipWithC :: proxy c
            -> (forall x. c x => x -> x -> x)
            -> HList xs
            -> HList xs
            -> HList xs

instance HZipWith c '[] where
  hzipWithC _ _ HNil HNil = HNil

instance (c x, HZipWith c xs) => HZipWith c (x ': xs) where
  hzipWithC p f (x :& xs) (y :& ys) =
    f x y :& hzipWithC p f xs ys

type family Append
  (a :: [k])
  (b :: [k])
  :: [k] where

  Append '[] b =
    b

  Append (x ': xs) b =
    x ': Append xs b



class KnownMaybeNat (m :: Maybe Nat) where
  maybeNatVal :: proxy m -> Maybe Integer

instance KnownMaybeNat 'Nothing where
  maybeNatVal _ = Nothing

instance KnownNat n => KnownMaybeNat ('Just n) where
  maybeNatVal _ =
    Just $ natVal (Proxy @n)

dimensionVal
  :: forall v.
     ( DimensionAware v
     , KnownMaybeNat (StaticDimension v)
     )
  => Maybe Integer
dimensionVal =
  maybeNatVal (Proxy @(StaticDimension v))