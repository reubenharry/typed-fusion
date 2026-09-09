{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Fibonacci fusion category as an instance of the generic fusion core.
--
-- Trees \/ Fuse \/ Mult come from 'Fusion.Obj'; Hom from
-- 'Fusion.Hom'; tensor\/braid\/associator from 'Fusion.Ops'.
module Fusion.Fibonacci
  ( -- * Labels \/ objects
    Simple (..)
  , FibObj
  , Obj (..)
  , Norm
  , Fuse
  , FuseNorm
  , Stabilize
  , MultOne
  , MultTau
  , Mult
  , Mults
  , HomDim
  , FuseIdemMult
    -- * KnownNat bundles
  , KnownMult
  , KnownNTensor
  , KnownAssoc
  , KnownTensorMult
  , KnownAssocMult
    -- * Hom
  , HomS (..)
  , HomBlocks (..)
  , Fib (..)
  , composeBlocks
  , idBlocks
  , zeroBlocks
  , tensorBlocks
  , braidBlocks
  , associateBlocks
  , disassociateBlocks
  , phi
  , phiInv
  , phiInvSqrt
  , cup
  , cap
  , zeroMor
  , fuseMap
  , eqFib
    -- * Fuse \/ split
  , fuse
  , split
    -- * Fusion theory
  , FibTh
  ) where

import Control.Category.Constrained.Prelude (Category (..))
import Data.Complex (Complex (..))
import Data.Kind (Constraint)
import Data.Proxy (Proxy (..))
import Categorical.Associative (Associative (..))
import Categorical.Bifunctor (Bifunctor (..), PFunctor (..), QFunctor (..))
import Categorical.Braided (Braided (..))
import Categorical.Monoidal (Monoidal (..))
import Fusion.Data (FusionData (..), fuseOutcomesFinite)
import Fusion.Hom
  ( HomS (..)
  , composeHom
  , eqHom
  , idHom
  , zeroHom
  )
import Fusion.Obj
  ( Fuse
  , FuseIdemMult
  , FuseNorm
  , HomDim
  , Mult
  , Mults
  , Norm
  , Obj (..)
  , Stabilize
  )
import Fusion.Ops
  ( PackHom (..)
  , associateSectors
  , braidSectors
  , disassociateSectors
  , packHom
  , tensorSectors
  , unpackHom
  )
import Fusion.Theory (FiniteIrr (..), FusionTheory (..))
import GHC.TypeLits (KnownNat, Nat, natVal, type (*), type (+))
import Numeric.LinearAlgebra.Static (M, Sized (fromList), konst)
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------
-- Theory
--------------------------------------------------------------------------------

data FibTh

-- | Simple labels @{𝟙, τ}@.
data Simple
  = One
  | Tau
  deriving (Eq, Ord, Show)

instance FusionTheory Simple FibTh where
  type UnitLab FibTh = 'One
  type FuseN FibTh 'One 'One = '[ '( 'One, 1)]
  type FuseN FibTh 'One 'Tau = '[ '( 'Tau, 1)]
  type FuseN FibTh 'Tau 'One = '[ '( 'Tau, 1)]
  type FuseN FibTh 'Tau 'Tau = '[ '( 'One, 1), '( 'Tau, 1)]
  type DualLab FibTh j = j

instance FiniteIrr Simple FibTh where
  type Irr FibTh = '[ 'One, 'Tau]
  irrVals _ = [One, Tau]

instance FusionData Simple FibTh where
  type TermLab FibTh = Simple
  fuseOutcomes = fuseOutcomesFinite
  nSymbol _ One One One = 1
  nSymbol _ One Tau Tau = 1
  nSymbol _ Tau One Tau = 1
  nSymbol _ Tau Tau One = 1
  nSymbol _ Tau Tau Tau = 1
  nSymbol _ _ _ _ = 0
  fSymbol _ inv Tau Tau Tau One Tau = [(Tau, if inv then phi else phiInv)]
  fSymbol _ _ Tau Tau Tau Tau One =
    [(One, phiInv), (Tau, phiInvSqrt)]
  fSymbol _ _ Tau Tau Tau Tau Tau =
    [(One, phiInvSqrt), (Tau, -phiInv)]
  fSymbol p _ a b c d e =
    [ (f, 1)
    | f <- irrVals p
    , canFuseD p a b e
    , canFuseD p e c d
    , canFuseD p b c f
    , canFuseD p a f d
    ]
  rSymbol _ Tau Tau One =
    let i = 0 :+ 1
     in exp (-4 * pi * i / 5)
  rSymbol _ Tau Tau Tau =
    let i = 0 :+ 1
     in exp (3 * pi * i / 5)
  rSymbol _ _ _ _ = 1
  cupCoeff _ Tau = phi
  cupCoeff _ _ = 1

--------------------------------------------------------------------------------
-- Objects
--------------------------------------------------------------------------------

type FibObj = Obj Simple

-- | Fib aliases onto generic @Mult@.
type MultOne (a :: FibObj) = Mult FibTh 'One a
type MultTau (a :: FibObj) = Mult FibTh 'Tau a

type FuseIdemMultFib (a :: FibObj) = FuseIdemMult FibTh a

--------------------------------------------------------------------------------
-- KnownNat bundles (2-sector Fib layout, for static matrix sizes)
--------------------------------------------------------------------------------

type family AllKnownNat (ns :: [Nat]) :: Constraint where
  AllKnownNat '[] = ()
  AllKnownNat (n ': ns) = (KnownNat n, AllKnownNat ns)

type family AppendNat (xs :: [Nat]) (ys :: [Nat]) :: [Nat] where
  AppendNat '[] ys = ys
  AppendNat (x ': xs) ys = x ': AppendNat xs ys

type family NTensorNats (n1a :: Nat) (nta :: Nat) (n1b :: Nat) (ntb :: Nat) :: [Nat] where
  NTensorNats n1a nta n1b ntb =
    '[ n1a * n1b
     , n1b * n1a
     , nta * ntb
     , ntb * nta
     , n1a * ntb
     , ntb * n1a
     , nta * n1b
     , n1b * nta
     , n1a * n1b + nta * ntb
     , n1b * n1a + ntb * nta
     , n1a * ntb + nta * n1b
     , n1b * nta + ntb * n1a
     , (n1a * ntb + nta * n1b) + nta * ntb
     , (n1b * nta + ntb * n1a) + ntb * nta
     ]

type KnownNTensor (n1a :: Nat) (nta :: Nat) (n1b :: Nat) (ntb :: Nat) =
  ( KnownNat n1a
  , KnownNat nta
  , KnownNat n1b
  , KnownNat ntb
  , AllKnownNat (NTensorNats n1a nta n1b ntb)
  )

type family AssocNats
  (n1a :: Nat) (nta :: Nat)
  (n1b :: Nat) (ntb :: Nat)
  (n1c :: Nat) (ntc :: Nat) :: [Nat] where
  AssocNats n1a nta n1b ntb n1c ntc =
    AppendNat
      (NTensorNats n1a nta n1b ntb)
      ( AppendNat
          (NTensorNats n1b ntb n1c ntc)
          ( AppendNat
              ( NTensorNats
                  (n1a * n1b + nta * ntb)
                  ((n1a * ntb + nta * n1b) + nta * ntb)
                  n1c
                  ntc
              )
              ( NTensorNats
                  n1a
                  nta
                  (n1b * n1c + ntb * ntc)
                  ((n1b * ntc + ntb * n1c) + ntb * ntc)
              )
          )
      )

type KnownAssoc
  (n1a :: Nat) (nta :: Nat)
  (n1b :: Nat) (ntb :: Nat)
  (n1c :: Nat) (ntc :: Nat) =
  ( KnownNat n1a
  , KnownNat nta
  , KnownNat n1b
  , KnownNat ntb
  , KnownNat n1c
  , KnownNat ntc
  , AllKnownNat (AssocNats n1a nta n1b ntb n1c ntc)
  )

type KnownMult (a :: FibObj) =
  ( KnownNat (MultOne a)
  , KnownNat (MultTau a)
  )

type KnownTensorMult (a :: FibObj) (b :: FibObj) =
  KnownNTensor (MultOne a) (MultTau a) (MultOne b) (MultTau b)

type KnownAssocMult (a :: FibObj) (b :: FibObj) (c :: FibObj) =
  KnownAssoc
    (MultOne a) (MultTau a)
    (MultOne b) (MultTau b)
    (MultOne c) (MultTau c)

--------------------------------------------------------------------------------
-- Hom: HomS spine + 2-sector view for diagrams
--------------------------------------------------------------------------------

-- | Compatibility view of 2-sector Hom (diagrams \/ legacy).
data HomBlocks (n1x :: Nat) (ntx :: Nat) (n1y :: Nat) (nty :: Nat) = HomBlocks
  { blkOne :: M n1y n1x
  , blkTau :: M nty ntx
  }

homSToBlocks
  :: HomS '[n1x, ntx] '[n1y, nty]
  -> HomBlocks n1x ntx n1y nty
homSToBlocks (HomCons o (HomCons t HomNil)) = HomBlocks o t

blocksToHomS
  :: (KnownNat n1x, KnownNat ntx, KnownNat n1y, KnownNat nty)
  => HomBlocks n1x ntx n1y nty
  -> HomS '[n1x, ntx] '[n1y, nty]
blocksToHomS (HomBlocks o t) = HomCons o (HomCons t HomNil)

newtype Fib (a :: FibObj) (b :: FibObj) = Fib
  { unFib :: HomS (Mults FibTh a) (Mults FibTh b) }

-- Mults FibTh a = '[MultOne a, MultTau a] definitionally when Irr = [One,Tau]

type FibHom a b =
  ( Mults FibTh a ~ '[MultOne a, MultTau a]
  , Mults FibTh b ~ '[MultOne b, MultTau b]
  )

phi :: Complex Double
phi = ((1 + sqrt 5) / 2) :+ 0

phiInv :: Complex Double
phiInv = 1 / phi

phiInvSqrt :: Complex Double
phiInvSqrt = sqrt phiInv

natI :: forall n. KnownNat n => Int
natI = fromIntegral (natVal (Proxy @n))

idBlocks
  :: forall n1 nt
   . (KnownNat n1, KnownNat nt)
  => HomBlocks n1 nt n1 nt
idBlocks = homSToBlocks (idHom @'[n1, nt])

zeroBlocks
  :: forall n1x ntx n1y nty
   . (KnownNat n1x, KnownNat ntx, KnownNat n1y, KnownNat nty)
  => HomBlocks n1x ntx n1y nty
zeroBlocks = homSToBlocks (zeroHom @'[n1x, ntx] @'[n1y, nty])

composeBlocks
  :: forall n1x ntx n1y nty n1z ntz
   . ( KnownNat n1x
     , KnownNat ntx
     , KnownNat n1y
     , KnownNat nty
     , KnownNat n1z
     , KnownNat ntz
     )
  => HomBlocks n1y nty n1z ntz
  -> HomBlocks n1x ntx n1y nty
  -> HomBlocks n1x ntx n1z ntz
composeBlocks g f =
  homSToBlocks $
    composeHom (blocksToHomS g) (blocksToHomS f)

--------------------------------------------------------------------------------
-- Ops via generic Fusion.Ops
--------------------------------------------------------------------------------

tensorBlocks
  :: forall n1x ntx n1y nty n1z ntz n1w ntw
   . ( KnownNTensor n1x ntx n1z ntz
     , KnownNTensor n1y nty n1w ntw
     )
  => HomBlocks n1x ntx n1y nty
  -> HomBlocks n1z ntz n1w ntw
  -> HomBlocks
      (n1x * n1z + ntx * ntz)
      ((n1x * ntz + ntx * n1z) + ntx * ntz)
      (n1y * n1w + nty * ntw)
      ((n1y * ntw + nty * n1w) + nty * ntw)
tensorBlocks f g =
  let fs = unpackHom (blocksToHomS f)
      gs = unpackHom (blocksToHomS g)
      rs =
        tensorSectors
          (Proxy @FibTh)
          [natI @n1x, natI @ntx]
          [natI @n1z, natI @ntz]
          [natI @n1y, natI @nty]
          [natI @n1w, natI @ntw]
          fs
          gs
   in homSToBlocks (packHom rs)

braidBlocks
  :: forall n1a nta n1b ntb
   . KnownNTensor n1a nta n1b ntb
  => HomBlocks
      (n1a * n1b + nta * ntb)
      ((n1a * ntb + nta * n1b) + nta * ntb)
      (n1b * n1a + ntb * nta)
      ((n1b * nta + ntb * n1a) + ntb * nta)
braidBlocks =
  let rs =
        braidSectors
          (Proxy @FibTh)
          [natI @n1a, natI @nta]
          [natI @n1b, natI @ntb]
   in homSToBlocks (packHom rs)

associateBlocks
  :: forall n1a nta n1b ntb n1c ntc
   . KnownAssoc n1a nta n1b ntb n1c ntc
  => HomBlocks
      ( (n1a * n1b + nta * ntb) * n1c
          + ((n1a * ntb + nta * n1b) + nta * ntb) * ntc
      )
      ( ((n1a * n1b + nta * ntb) * ntc + ((n1a * ntb + nta * n1b) + nta * ntb) * n1c)
          + ((n1a * ntb + nta * n1b) + nta * ntb) * ntc
      )
      ( n1a * (n1b * n1c + ntb * ntc)
          + nta * ((n1b * ntc + ntb * n1c) + ntb * ntc)
      )
      ( (n1a * ((n1b * ntc + ntb * n1c) + ntb * ntc) + nta * (n1b * n1c + ntb * ntc))
          + nta * ((n1b * ntc + ntb * n1c) + ntb * ntc)
      )
associateBlocks =
  let rs =
        associateSectors
          (Proxy @FibTh)
          [natI @n1a, natI @nta]
          [natI @n1b, natI @ntb]
          [natI @n1c, natI @ntc]
   in homSToBlocks (packHom rs)

disassociateBlocks
  :: forall n1a nta n1b ntb n1c ntc
   . KnownAssoc n1a nta n1b ntb n1c ntc
  => HomBlocks
      ( n1a * (n1b * n1c + ntb * ntc)
          + nta * ((n1b * ntc + ntb * n1c) + ntb * ntc)
      )
      ( (n1a * ((n1b * ntc + ntb * n1c) + ntb * ntc) + nta * (n1b * n1c + ntb * ntc))
          + nta * ((n1b * ntc + ntb * n1c) + ntb * ntc)
      )
      ( (n1a * n1b + nta * ntb) * n1c
          + ((n1a * ntb + nta * n1b) + nta * ntb) * ntc
      )
      ( ((n1a * n1b + nta * ntb) * ntc + ((n1a * ntb + nta * n1b) + nta * ntb) * n1c)
          + ((n1a * ntb + nta * n1b) + nta * ntb) * ntc
      )
disassociateBlocks =
  let rs =
        disassociateSectors
          (Proxy @FibTh)
          [natI @n1a, natI @nta]
          [natI @n1b, natI @ntb]
          [natI @n1c, natI @ntc]
   in homSToBlocks (packHom rs)

--------------------------------------------------------------------------------
-- Named morphisms
--------------------------------------------------------------------------------

cup :: Fib ('Atom 'One) ('Tensor ('Atom 'Tau) ('Atom 'Tau))
cup =
  Fib $
    HomCons
      (fromList [phi] :: M 1 1)
      (HomCons (konst 0 :: M 1 0) HomNil)

cap :: Fib ('Tensor ('Atom 'Tau) ('Atom 'Tau)) ('Atom 'One)
cap =
  Fib $
    HomCons
      (fromList [1] :: M 1 1)
      (HomCons (konst 0 :: M 0 1) HomNil)

fuse :: Fib ('Tensor ('Atom 'Tau) ('Atom 'Tau)) ('Sum ('Atom 'One) ('Atom 'Tau))
fuse = Fib idHom

split :: Fib ('Sum ('Atom 'One) ('Atom 'Tau)) ('Tensor ('Atom 'Tau) ('Atom 'Tau))
split = Fib idHom

eqFib :: (KnownMult a, KnownMult b, FibHom a b) => Fib a b -> Fib a b -> Bool
eqFib (Fib h) (Fib g) = eqHom h g

zeroMor
  :: forall a c
   . (KnownMult a, KnownMult c, FibHom a c)
  => Fib a c
zeroMor = Fib zeroHom

fuseMap
  :: forall a b
   . (FuseIdemMultFib a, FuseIdemMultFib b)
  => Fib a b
  -> Fib (Fuse FibTh a) (Fuse FibTh b)
fuseMap (Fib h) = Fib h

--------------------------------------------------------------------------------
-- Category \/ monoidal
--------------------------------------------------------------------------------

instance Category Fib where
  type Object Fib a = (KnownMult a, Mults FibTh a ~ '[MultOne a, MultTau a])

  id :: forall a. Object Fib a => Fib a a
  id = Fib idHom

  (.)
    :: forall a b c
     . (Object Fib a, Object Fib b, Object Fib c)
    => Fib b c
    -> Fib a b
    -> Fib a c
  (.) (Fib g) (Fib f) = Fib (composeHom g f)

instance PFunctor Tensor Fib Fib where
  first
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (Tensor a c)
       , Object Fib (Tensor b c)
       )
    => Fib a b
    -> Fib (Tensor a c) (Tensor b c)
  first f = bimap f (id :: Fib c c)

instance QFunctor Tensor Fib Fib where
  second
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (Tensor c a)
       , Object Fib (Tensor c b)
       )
    => Fib a b
    -> Fib (Tensor c a) (Tensor c b)
  second g = bimap (id :: Fib c c) g

instance Bifunctor Tensor Fib Fib Fib where
  bimap
    :: forall a b c d
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib d
       , Object Fib (Tensor a c)
       , Object Fib (Tensor b d)
       , PackHom (Mults FibTh a) (Mults FibTh b)
       , PackHom (Mults FibTh c) (Mults FibTh d)
       , PackHom (Mults FibTh (Tensor a c)) (Mults FibTh (Tensor b d))
       )
    => Fib a b
    -> Fib c d
    -> Fib (Tensor a c) (Tensor b d)
  bimap (Fib f) (Fib g) =
    Fib $
      packHom $
        tensorSectors
          (Proxy @FibTh)
          [natI @(MultOne a), natI @(MultTau a)]
          [natI @(MultOne c), natI @(MultTau c)]
          [natI @(MultOne b), natI @(MultTau b)]
          [natI @(MultOne d), natI @(MultTau d)]
          (unpackHom f)
          (unpackHom g)

instance Associative Fib Tensor where
  associate
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (Tensor a b)
       , Object Fib (Tensor b c)
       , Object Fib (Tensor (Tensor a b) c)
       , Object Fib (Tensor a (Tensor b c))
       , PackHom
           (Mults FibTh (Tensor (Tensor a b) c))
           (Mults FibTh (Tensor a (Tensor b c)))
       )
    => Fib (Tensor (Tensor a b) c) (Tensor a (Tensor b c))
  associate =
    Fib $
      packHom $
        associateSectors
          (Proxy @FibTh)
          [natI @(MultOne a), natI @(MultTau a)]
          [natI @(MultOne b), natI @(MultTau b)]
          [natI @(MultOne c), natI @(MultTau c)]

  disassociate
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (Tensor a b)
       , Object Fib (Tensor b c)
       , Object Fib (Tensor (Tensor a b) c)
       , Object Fib (Tensor a (Tensor b c))
       , PackHom
           (Mults FibTh (Tensor a (Tensor b c)))
           (Mults FibTh (Tensor (Tensor a b) c))
       )
    => Fib (Tensor a (Tensor b c)) (Tensor (Tensor a b) c)
  disassociate =
    Fib $
      packHom $
        disassociateSectors
          (Proxy @FibTh)
          [natI @(MultOne a), natI @(MultTau a)]
          [natI @(MultOne b), natI @(MultTau b)]
          [natI @(MultOne c), natI @(MultTau c)]

instance Monoidal Fib Tensor where
  type Id Fib Tensor = 'Atom 'One

  idl :: forall a. (Object Fib a, Object Fib ('Atom 'One), Object Fib (Tensor ('Atom 'One) a)) => Fib (Tensor ('Atom 'One) a) a
  idl = Fib idHom

  idr :: forall a. (Object Fib a, Object Fib ('Atom 'One), Object Fib (Tensor a ('Atom 'One))) => Fib (Tensor a ('Atom 'One)) a
  idr = Fib idHom

  coidl :: forall a. (Object Fib a, Object Fib ('Atom 'One), Object Fib (Tensor ('Atom 'One) a)) => Fib a (Tensor ('Atom 'One) a)
  coidl = Fib idHom

  coidr :: forall a. (Object Fib a, Object Fib ('Atom 'One), Object Fib (Tensor a ('Atom 'One))) => Fib a (Tensor a ('Atom 'One))
  coidr = Fib idHom

instance Braided Fib Tensor where
  braid
    :: forall a b
     . ( Object Fib a
       , Object Fib b
       , Object Fib (Tensor a b)
       , Object Fib (Tensor b a)
       , PackHom (Mults FibTh (Tensor a b)) (Mults FibTh (Tensor b a))
       )
    => Fib (Tensor a b) (Tensor b a)
  braid =
    Fib $
      packHom $
        braidSectors
          (Proxy @FibTh)
          [natI @(MultOne a), natI @(MultTau a)]
          [natI @(MultOne b), natI @(MultTau b)]
