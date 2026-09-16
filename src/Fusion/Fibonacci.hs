{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
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
  , Mult
  , Mults
  , HomDim
  , FuseIdemMult
    -- * KnownNat bundles
  , KnownMult
    -- * Hom
  , Fib (..)
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
import Data.Proxy (Proxy (..))
import Categorical.Associative (Associative (..))
import Categorical.Bifunctor (Bifunctor (..), PFunctor (..), QFunctor (..))
import Categorical.Braided (Braided (..))
import Categorical.CompactClosed (CompactClosed (..))
import Categorical.Monoidal (Monoidal (..))
import Fusion.Data (FusionData (..), fuseOutcomesFinite)
import Control.Arrow.Constrained (arr)
import Data.VectorSpace (AdditiveGroup (zeroV), InnerSpace ((<.>)), VectorSpace ((*^)))
import Fusion.Hom
  ( HomDualS (..)
  , MultsVal (..)
  , composeHomDual
  , eqHomDual
  , idHomDual
  , sectorFromMap
  , zeroHomDual
  )
import Math.LinearMap.Category
  ( DualVector
  , pattern LinearFunction
  , type (+>)
  , type (⊗)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Math.OrphanInstances ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Fusion.Obj
  ( DualObj
  , Fuse
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
  ( BuildHomDualS
  , HomSectors
  , associateHomDual
  , braidHomDual
  , disassociateHomDual
  , tensorHomDual
  , vacuumPairing
  )
import Fusion.Theory (FiniteIrr (..), FusionTheory (..), Label)
import GHC.TypeLits (KnownNat, natVal)
import Numeric.LinearAlgebra.Static (C, Sized (fromList), konst)
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

type instance Label FibTh = Simple

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
  unitVal _ = One

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
    [(f, 1) |
       canFuseD p a b e,
       canFuseD p e c d,
       f <- irrVals p,
       canFuseD p b c f,
       canFuseD p a f d]
  rSymbol _ Tau Tau One =
    let i = 0 :+ 1
     in exp (- (4 * pi * i / 5))
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

--------------------------------------------------------------------------------
-- KnownNat bundles
--------------------------------------------------------------------------------

type KnownMult (a :: FibObj) =
  ( KnownNat (Mult FibTh 'One a)
  , KnownNat (Mult FibTh 'Tau a)
  )

--------------------------------------------------------------------------------
-- Hom: Dual-left Fib
--------------------------------------------------------------------------------

newtype Fib (a :: FibObj) (b :: FibObj) = Fib
  { unFib :: HomDualS (Mults FibTh a) (Mults FibTh b) }

-- Mults FibTh a = '[Mult FibTh 'One a, Mult FibTh 'Tau a] definitionally when Irr = [One,Tau]

type FibHom a b =
  ( Mults FibTh a ~ '[Mult FibTh 'One a, Mult FibTh 'Tau a]
  , Mults FibTh b ~ '[Mult FibTh 'One b, Mult FibTh 'Tau b]
  )

phi :: Complex Double
phi = (1 + sqrt 5) / 2 :+ 0

phiInv :: Complex Double
phiInv = 1 / phi

phiInvSqrt :: Complex Double
phiInvSqrt = sqrt phiInv

natI :: forall n. KnownNat n => Int
natI = fromIntegral (natVal (Proxy @n))

--------------------------------------------------------------------------------
-- Named morphisms
--------------------------------------------------------------------------------

fuse :: Fib ('Irrep 'Tau :⊗: 'Irrep 'Tau) ('Irrep 'One :⊕: 'Irrep 'Tau)
fuse = Fib idHomDual

split :: Fib ('Irrep 'One :⊕: 'Irrep 'Tau) ('Irrep 'Tau :⊗: 'Irrep 'Tau)
split = Fib idHomDual

eqFib :: (KnownMult a, KnownMult b, FibHom a b) => Fib a b -> Fib a b -> Bool
eqFib (Fib h) (Fib g) = eqHomDual h g

zeroMor
  :: forall a c
   . (KnownMult a, KnownMult c, FibHom a c)
  => Fib a c
zeroMor = Fib zeroHomDual

fuseMap
  :: forall a b
   . (FuseIdemMult FibTh a, FuseIdemMult FibTh b)
  => Fib a b
  -> Fib (Fuse FibTh a) (Fuse FibTh b)
fuseMap (Fib h) = Fib h

--------------------------------------------------------------------------------
-- Category \/ monoidal
--------------------------------------------------------------------------------

instance Category Fib where
  type Object Fib a = (KnownMult a, Mults FibTh a ~ '[Mult FibTh 'One a, Mult FibTh 'Tau a])

  id :: forall a. Object Fib a => Fib a a
  id = Fib idHomDual

  (.)
    :: forall a b c
     . (Object Fib a, Object Fib b, Object Fib c)
    => Fib b c
    -> Fib a b
    -> Fib a c
  (.) (Fib g) (Fib f) = Fib (composeHomDual g f)

instance PFunctor (:⊗:) Fib Fib where
  first
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (a :⊗: c)
       , Object Fib (b :⊗: c)
       )
    => Fib a b
    -> Fib (a :⊗: c) (b :⊗: c)
  first f = bimap f (id :: Fib c c)

instance QFunctor (:⊗:) Fib Fib where
  second
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (c :⊗: a)
       , Object Fib (c :⊗: b)
       )
    => Fib a b
    -> Fib (c :⊗: a) (c :⊗: b)
  second = bimap (id :: Fib c c)

-- Dual-left morphisms from Ops (no densify buffer \/ pack).
instance Bifunctor (:⊗:) Fib Fib Fib where
  bimap
    :: forall a b c d
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib d
       , Object Fib (a :⊗: c)
       , Object Fib (b :⊗: d)
       , HomSectors (Mults FibTh a) (Mults FibTh b)
       , HomSectors (Mults FibTh c) (Mults FibTh d)
       , BuildHomDualS (Mults FibTh (a :⊗: c)) (Mults FibTh (b :⊗: d))
       )
    => Fib a b
    -> Fib c d
    -> Fib (a :⊗: c) (b :⊗: d)
  bimap (Fib f) (Fib g) =
    Fib (tensorHomDual (Proxy @FibTh) f g)

instance Associative Fib (:⊗:) where
  associate
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (a :⊗: b)
       , Object Fib (b :⊗: c)
       , Object Fib ((a :⊗: b) :⊗: c)
       , Object Fib (a :⊗: (b :⊗: c))
       , BuildHomDualS
           (Mults FibTh ((a :⊗: b) :⊗: c))
           (Mults FibTh (a :⊗: (b :⊗: c)))
       )
    => Fib ((a :⊗: b) :⊗: c) (a :⊗: (b :⊗: c))
  associate =
    Fib $
      associateHomDual
        (Proxy @FibTh)
        [natI @(Mult FibTh 'One a), natI @(Mult FibTh 'Tau a)]
        [natI @(Mult FibTh 'One b), natI @(Mult FibTh 'Tau b)]
        [natI @(Mult FibTh 'One c), natI @(Mult FibTh 'Tau c)]

  disassociate
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (a :⊗: b)
       , Object Fib (b :⊗: c)
       , Object Fib ((a :⊗: b) :⊗: c)
       , Object Fib (a :⊗: (b :⊗: c))
       , BuildHomDualS
           (Mults FibTh (a :⊗: (b :⊗: c)))
           (Mults FibTh ((a :⊗: b) :⊗: c))
       )
    => Fib (a :⊗: (b :⊗: c)) ((a :⊗: b) :⊗: c)
  disassociate =
    Fib $
      disassociateHomDual
        (Proxy @FibTh)
        [natI @(Mult FibTh 'One a), natI @(Mult FibTh 'Tau a)]
        [natI @(Mult FibTh 'One b), natI @(Mult FibTh 'Tau b)]
        [natI @(Mult FibTh 'One c), natI @(Mult FibTh 'Tau c)]

instance Monoidal Fib (:⊗:) where
  type Id Fib (:⊗:) = 'Irrep 'One

  idl :: forall a. (Object Fib a, Object Fib ('Irrep 'One), Object Fib ('Irrep 'One :⊗: a)) => Fib ('Irrep 'One :⊗: a) a
  idl = Fib idHomDual

  idr :: forall a. (Object Fib a, Object Fib ('Irrep 'One), Object Fib (a :⊗: 'Irrep 'One)) => Fib (a :⊗: 'Irrep 'One) a
  idr = Fib idHomDual

  coidl :: forall a. (Object Fib a, Object Fib ('Irrep 'One), Object Fib ('Irrep 'One :⊗: a)) => Fib a ('Irrep 'One :⊗: a)
  coidl = Fib idHomDual

  coidr :: forall a. (Object Fib a, Object Fib ('Irrep 'One), Object Fib (a :⊗: 'Irrep 'One)) => Fib a (a :⊗: 'Irrep 'One)
  coidr = Fib idHomDual

instance Braided Fib (:⊗:) where
  braid
    :: forall a b
     . ( Object Fib a
       , Object Fib b
       , Object Fib (a :⊗: b)
       , Object Fib (b :⊗: a)
       , BuildHomDualS (Mults FibTh (a :⊗: b)) (Mults FibTh (b :⊗: a))
       )
    => Fib (a :⊗: b) (b :⊗: a)
  braid =
    Fib $
      braidHomDual
        (Proxy @FibTh)
        [natI @(Mult FibTh 'One a), natI @(Mult FibTh 'Tau a)]
        [natI @(Mult FibTh 'One b), natI @(Mult FibTh 'Tau b)]

--------------------------------------------------------------------------------
-- Cups \/ caps (cup = ε, cap = η)
--------------------------------------------------------------------------------

-- | Math contract (skeletal finite fusion):
--
--   * @ε_X : X ⊗ X* → 𝟙@, @η_X : 𝟙 → X* ⊗ X@ ('DualObj' / 'CompactClosed').
--   * Vacuum sector is Dual-left @Dual (C n_𝟙(X⊗X*)) ⊗ C 1@ (ε) or the
--     dual column (η); other Irr sectors are zero Hom.
--   * Weights from 'vacuumPairing' + 'cupCoeff' (ε) \/ @1@ (η).

-- | Counit @ε_a : a ⊗ a* → 𝟙@ as Dual-left sector Hom.
cup
  :: forall a
   . ( Object Fib a
     , Object Fib (DualObj FibTh a)
     , Object Fib (a :⊗: DualObj FibTh a)
     , Object Fib ('Irrep 'One)
     )
  => Fib (a :⊗: DualObj FibTh a) ('Irrep 'One)
cup =
  let nx = multsVal @(Mults FibTh a)
      ny = multsVal @(Mults FibTh (DualObj FibTh a))
      w = vacuumPairing (Proxy @FibTh) nx ny (cupCoeff (Proxy @FibTh))
      wVec = fromList w :: C (Mult FibTh 'One (a :⊗: DualObj FibTh a))
      vac =
        sectorFromMap
          ( arr (LinearFunction (\v -> konst (wVec <.> v)))
              :: C (Mult FibTh 'One (a :⊗: DualObj FibTh a)) +> C 1
          )
   in Fib $
        HomDualCons
          vac
          (HomDualCons
             (zeroV :: DualVector (C (Mult FibTh 'Tau (a :⊗: DualObj FibTh a))) ⊗ C 0)
             HomDualNil)

-- | Unit @η_a : 𝟙 → a* ⊗ a@ as Dual-left sector Hom.
cap
  :: forall a
   . ( Object Fib a
     , Object Fib (DualObj FibTh a)
     , Object Fib (DualObj FibTh a :⊗: a)
     , Object Fib ('Irrep 'One)
     )
  => Fib ('Irrep 'One) (DualObj FibTh a :⊗: a)
cap =
  let nx = multsVal @(Mults FibTh (DualObj FibTh a))
      ny = multsVal @(Mults FibTh a)
      w = vacuumPairing (Proxy @FibTh) nx ny (const 1)
      wVec = fromList w :: C (Mult FibTh 'One (DualObj FibTh a :⊗: a))
      vac =
        sectorFromMap
          ( arr (LinearFunction (\s -> (konst 1 <.> s) *^ wVec))
              :: C 1 +> C (Mult FibTh 'One (DualObj FibTh a :⊗: a))
          )
   in Fib $
        HomDualCons
          vac
          (HomDualCons
             (zeroV :: DualVector (C 0) ⊗ C (Mult FibTh 'Tau (DualObj FibTh a :⊗: a)))
             HomDualNil)



--------------------------------------------------------------------------------
-- Compact closed (right duals)
--------------------------------------------------------------------------------

instance CompactClosed Fib (:⊗:) where
  type Dual Fib (:⊗:) a = DualObj FibTh a
  unit = cap
  counit = cup
