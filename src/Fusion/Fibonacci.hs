{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Fibonacci fusion data (@FibTh@) and the skeletal category @Fib = FinFusion FibTh@.
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
    -- * Hom
  , Fib
  , pattern Fib
  , unFib
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
import Fusion.Data (FusionData (..), fuseOutcomesFinite)
import Fusion.Finite (FinFusion (..))
import qualified Fusion.Finite as Finite
import Fusion.Hom (HomDualS, idHomDual)
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
import Fusion.Theory (FiniteIrr (..), FusionTheory (..), Label)

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
-- Category synonym
--------------------------------------------------------------------------------

type FibObj = Obj Simple

-- | Skeletal Fibonacci category.
type Fib = FinFusion Simple FibTh

pattern Fib :: HomDualS (Mults FibTh a) (Mults FibTh b) -> Fib a b
pattern Fib h = FinFusion h

{-# COMPLETE Fib #-}

unFib :: Fib a b -> HomDualS (Mults FibTh a) (Mults FibTh b)
unFib = unFinFusion

eqFib
  :: (Object Fib a, Object Fib b)
  => Fib a b
  -> Fib a b
  -> Bool
eqFib = Finite.eqFin

cup
  :: forall a
   . ( Object Fib a
     , Object Fib (DualObj FibTh a)
     , Object Fib (a :⊗: DualObj FibTh a)
     , Object Fib ('Irrep 'One)
     )
  => Fib (a :⊗: DualObj FibTh a) ('Irrep 'One)
cup = Finite.cup @Simple @FibTh @a

cap
  :: forall a
   . ( Object Fib a
     , Object Fib (DualObj FibTh a)
     , Object Fib (DualObj FibTh a :⊗: a)
     , Object Fib ('Irrep 'One)
     )
  => Fib ('Irrep 'One) (DualObj FibTh a :⊗: a)
cap = Finite.cap @Simple @FibTh @a

zeroMor
  :: forall a c
   . (Object Fib a, Object Fib c)
  => Fib a c
zeroMor = Finite.zeroMor @Simple @FibTh @a @c

fuseMap
  :: forall a b
   . (FuseIdemMult FibTh a, FuseIdemMult FibTh b)
  => Fib a b
  -> Fib (Fuse FibTh a) (Fuse FibTh b)
fuseMap = Finite.fuseMap @Simple @FibTh @a @b

phi :: Complex Double
phi = (1 + sqrt 5) / 2 :+ 0

phiInv :: Complex Double
phiInv = 1 / phi

phiInvSqrt :: Complex Double
phiInvSqrt = sqrt phiInv

fuse :: (Object Fib ('Irrep 'Tau :⊗: 'Irrep 'Tau), Object Fib ('Irrep 'One :⊕: 'Irrep 'Tau))
  => Fib ('Irrep 'Tau :⊗: 'Irrep 'Tau) ('Irrep 'One :⊕: 'Irrep 'Tau)
fuse = Fib idHomDual

split :: (Object Fib ('Irrep 'One :⊕: 'Irrep 'Tau), Object Fib ('Irrep 'Tau :⊗: 'Irrep 'Tau))
  => Fib ('Irrep 'One :⊕: 'Irrep 'Tau) ('Irrep 'Tau :⊗: 'Irrep 'Tau)
split = Fib idHomDual
