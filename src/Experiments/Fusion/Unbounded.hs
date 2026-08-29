{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Unbounded \/ Rep fusion — design spike and a tiny typed milestone.
--
-- Finite theories (Fib, Ising) use full-Irr @HomS@ spines. Unbounded Irr
-- (U(1), SU(2), …) must /not/ stretch that representation: Hom is a
-- finite-support map over shared charges, and F\/R come from formulas
-- (CG \/ 6j), aligning with @Experiments.Symbolic@ \/ @Experiments.General@
-- rather than cloning Fib’s table-driven @associateSectors@.
--
-- This module records that fork and offers a U(1)-style multiplicity spine
-- as the first typed milestone (no full associator).
module Experiments.Fusion.Unbounded
  ( Spine
  , SpineMult
  , U1Charge
  , AddCharge
  , SpineTensorU1
  ) where

import GHC.TypeLits (Nat, type (*), type (+))

-- | Finite-support sector spine: list of @(charge, multiplicity)@.
type Spine charge = [(charge, Nat)]

-- | Lookup multiplicity of a charge in a spine (0 if absent).
type family SpineMult (c :: charge) (sp :: Spine charge) :: Nat where
  SpineMult _c '[] = 0
  SpineMult c ('(c, n) ': _) = n
  SpineMult c ('(_d, _n) ': rest) = SpineMult c rest

type U1Charge = Nat

type family AddCharge (p :: U1Charge) (q :: U1Charge) :: U1Charge where
  AddCharge p q = p + q

-- | @[(p,m)] ⊗ [(q,n)] = [(p+q, m*n)]@ for singleton U(1) spines.
type family SpineTensorU1 (a :: Spine U1Charge) (b :: Spine U1Charge) :: Spine U1Charge where
  SpineTensorU1 '[ '(p, m)] '[ '(q, n)] = '[ '(p + q, m * n)]
