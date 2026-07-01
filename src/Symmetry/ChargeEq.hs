{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE EmptyCase #-}
-- The singletons (@SZero@\/@SPos@\/@SNeg@, @SingI@\/@SDecide@) for 'Z' are
-- orphans here because 'Z' is defined in "Utils"; collecting them in this one
-- small module — alongside the equality machinery that uses them — is
-- deliberate, so we silence the warning rather than scatter them.
{-# OPTIONS_GHC -Wno-orphans -Wno-unused-top-binds #-}

-- | Decidable equality for charges ('Z') and naturals, at both the type level
-- (the 'ZEq' \/ 'NatEq' \/ 'OrdEq' families) and the singleton level (the
-- @s*@ deciders and reflexivity lemmas).
--
-- The deciders return /reduction witnesses/ ('ZEqResult', 'NatEqResult') rather
-- than plain 'Bool's: pattern-matching one brings a @ZEq z z2 ~ 'True@ (or
-- @'False@) equation into scope. This is what lets value-level singleton
-- recursion drive type-family reduction — GHC reduces a family on a known
-- @'True@\/@'False@, but never on charge /apartness/. So we phrase 'LookupMult'
-- and friends as a branch on 'ZEq' and decide that branch here.
module Symmetry.ChargeEq
  ( -- * Type-level equality
    OrdEq, NatEq, ZEq
    -- * Singleton-level deciders
  , NatEqResult(..), sNatEq
  , ZEqResult(..), sZEq, fromNatEq
    -- * Reflexivity
  , natEqRefl, zEqRefl
  , chargeInteger
  ) where

import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Data.Type.Ord (OrderingI(..))
import GHC.TypeLits (Nat, CmpNat)
import qualified GHC.TypeNats
import Data.Singletons (Sing, fromSing)
import Data.Singletons.TH (genSingletons, singDecideInstances)
import Symmetry.Utils (Z(..))

-- Charge singletons (@SZero@, @SPos@, @SNeg@) and @SDecide Z@ (used downstream by
-- the @(%~)@ charge comparison in composition).
$(genSingletons [''Z])
$(singDecideInstances [''Z])

--------------------------------------------------------------------------------
-- Type-level equality
--------------------------------------------------------------------------------

-- | Equality of charges as a @Bool@ (so families can branch on the result
-- instead of on a non-linear pattern). 'OrdEq' collapses a 'CmpNat' result;
-- 'NatEq' compares naturals; 'ZEq' compares charges constructor-wise.
type family OrdEq (o :: Ordering) :: Bool where
  OrdEq 'EQ = 'True
  OrdEq 'LT = 'False
  OrdEq 'GT = 'False

type family NatEq (a :: Nat) (b :: Nat) :: Bool where
  NatEq a b = OrdEq (CmpNat a b)

type family ZEq (a :: Z) (b :: Z) :: Bool where
  ZEq 'Zero    'Zero    = 'True
  ZEq ('Pos a) ('Pos b) = NatEq a b
  ZEq ('Neg a) ('Neg b) = NatEq a b
  ZEq _        _        = 'False

--------------------------------------------------------------------------------
-- Singleton-level deciders
--------------------------------------------------------------------------------

-- | A decided @NatEq@, carrying the resulting reduction equation.
data NatEqResult (a :: Nat) (b :: Nat) where
  NatEqTrue  :: (NatEq a b ~ 'True)  => NatEqResult a b
  NatEqFalse :: (NatEq a b ~ 'False) => NatEqResult a b

-- | Decide 'NatEq' via GHC's primitive 'GHC.TypeNats.cmpNat', whose 'OrderingI'
-- result exposes the @CmpNat@ equation we collapse with 'OrdEq'.
sNatEq :: forall a b. Sing (a :: Nat) -> Sing (b :: Nat) -> NatEqResult a b
sNatEq sa sb =
  GHC.TypeNats.withKnownNat sa $
  GHC.TypeNats.withKnownNat sb $
  case GHC.TypeNats.cmpNat (Proxy @a) (Proxy @b) of
    EQI -> NatEqTrue   -- CmpNat a b ~ 'EQ ⟹ NatEq a b = OrdEq 'EQ = 'True
    LTI -> NatEqFalse  -- CmpNat a b ~ 'LT ⟹ NatEq a b = 'False
    GTI -> NatEqFalse  -- CmpNat a b ~ 'GT ⟹ NatEq a b = 'False

-- | A decided @ZEq@, carrying the resulting reduction equation.
data ZEqResult (z :: Z) (z2 :: Z) where
  ZEqTrue  :: (ZEq z z2 ~ 'True)  => ZEqResult z z2
  ZEqFalse :: (ZEq z z2 ~ 'False) => ZEqResult z z2

-- | Decide 'ZEq' by structural recursion on the charge singletons, delegating to
-- 'sNatEq' for matching @Pos@\/@Neg@ payloads.
sZEq :: Sing (z :: Z) -> Sing (z2 :: Z) -> ZEqResult z z2
sZEq SZero    SZero    = ZEqTrue
sZEq (SPos a) (SPos b) = fromNatEq (sNatEq a b)
sZEq (SNeg a) (SNeg b) = fromNatEq (sNatEq a b)
sZEq SZero    (SPos _) = ZEqFalse
sZEq SZero    (SNeg _) = ZEqFalse
sZEq (SPos _) SZero    = ZEqFalse
sZEq (SPos _) (SNeg _) = ZEqFalse
sZEq (SNeg _) SZero    = ZEqFalse
sZEq (SNeg _) (SPos _) = ZEqFalse

-- | Lift a @NatEq@ witness to the @ZEq@ of the surrounding charge (they share the
-- same @'True'@\/@'False'@ payload for @Pos@\/@Neg@).
fromNatEq :: (ZEq z z2 ~ NatEq a b) => NatEqResult a b -> ZEqResult z z2
fromNatEq NatEqTrue  = ZEqTrue
fromNatEq NatEqFalse = ZEqFalse

--------------------------------------------------------------------------------
-- Reflexivity
--------------------------------------------------------------------------------

-- | @NatEq@ is reflexive. GHC's built-in solver knows @CmpNat a a ~ 'EQ@, so the
-- @LTI@\/@GTI@ branches have contradictory givens and need no equations.
natEqRefl :: forall a. Sing (a :: Nat) -> NatEq a a :~: 'True
natEqRefl sa =
  GHC.TypeNats.withKnownNat sa $
  case GHC.TypeNats.cmpNat (Proxy @a) (Proxy @a) of
    EQI -> Refl

-- | @ZEq@ is reflexive — the witness for "a charge is present in its own rep".
zEqRefl :: Sing (z :: Z) -> ZEq z z :~: 'True
zEqRefl SZero    = Refl
zEqRefl (SPos a) = natEqRefl a
zEqRefl (SNeg a) = natEqRefl a

-- | Total order key for U(1) charge singletons (used by 'DirectSum' map keys).
chargeInteger :: Sing (z :: Z) -> Integer
chargeInteger SZero = 0
chargeInteger (SPos sn) = fromIntegral (fromSing sn)
chargeInteger (SNeg sn) = negate (fromIntegral (fromSing sn))
