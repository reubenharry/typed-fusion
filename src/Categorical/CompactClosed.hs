{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Compact closed \/ right-rigid structure (Kmett @categories@ shape), on
-- @constrained-categories@ 'Category' with 'Object' premises.
--
-- Kmett's @categories@ has 'Control.Category.Monoidal' and Cartesian closed
-- (@CCC@), but not object duals with cups\/caps. @Control.Category.Dual@ is the
-- opposite category, not @a ↦ a*@. We add the missing rigid layer here.
--
-- Right-dual convention (matches Hom and Fib @cup@\/@cap@):
--
-- @
-- unit    η = cap    : I → Dual a ⊗ a     (coevaluation)
-- counit  ε = cup    : a ⊗ Dual a → I     (evaluation)
-- @
--
-- Snake identities (law, not enforced):
--
-- @
-- idl . (counit `bimap` id) . associate . (id `bimap` unit) . coidr ≡ id
-- idr . (id `bimap` counit) . disassociate . (unit `bimap` id) . coidl ≡ id
-- @
--
-- Superclass is only 'Monoidal' (not 'Symmetric'): Fibonacci is braided rigid,
-- not symmetric. Kelly–Laplaza compact closed would also ask for 'Symmetric'.
module Categorical.CompactClosed
  ( CompactClosed (..)
  , NameC
  , UnnameC
  , name
  , unname
  , ComposeNamesC
  , composeNames
  ) where

import Control.Category.Constrained (Category (..))
import Data.Kind (Type)
import Categorical.Associative (Associative (..))
import Categorical.Bifunctor (Bifunctor (..))
import Categorical.Monoidal (Monoidal (..))
import Prelude hiding (id, (.))

-- | Right duals on a monoidal biendofunctor.
class Monoidal k p => CompactClosed (k :: κ -> κ -> Type) (p :: κ -> κ -> κ) where
  type Dual k p (a :: κ) :: κ

  -- | Coevaluation @η : I → Dual a ⊗ a@.
  unit
    :: ( Object k a
       , Object k (Id k p)
       , Object k (Dual k p a)
       , Object k (p (Dual k p a) a)
       )
    => k (Id k p) (p (Dual k p a) a)

  -- | Evaluation @ε : a ⊗ Dual a → I@.
  counit
    :: ( Object k a
       , Object k (Id k p)
       , Object k (Dual k p a)
       , Object k (p a (Dual k p a))
       )
    => k (p a (Dual k p a)) (Id k p)

--------------------------------------------------------------------------------
-- Name \/ unname (⌜f⌝ = (a* ⊗ f) ∘ η_a)
--------------------------------------------------------------------------------

type NameC (k :: κ -> κ -> Type) (p :: κ -> κ -> κ) (a :: κ) (b :: κ) =
  ( CompactClosed k p
  , Object k a
  , Object k b
  , Object k (Id k p)
  , Object k (Dual k p a)
  , Object k (p (Dual k p a) a)
  , Object k (p (Dual k p a) b)
  )

-- | Name @⌜f⌝ = (a* ⊗ f) ∘ η_a : I → a* ⊗ b@.
name
  :: forall {κ} (k :: κ -> κ -> Type) (p :: κ -> κ -> κ) (a :: κ) (b :: κ)
   . NameC k p a b
  => k a b
  -> k (Id k p) (p (Dual k p a) b)
name f = bimap id f . unit

type UnnameC (k :: κ -> κ -> Type) (p :: κ -> κ -> κ) (a :: κ) (c :: κ) =
  ( CompactClosed k p
  , Object k a
  , Object k c
  , Object k (Id k p)
  , Object k (Dual k p a)
  , Object k (p a (Id k p))
  , Object k (p (Dual k p a) c)
  , Object k (p a (p (Dual k p a) c))
  , Object k (p (p a (Dual k p a)) c)
  , Object k (p a (Dual k p a))
  , Object k (p (Id k p) c)
  )

-- | Unname: recover @f : a → c@ from @⌜f⌝ : I → a* ⊗ c@.
--
-- @
-- a ─ρ⁻¹→ a ⊗ I ─id⊗⌜f⌝→ a ⊗ (a* ⊗ c) ─α⁻¹→ (a ⊗ a*) ⊗ c ─ε⊗id→ I ⊗ c ─λ→ c
-- @
unname
  :: forall {κ} (k :: κ -> κ -> Type) (p :: κ -> κ -> κ) (a :: κ) (c :: κ)
   . UnnameC k p a c
  => k (Id k p) (p (Dual k p a) c)
  -> k a c
unname n =
  idl
    . bimap counit id
    . disassociate
    . bimap id n
    . coidr

--------------------------------------------------------------------------------
-- Name composition (Mac Lane ladder on ⌜f⌝ ⊗ ⌜g⌝)
--------------------------------------------------------------------------------

-- | Object premises for 'composeNames': every tensor that appears in the
-- five-step Dual-left Hom ladder. Independent of fusion labels \/ 'DualObj';
-- only 'CompactClosed' (hence 'Monoidal' \/ 'Associative' \/ 'Bifunctor').
type ComposeNamesC (k :: κ -> κ -> Type) (p :: κ -> κ -> κ) (a :: κ) (b :: κ) (c :: κ) =
  ( CompactClosed k p
  , Object k a
  , Object k b
  , Object k c
  , Object k (Id k p)
  , Object k (Dual k p a)
  , Object k (Dual k p b)
  , Object k (p (Dual k p a) b)
  , Object k (p (Dual k p b) c)
  , Object k (p (Id k p) (Id k p))
  , Object k (p (p (Dual k p a) b) (p (Dual k p b) c))
  , Object k (p (Dual k p a) (p b (p (Dual k p b) c)))
  , Object k (p b (p (Dual k p b) c))
  , Object k (p (p b (Dual k p b)) c)
  , Object k (p (Dual k p a) (p (p b (Dual k p b)) c))
  , Object k (p b (Dual k p b))
  , Object k (p (Id k p) c)
  , Object k (p (Dual k p a) (p (Id k p) c))
  , Object k (p (Dual k p a) c)
  )

-- | Compose names @⌜f⌝ : I → a* ⊗ b@ and @⌜g⌝ : I → b* ⊗ c@ to
-- @⌜g ∘ f⌝ : I → a* ⊗ c@ via the five Mac Lane morphisms
-- (same ladder as Hom genealogy / 'composeMorObj'):
--
-- @
--   ⌜f⌝ ⊗ ⌜g⌝
--     ─ α ─►         a* ⊗ (b ⊗ (b* ⊗ c))
--     ─ id⊗α⁻¹ ─►    a* ⊗ ((b ⊗ b*) ⊗ c)
--     ─ id⊗(ε⊗id) ─► a* ⊗ (I ⊗ c)
--     ─ id⊗λ ─►      a* ⊗ c
-- @
--
-- Works in any 'CompactClosed' category (Fib, future Ising, …): no
-- 'FusionTheory' \/ densify.
composeNames
  :: forall {κ} (hom :: κ -> κ -> Type) (prod :: κ -> κ -> κ) (a :: κ) (b :: κ) (c :: κ)
   . ComposeNamesC hom prod a b c
  => hom (Id hom prod) (prod (Dual hom prod a) b)
  -> hom (Id hom prod) (prod (Dual hom prod b) c)
  -> hom (Id hom prod) (prod (Dual hom prod a) c)
composeNames nf ng =
    (id ⊗ idl)
  . (id ⊗ (counit ⊗ id))
  . (id ⊗ disassociate)
  . associate
  . bimap nf ng
  . coidr

-- higher precedence for ⊗
infixl 8 ⊗
(⊗)
    :: forall {κ}  (k :: κ -> κ -> Type) (p :: κ -> κ -> κ) (r :: κ -> κ -> Type) (s :: κ -> κ -> Type) (t :: κ -> κ -> Type) (a :: κ) (b :: κ) (c :: κ) (d :: κ). (Bifunctor (p :: κ -> κ -> κ) (r :: κ -> κ -> Type) (s :: κ -> κ -> Type) (t :: κ -> κ -> Type),  Object r a
       , Object r b
       , Object s c
       , Object s d
       , Object t (p a c)
       , Object t (p b d)
       )
    => r a b
    -> s c d
    -> t (p a c) (p b d)
(⊗) = bimap