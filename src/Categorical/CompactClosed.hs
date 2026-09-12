{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
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
  ) where

import Control.Category.Constrained (Category (..))
import Data.Kind (Type)
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
