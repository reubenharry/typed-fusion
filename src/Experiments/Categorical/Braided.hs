{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Braided (co)associative biendofunctors (Kmett @categories@ shape), on
-- @constrained-categories@ 'Category' with 'Object' premises.
module Experiments.Categorical.Braided
  ( Braided (..)
  , Symmetric
  , swap
  ) where

import Control.Category.Constrained (Category (..))
import Data.Kind (Type)
import Experiments.Categorical.Associative (Associative)
import Prelude hiding (id, (.))

-- | Braiding for an associative biendofunctor (hexagon laws with @associate@).
--
-- When also 'Monoidal', expect @idr . braid = idl@ etc. (not enforced here).
class Associative k p => Braided (k :: κ -> κ -> Type) (p :: κ -> κ -> κ) where
  braid
    :: ( Object k a
       , Object k b
       , Object k (p a b)
       , Object k (p b a)
       )
    => k (p a b) (p b a)

-- | Symmetric braiding: @braid . braid = id@. Fibonacci is /not/ symmetric.
class Braided k p => Symmetric (k :: κ -> κ -> Type) (p :: κ -> κ -> κ)

swap
  :: ( Symmetric k p
     , Object k a
     , Object k b
     , Object k (p a b)
     , Object k (p b a)
     )
  => k (p a b) (p b a)
swap = braid
