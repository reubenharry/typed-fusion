{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Associative biendofunctors (Kmett @categories@ shape), on
-- @constrained-categories@ 'Category' with 'Object' premises.
module Categorical.Associative
  ( Associative (..)
  ) where

import Control.Category.Constrained (Category (..))
import Data.Kind (Type)
import Categorical.Bifunctor (Bifunctor)
import Prelude hiding (id, (.))

-- | Associative biendofunctor: Mac Lane pentagon (law, not enforced here).
--
-- @
-- bimap id associate . associate . bimap associate id = associate . associate
-- @
class Bifunctor p k k k => Associative (k :: κ -> κ -> Type) (p :: κ -> κ -> κ) where
  associate
    :: ( Object k a
       , Object k b
       , Object k c
       , Object k (p a b)
       , Object k (p b c)
       , Object k (p (p a b) c)
       , Object k (p a (p b c))
       )
    => k (p (p a b) c) (p a (p b c))

  disassociate
    :: ( Object k a
       , Object k b
       , Object k c
       , Object k (p a b)
       , Object k (p b c)
       , Object k (p (p a b) c)
       , Object k (p a (p b c))
       )
    => k (p a (p b c)) (p (p a b) c)
