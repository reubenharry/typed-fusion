{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Categorical bifunctors (Kmett @categories@ shape), on
-- @constrained-categories@ 'Category' with 'Object' constraints.
--
-- Compared to @Control.Categorical.Bifunctor@: poly-kinded object
-- constructors @p :: κ → κ → κ@, and every map carries 'Object' premises so
-- non-Hask categories (e.g. Fib) typecheck.
module Categorical.Bifunctor
  ( PFunctor (..)
  , QFunctor (..)
  , Bifunctor (..)
  ) where

import Control.Category.Constrained (Category (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- | Functorial in the first argument of @p@.
class (Category r, Category t) => PFunctor (p :: κ -> κ -> κ) (r :: κ -> κ -> Type) (t :: κ -> κ -> Type) | p r -> t, p t -> r where
  first
    :: ( Object r a
       , Object r b
       , Object t c
       , Object t (p a c)
       , Object t (p b c)
       )
    => r a b
    -> t (p a c) (p b c)

-- | Functorial in the second argument of @p@.
class (Category s, Category t) => QFunctor (q :: κ -> κ -> κ) (s :: κ -> κ -> Type) (t :: κ -> κ -> Type) | q s -> t, q t -> s where
  second
    :: ( Object s a
       , Object s b
       , Object t c
       , Object t (q c a)
       , Object t (q c b)
       )
    => s a b
    -> t (q c a) (q c b)

-- | Bifunctor @p : r × s → t@. Biendofunctor when @r ~ s ~ t@.
--
-- Minimal definition: 'bimap', or both 'first' and 'second' (then set
-- @bimap f g = second g . first f@ in the instance).
class (PFunctor p r t, QFunctor p s t) => Bifunctor (p :: κ -> κ -> κ) (r :: κ -> κ -> Type) (s :: κ -> κ -> Type) (t :: κ -> κ -> Type) | p r -> s t, p s -> r t, p t -> r s where
  bimap
    :: ( Object r a
       , Object r b
       , Object s c
       , Object s d
       , Object t (p a c)
       , Object t (p b d)
       )
    => r a b
    -> s c d
    -> t (p a c) (p b d)
