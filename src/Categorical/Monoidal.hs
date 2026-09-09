{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Monoidal biendofunctors (Kmett @categories@ shape), on
-- @constrained-categories@ 'Category' with 'Object' premises.
module Categorical.Monoidal
  ( Monoidal (..)
  ) where

import Control.Category.Constrained (Category (..))
import Data.Kind (Type)
import Categorical.Associative (Associative)
import Prelude hiding (id, (.))

-- | Monoidal structure on an associative biendofunctor (unitors).
--
-- Triangle identities (law, not enforced here):
-- @
-- first idr = second idl . associate
-- idr . coidr = id
-- idl . coidl = id
-- @
class Associative k p => Monoidal (k :: κ -> κ -> Type) (p :: κ -> κ -> κ) where
  type Id k p :: κ

  idl
    :: ( Object k a
       , Object k (Id k p)
       , Object k (p (Id k p) a)
       )
    => k (p (Id k p) a) a

  idr
    :: ( Object k a
       , Object k (Id k p)
       , Object k (p a (Id k p))
       )
    => k (p a (Id k p)) a

  coidl
    :: ( Object k a
       , Object k (Id k p)
       , Object k (p (Id k p) a)
       )
    => k a (p (Id k p) a)

  coidr
    :: ( Object k a
       , Object k (Id k p)
       , Object k (p a (Id k p))
       )
    => k a (p a (Id k p))
