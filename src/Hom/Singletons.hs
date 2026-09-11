{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Term-level singletons for genealogy-preserving 'FTree' / 'FTrees' trees.
-- Label-polymorphic: SU(2) uses @Nat@ (@2j@); U(1) uses 'Z'.
module Hom.Singletons
  ( KnownRoot (..)
  , KnownLabId
  , SFTree (..)
  , KnownFTree (..)
  , SFTrees (..)
  , KnownFTrees (..)
  , rootLab
  ) where

import Data.Complex (Complex)
import Data.Kind (Constraint)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (Scalar, VectorSpace)
import Hom.Expr
import Hom.TypeLevel (LabCarrier, LabDim)
import GHC.TypeLits (KnownNat, Nat, natVal)
import Symmetry.Utils (KnownZ, Z, getZ)

-- | Term-level access to a root label. Superclasses give the carrier @C (LabDim j)@.
class
  ( KnownNat (LabDim j)
  , VectorSpace (LabCarrier j)
  , Scalar (LabCarrier j) ~ Complex Double
  ) =>
  KnownRoot (j :: k)
  where
  rootVal :: Proxy j -> Integer

instance KnownNat j => KnownRoot (j :: Nat) where
  rootVal _ = natVal (Proxy @j)

instance KnownZ j => KnownRoot (j :: Z) where
  rootVal _ = getZ @j

-- | Extra identity constraint: @KnownNat@ on @Nat@ roots (for 'cmpNat' walks);
-- vacuous on 'Z'.
type family KnownLabId (j :: k) :: Constraint where
  KnownLabId (j :: Nat) = KnownNat j
  KnownLabId (_ :: Z) = ()

-- | Singleton for a genealogy-preserving 'FTree'.
data SFTree (t :: FTree lab) where
  SIrrepTree
    :: forall lab (j :: lab)
     . ( KnownRoot j
       , KnownLabId j
       )
    => SFTree ('IrrepTree j)
  SFrom
    :: forall lab (j :: lab) (l :: FTree lab) (r :: FTree lab)
     . ( KnownRoot j
       , KnownLabId j
       )
    => SFTree l
    -> SFTree r
    -> SFTree ('From j '(l, r))

-- | Materialize 'SFTree' for a statically known tree.
class KnownFTree (t :: FTree lab) where
  fTreeSing :: SFTree t

instance
  ( KnownRoot j
  , KnownLabId j
  ) =>
  KnownFTree ('IrrepTree j)
  where
  fTreeSing = SIrrepTree @_ @j

instance
  ( KnownRoot j
  , KnownLabId j
  , KnownFTree l
  , KnownFTree r
  ) =>
  KnownFTree ('From j '(l, r))
  where
  fTreeSing = SFrom @_ @j (fTreeSing @_ @l) (fTreeSing @_ @r)

-- | Singleton spine for 'FTrees'.
data SFTrees (ts :: FTrees lab) where
  SFTreesNil :: SFTrees '[]
  SFTreesCons
    :: forall t rest
     . SFTree t
    -> SFTrees rest
    -> SFTrees (t ': rest)

-- | Materialize 'SFTrees' for a statically known tree list.
class KnownFTrees (ts :: FTrees lab) where
  fTreesSing :: SFTrees ts

instance KnownFTrees '[] where
  fTreesSing = SFTreesNil

instance
  ( KnownFTree t
  , KnownFTrees rest
  ) =>
  KnownFTrees (t ': rest)
  where
  fTreesSing = SFTreesCons (fTreeSing @_ @t) (fTreesSing @_ @rest)

-- | Root label as 'Int' (SU(2) @2j@ / U(1) charge).
rootLab :: SFTree t -> Int
rootLab (SIrrepTree @_ @j) = fromInteger (rootVal (Proxy @j))
rootLab (SFrom @_ @j _ _) = fromInteger (rootVal (Proxy @j))
