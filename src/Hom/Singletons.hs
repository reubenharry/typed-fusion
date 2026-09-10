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
-- SU(2) phase: labels are 'Nat'.
module Hom.Singletons
  ( SFTree (..)
  , KnownFTree (..)
  , SFTrees (..)
  , KnownFTrees (..)
  , rootLab
  ) where

import Data.Proxy (Proxy (..))
import Hom.Expr
import Hom.TypeLevel (IrrepDim)
import GHC.TypeLits (KnownNat, Nat, natVal)

-- | Singleton for a genealogy-preserving 'FTree' tree (@lab ~ Nat@ / SU(2)).
data SFTree (t :: FTree Nat) where
  SIrrepTree
    :: forall j
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SFTree ('IrrepTree j)
  SFrom
    :: forall j l r
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SFTree l
    -> SFTree r
    -> SFTree ('From j '(l, r))

-- | Materialize 'SFTree' for a statically known tree.
class KnownFTree (t :: FTree Nat) where
  fTreeSing :: SFTree t

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  KnownFTree ('IrrepTree j)
  where
  fTreeSing = SIrrepTree @j

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  , KnownFTree l
  , KnownFTree r
  ) =>
  KnownFTree ('From j '(l, r))
  where
  fTreeSing = SFrom @j (fTreeSing @l) (fTreeSing @r)

-- | Singleton spine for 'FTrees'.
data SFTrees (ts :: FTrees Nat) where
  SFTreesNil :: SFTrees '[]
  SFTreesCons
    :: forall t rest
     . SFTree t
    -> SFTrees rest
    -> SFTrees (t ': rest)

-- | Materialize 'SFTrees' for a statically known tree list.
class KnownFTrees (ts :: FTrees Nat) where
  fTreesSing :: SFTrees ts

instance KnownFTrees '[] where
  fTreesSing = SFTreesNil

instance
  ( KnownFTree t
  , KnownFTrees rest
  ) =>
  KnownFTrees (t ': rest)
  where
  fTreesSing = SFTreesCons (fTreeSing @t) (fTreesSing @rest)

-- | Root @2j@ as an 'Int' (for channel keys / Racah packing).
rootLab :: SFTree t -> Int
rootLab (SIrrepTree @j) = fromIntegral (natVal (Proxy @j))
rootLab (SFrom @j _ _) = fromIntegral (natVal (Proxy @j))