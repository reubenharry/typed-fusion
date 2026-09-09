{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
module Hom.Singletons
  ( SIrrep (..)
  , SFTree (..)
  , KnownFTree (..)
  , SFTrees (..)
  , KnownFTrees (..)
  , rootLab
  ) where

import Data.Proxy (Proxy (..))
import Hom.Expr
import Hom.TypeLevel (IrrepDim)
import GHC.TypeLits (KnownNat, Nat, natVal)

-- | Singleton for an irrep label (@2j@ as 'Nat').
data SIrrep (j :: Nat) where
  SAtomI
    :: forall j
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SIrrep j

-- | Singleton for a genealogy-preserving 'FTree' tree.
data SFTree (t :: FTree) where
  SI
    :: forall j
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SFTree ('I j)
  SFrom
    :: forall j l r
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SFTree l
    -> SFTree r
    -> SFTree ('From j '(l, r))

-- | Materialize 'SFTree' for a statically known tree.
class KnownFTree (t :: FTree) where
  fTreeSing :: SFTree t

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  KnownFTree ('I j)
  where
  fTreeSing = SI @j

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
data SFTrees (ts :: FTrees) where
  SFTreesNil :: SFTrees '[]
  SFTreesCons
    :: forall t rest
     . SFTree t
    -> SFTrees rest
    -> SFTrees (t ': rest)

-- | Materialize 'SFTrees' for a statically known tree list.
class KnownFTrees (ts :: FTrees) where
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
rootLab (SI @j) = fromIntegral (natVal (Proxy @j))
rootLab (SFrom @j _ _) = fromIntegral (natVal (Proxy @j))
