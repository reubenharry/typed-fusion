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

-- | Term-level singletons for genealogy-preserving 'Irrep' / 'Rep' trees.
module Experiments.Symbolic.Singletons
  ( SIrrep (..)
  , SIrrepTree (..)
  , KnownIrrep (..)
  , SRep (..)
  , KnownRep (..)
  , rootLab
  ) where

import Data.Proxy (Proxy (..))
import Experiments.Symbolic.Expr
import Experiments.Symbolic.TypeLevel (IrrepDim)
import GHC.TypeLits (KnownNat, Nat, natVal)

-- | Singleton for an irrep label (@2j@ as 'Nat').
data SIrrep (j :: Nat) where
  SAtomI
    :: forall j
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SIrrep j

-- | Singleton for a genealogy-preserving 'Irrep' tree.
data SIrrepTree (t :: Irrep) where
  SLeaf
    :: forall j
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SIrrepTree ('Leaf j)
  SNode
    :: forall j l r
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SIrrepTree l
    -> SIrrepTree r
    -> SIrrepTree ('Node j l r)

-- | Materialize 'SIrrepTree' for a statically known tree.
class KnownIrrep (t :: Irrep) where
  irrepSing :: SIrrepTree t

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  KnownIrrep ('Leaf j)
  where
  irrepSing = SLeaf @j

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  , KnownIrrep l
  , KnownIrrep r
  ) =>
  KnownIrrep ('Node j l r)
  where
  irrepSing = SNode @j (irrepSing @l) (irrepSing @r)

-- | Singleton spine for 'Rep'.
data SRep (ts :: Rep) where
  SRepNil :: SRep '[]
  SRepCons
    :: forall t rest
     . SIrrepTree t
    -> SRep rest
    -> SRep (t ': rest)

-- | Materialize 'SRep' for a statically known tree list.
class KnownRep (ts :: Rep) where
  repSing :: SRep ts

instance KnownRep '[] where
  repSing = SRepNil

instance
  ( KnownIrrep t
  , KnownRep rest
  ) =>
  KnownRep (t ': rest)
  where
  repSing = SRepCons (irrepSing @t) (repSing @rest)

-- | Root @2j@ as an 'Int' (for channel keys / Racah packing).
rootLab :: SIrrepTree t -> Int
rootLab (SLeaf @j) = fromIntegral (natVal (Proxy @j))
rootLab (SNode @j _ _) = fromIntegral (natVal (Proxy @j))
