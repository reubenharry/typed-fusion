{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Shared group index for representation spines and intertwiner plumbing.
--
-- @GroupElement SU2@ is the Cayley–Klein type from 'Symmetry.SU2'; the irrep
-- action lives there as 'Symmetry.SU2.applyWigner'.
module Symmetry.Group
  ( Group (..)
  , GroupElement
  , SU2Element
  , Irreps
  , Rep
  , IrrepDim
  , SectorDim
  , RepDimG
  , IrrepEq
  , LookupMultGo
  , GroupSpine (..)
  , IntertwinerHom
  , LookupMultG
  , HomSectorListU1
  , LookupMultU1
  , HomSectorListSU2
  , LookupMultSU2
  ) where

import Data.Kind (Type)
import GHC.TypeLits (Nat, type (+), type (*))
import Symmetry.ChargeEq (NatEq, ZEq)
import Symmetry.SU2 (SU2Element)
import Symmetry.Utils (Z, Append)

data Group = U1 | SU2

-- | Concrete group element used by representation actions.
type family GroupElement (g :: Group) :: Type where
  GroupElement U1 = Double
  GroupElement SU2 = SU2Element

type family Irreps (g :: Group) :: Type where
  Irreps U1 = Z
  Irreps SU2 = Nat

type family Rep (g :: Group) :: Type where
  Rep U1 = [(Z, Nat)]
  Rep SU2 = [(Nat, Nat)]

type family IrrepDim (g :: Group) (j :: Irreps g) :: Nat where
  IrrepDim U1 _ = 1
  IrrepDim SU2 j = j + 1

type family SectorDim (g :: Group) (j :: Irreps g) (m :: Nat) :: Nat where
  SectorDim U1 _ m = m
  SectorDim SU2 j m = m * (j + 1)

type family RepDimG (g :: Group) (r :: Rep g) :: Nat where
  RepDimG U1 '[] = 0
  RepDimG U1 ('(z, m) ': rs) = m + RepDimG U1 rs
  RepDimG SU2 '[] = 0
  RepDimG SU2 ('(j, m) ': rs) = m * (j + 1) + RepDimG SU2 rs

type family IrrepEq (g :: Group) (a :: Irreps g) (b :: Irreps g) :: Bool where
  IrrepEq U1 a b = ZEq a b
  IrrepEq SU2 a b = NatEq a b

type family LookupMultGo (eq :: Bool) (m :: Nat) (rest :: Maybe Nat) :: Maybe Nat where
  LookupMultGo 'True m _ = 'Just m
  LookupMultGo 'False _ rest = rest

--------------------------------------------------------------------------------
-- Per-group spine operations (class avoids non-injective dispatch families)
--------------------------------------------------------------------------------

type family LookupMultU1 (z :: Z) (q :: Rep U1) :: Maybe Nat where
  LookupMultU1 _ '[]                = 'Nothing
  LookupMultU1 z ('(z2, m) ': rest) = LookupMultGo (ZEq z z2) m (LookupMultU1 z rest)

type family LookupMultSU2 (j :: Nat) (q :: Rep SU2) :: Maybe Nat where
  LookupMultSU2 _ '[]                = 'Nothing
  LookupMultSU2 j ('(j2, m) ': rest) = LookupMultGo (NatEq j j2) m (LookupMultSU2 j rest)

type family MkBlock (j :: k) (mm :: Maybe Nat) (n :: Nat) :: [(k, Nat, Nat)] where
  MkBlock _ 'Nothing  _ = '[]
  MkBlock j ('Just m) n = '[ '( j, m, n)]

type family HomSectorListU1 (r :: Rep U1) (q :: Rep U1) :: [(Z, Nat, Nat)] where
  HomSectorListU1 '[] _              = '[]
  HomSectorListU1 ('(z, n) ': rs) q  =
    Append (MkBlock z (LookupMultU1 z q) n) (HomSectorListU1 rs q)

type family HomSectorListSU2 (r :: Rep SU2) (q :: Rep SU2) :: [(Nat, Nat, Nat)] where
  HomSectorListSU2 '[] _              = '[]
  HomSectorListSU2 ('(j, n) ': rs) q  =
    Append (MkBlock j (LookupMultSU2 j q) n) (HomSectorListSU2 rs q)

-- | Hom-sector spine for an intertwiner, indexed by group (avoids ambiguous
-- associated-type use in data kinds).
type family IntertwinerHom (g :: Group) (r :: Rep g) (q :: Rep g) :: [(Irreps g, Nat, Nat)] where
  IntertwinerHom U1 r q = HomSectorListU1 r q
  IntertwinerHom SU2 r q = HomSectorListSU2 r q

type family LookupMultG (g :: Group) (j :: Irreps g) (q :: Rep g) :: Maybe Nat where
  LookupMultG U1 z q = LookupMultU1 z q
  LookupMultG SU2 j q = LookupMultSU2 j q

class GroupSpine (g :: Group) where
  type HomSectorListK (r :: Rep g) (q :: Rep g) :: [(Irreps g, Nat, Nat)]
  type LookupMultK (j :: Irreps g) (q :: Rep g) :: Maybe Nat

instance GroupSpine U1 where
  type HomSectorListK r q = HomSectorListU1 r q
  type LookupMultK z q = LookupMultU1 z q

instance GroupSpine SU2 where
  type HomSectorListK r q = HomSectorListSU2 r q
  type LookupMultK j q = LookupMultSU2 j q
