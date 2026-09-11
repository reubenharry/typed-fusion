{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Pretty-printers for unfused 'ToVObj' and fused 'FTreeV'.
--
-- @C n@ already has a verbose hmatrix 'Show'; these printers are shorter and
-- label fused channels by root. 'ToVObj' \/ @⊗@ are type families, so unfused
-- trees use 'PrettyObj' (same pattern as 'ArbitraryObj').
module Hom.Pretty
  ( ppComplex
  , ppC
  , PrettyObj (..)
  , ppFTreeV
  ) where

import Data.Complex (Complex (..))
import Data.List (intercalate)
import qualified Data.Vector.Storable as VS
import Fusion.Obj (Obj (Irrep, (:⊗:), (:⊕:)))
import GHC.TypeLits (KnownNat)
import Hom.Core (KnownToVObj)
import Hom.Expr (FTrees)
import Hom.FTreeV (FTreeV (..))
import Hom.Singletons
  ( KnownFTree
  , KnownFTrees (..)
  , KnownRoot
  , SFTree (..)
  , SFTrees (..)
  , fTreesSing
  , rootLab
  )
import Hom.TypeLevel (IrrepDim, LabDim, Root, ToVObj)
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Group (Group (..), Irreps)
import Symmetry.Utils (KnownZ, getZ)

-- | Compact @a+bi@ (omits @+0i@ / leading @+@).
ppComplex :: Complex Double -> String
ppComplex (r :+ i)
  | abs i < 1e-12 = fmt r
  | abs r < 1e-12 = fmt i ++ "i"
  | i >= 0 = fmt r ++ "+" ++ fmt i ++ "i"
  | otherwise = fmt r ++ fmt i ++ "i"
  where
    fmt x =
      show (fromIntegral (round (x * 1e4) :: Integer) / 1e4 :: Double)

-- | Pretty @C n@ as @[…]@.
ppC :: forall n. KnownNat n => C n -> String
ppC v =
  "[" ++ intercalate ", " (map ppComplex (VS.toList (toArray v))) ++ "]"

--------------------------------------------------------------------------------
-- Unfused Obj
--------------------------------------------------------------------------------

-- | Pretty-print a 'ToVObj' tree.
class KnownToVObj g a => PrettyObj (g :: Group) (a :: Obj (Irreps g)) where
  ppObj :: ToVObj g a -> String

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  PrettyObj SU2 ('Irrep j)
  where
  ppObj = ppC @(IrrepDim j)

instance
  ( PrettyObj SU2 a
  , PrettyObj SU2 b
  ) =>
  PrettyObj SU2 (a :⊗: b)
  where
  -- Probe stub: general @Tensor@ has no free compositional pretty without
  -- 'StaticDimension' / buffer unpack constraints.
  ppObj _ = "<⊗>"

instance
  ( PrettyObj SU2 a
  , PrettyObj SU2 b
  ) =>
  PrettyObj SU2 (a :⊕: b)
  where
  ppObj (x, y) = "(" ++ ppObj @SU2 @a x ++ ") ⊕ (" ++ ppObj @SU2 @b y ++ ")"

instance KnownZ j => PrettyObj U1 ('Irrep j) where
  ppObj v = "q=" ++ show (getZ @j) ++ ":" ++ ppC @1 v

instance
  ( PrettyObj U1 a
  , PrettyObj U1 b
  ) =>
  PrettyObj U1 (a :⊗: b)
  where
  ppObj _ = "<⊗>"

instance
  ( PrettyObj U1 a
  , PrettyObj U1 b
  ) =>
  PrettyObj U1 (a :⊕: b)
  where
  ppObj (x, y) = "(" ++ ppObj @U1 @a x ++ ") ⊕ (" ++ ppObj @U1 @b y ++ ")"

--------------------------------------------------------------------------------
-- Fused FTreeV
--------------------------------------------------------------------------------

-- | Channel list with root labels: @[j=0: […], j=2: […], …]@.
ppFTreeV :: forall ts. KnownFTrees ts => FTreeV ts -> String
ppFTreeV = wrap . go (fTreesSing @_ @ts)
  where
    wrap [] = "[]"
    wrap parts = "[" ++ intercalate ", " parts ++ "]"
    go :: SFTrees ts' -> FTreeV ts' -> [String]
    go SFTreesNil FNil = []
    go (SFTreesCons t rest) (FCons v rs) =
      let label = "j=" ++ show (rootLab t)
          body = case t of
            SIrrepTree {} -> ppC v
            SFrom {} -> ppC v
       in (label ++ ": " ++ body) : go rest rs

instance Show (FTreeV ('[] :: FTrees lab)) where
  show FNil = "[]"

instance
  ( KnownFTree t
  , KnownRoot (Root t)
  , KnownFTrees (t ': rest)
  , KnownNat (LabDim (Root t))
  , Show (FTreeV rest)
  ) =>
  Show (FTreeV (t ': rest))
  where
  show v = ppFTreeV @(t ': rest) v
