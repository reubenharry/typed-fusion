{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Group actions on unfused 'ToVObj' trees and fused multiplet spines.
--
-- 'actsOnObj': inductive on 'Obj' — irrep Wigner / U(1) phase, Kronecker on
-- @⊗@, componentwise on @⊕@.
--
-- 'actsOnFTrees': inductive on 'FTrees' — 'actsOnRoot' per channel.
-- 'actsOnFused' wraps that for the nested 'Fused' view.
module Hom.Action
  ( ActsOnObj (..)
  , ActsOnRoot (..)
  , ActsOnFTrees (..)
  , actsOnFused
  ) where

import Control.Arrow.Constrained (($), arr)
import Data.Complex (Complex (..))
import Data.Proxy (Proxy (..))
import Data.VectorSpace (VectorSpace ((*^)))
import Fusion.Obj (Obj (Irrep, (:⊗:), (:⊕:)))
import GHC.TypeLits (KnownNat, natVal)
import Hom.Core (KnownToVObj)
import Hom.Expr (FTrees)
import Hom.FTreeV (FTreeV (..), fTreeVToV, makeFTrees)
import Hom.Singletons (KnownFTrees)
import Hom.TypeLevel
  ( Fused
  , IrrepDim
  , LabCarrier
  , ObjTrees
  , Root
  , ToVFTrees
  , ToVObj
  )
import Math.LinearMap.Category
  ( TensorSpace
  , pattern LinearFunction
  , type (⊗)
  )
import Categorical.Linear ((⊗^))
import Symmetry.Group (Group (..), GroupElement, Irreps, U1Element (..))
import Symmetry.SU2 (applyWigner)
import Symmetry.Utils (KnownZ, getZ)

import Prelude hiding (id, ($))

--------------------------------------------------------------------------------
-- Unfused Obj action (compositional on ⊗ / ⊕)
--------------------------------------------------------------------------------

-- | Group action on unfused object spaces.
--
-- Superclass 'KnownToVObj' supplies the linear / tensor structure needed for
-- the Kronecker case. Instances induct on 'Obj' (same pattern as 'KnownToVObj').
class KnownToVObj g a => ActsOnObj (g :: Group) (a :: Obj (Irreps g)) where
  actsOnObj :: GroupElement g -> ToVObj g a -> ToVObj g a

-- SU(2) ----------------------------------------------------------------------

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  ActsOnObj SU2 ('Irrep j)
  where
  actsOnObj = applyWigner (fromIntegral (natVal (Proxy @j)))

instance
  ( ActsOnObj SU2 a
  , ActsOnObj SU2 b
  , TensorSpace (ToVObj SU2 a)
  , TensorSpace (ToVObj SU2 b)
  , TensorSpace (ToVObj SU2 a ⊗ ToVObj SU2 b)
  ) =>
  ActsOnObj SU2 (a :⊗: b)
  where
  actsOnObj g t =
    let fa = arr (LinearFunction (actsOnObj @SU2 @a g))
        fb = arr (LinearFunction (actsOnObj @SU2 @b g))
     in (fa ⊗^ fb) $ t

instance (ActsOnObj SU2 a, ActsOnObj SU2 b) => ActsOnObj SU2 (a :⊕: b) where
  actsOnObj g (x, y) = (actsOnObj @SU2 @a g x, actsOnObj @SU2 @b g y)

-- U(1) -----------------------------------------------------------------------

instance KnownZ j => ActsOnObj U1 ('Irrep j) where
  actsOnObj (U1Element θ) v =
    let q = fromIntegral (getZ @j) :: Double
        phase = exp (0 :+ (q * θ))
     in phase *^ v

instance
  ( ActsOnObj U1 a
  , ActsOnObj U1 b
  , TensorSpace (ToVObj U1 a)
  , TensorSpace (ToVObj U1 b)
  , TensorSpace (ToVObj U1 a ⊗ ToVObj U1 b)
  ) =>
  ActsOnObj U1 (a :⊗: b)
  where
  actsOnObj g t =
    let fa = arr (LinearFunction (actsOnObj @U1 @a g))
        fb = arr (LinearFunction (actsOnObj @U1 @b g))
     in (fa ⊗^ fb) $ t

instance (ActsOnObj U1 a, ActsOnObj U1 b) => ActsOnObj U1 (a :⊕: b) where
  actsOnObj g (x, y) = (actsOnObj @U1 @a g x, actsOnObj @U1 @b g y)

--------------------------------------------------------------------------------
-- Fused multiplet action (FTreeV spines)
--------------------------------------------------------------------------------

-- | Action on a single irrep carrier ('LabCarrier').
class ActsOnRoot (g :: Group) (j :: Irreps g) where
  actsOnRoot :: GroupElement g -> LabCarrier j -> LabCarrier j

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  ActsOnRoot SU2 j
  where
  actsOnRoot = applyWigner (fromIntegral (natVal (Proxy @j)))

instance KnownZ j => ActsOnRoot U1 j where
  actsOnRoot (U1Element θ) v =
    let q = fromIntegral (getZ @j) :: Double
        phase = exp (0 :+ (q * θ))
     in phase *^ v

-- | Channel-wise group action on an 'FTreeV' spine (inductive on 'FTrees').
--
-- Instances are per concrete group (not @Irreps g@ in the head — type families
-- are illegal there).
class ActsOnFTrees (g :: Group) (ts :: FTrees (Irreps g)) where
  actsOnFTrees :: GroupElement g -> FTreeV ts -> FTreeV ts

instance ActsOnFTrees SU2 '[] where
  actsOnFTrees _ FNil = FNil

instance
  ( ActsOnRoot SU2 (Root t)
  , ActsOnFTrees SU2 rest
  ) =>
  ActsOnFTrees SU2 (t ': rest)
  where
  actsOnFTrees g (FCons v rest) =
    FCons (actsOnRoot @SU2 @(Root t) g v) (actsOnFTrees @SU2 @rest g rest)

instance ActsOnFTrees U1 '[] where
  actsOnFTrees _ FNil = FNil

instance
  ( ActsOnRoot U1 (Root t)
  , ActsOnFTrees U1 rest
  ) =>
  ActsOnFTrees U1 (t ': rest)
  where
  actsOnFTrees g (FCons v rest) =
    FCons (actsOnRoot @U1 @(Root t) g v) (actsOnFTrees @U1 @rest g rest)

-- | 'actsOnFTrees' on the nested 'Fused' view ('makeFTrees' / 'fTreeVToV').
actsOnFused
  :: forall g a
   . ( ActsOnFTrees g (ObjTrees g a)
     , KnownFTrees (ObjTrees g a)
     , Fused g a ~ ToVFTrees (ObjTrees g a)
     )
  => GroupElement g
  -> Fused g a
  -> Fused g a
actsOnFused g v =
  fTreeVToV @(ObjTrees g a)
    (actsOnFTrees @g @(ObjTrees g a) g (makeFTrees @(ObjTrees g a) v))
