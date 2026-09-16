{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Sector Hom: Irr-ordered Dual-left spines.
--
-- 'HomDualS' — @Dual (C n_s(X)) ⊗ C n_s(Y)@ per sector (skeletal finite Hom).
module Fusion.Hom
  ( HomDualS (..)
  , SectorDual
  , BuildIdDual
  , BuildZeroDual
  , idHomDual
  , zeroHomDual
  , fillHomDual
  , composeHomDual
  , eqHomDual
  , sectorFromMap
  , sectorToMap
  , KnownMults
  , MultsVal (..)
  , AllKnownNat
  ) where

import Control.Arrow.Constrained (($))
import Control.Category.Constrained.Prelude (Category (..))
import Data.Complex (Complex)
import Data.Kind (Constraint)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (AdditiveGroup (zeroV), Scalar)
import GHC.TypeLits (KnownNat, Nat, natVal)
import Math.LinearMap.Category
  ( DualVector
  , LinearSpace
  , TensorSpace
  , type (+>)
  , type (⊗)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Class (asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
import Math.OrphanInstances ()
import Numeric.LinearAlgebra.Static
  ( C
  , Sized (fromList, unwrap)
  )
import Numeric.LinearAlgebra.Static.COrphans ()
import Prelude hiding (id, (.), ($))

--------------------------------------------------------------------------------
-- KnownNat on a multiplicity list
--------------------------------------------------------------------------------

type family AllKnownNat (ns :: [Nat]) :: Constraint where
  AllKnownNat '[] = ()
  AllKnownNat (n ': ns) = (KnownNat n, AllKnownNat ns)

type KnownMults (ns :: [Nat]) = AllKnownNat ns

-- | Value-level read of a 'KnownMults' spine (Irr order).
class MultsVal (ns :: [Nat]) where
  multsVal :: [Int]

instance MultsVal '[] where
  multsVal = []

instance (KnownNat n, MultsVal ns) => MultsVal (n ': ns) where
  multsVal = fromIntegral (natVal (Proxy @n)) : multsVal @ns

--------------------------------------------------------------------------------
-- HomDualS spine (Dual-left linearmap packs)
--------------------------------------------------------------------------------

-- | Constraints for a Dual-left sector @Dual (C nd) ⊗ C nc@.
type SectorDual nd nc =
  ( KnownNat nd
  , KnownNat nc
  , LinearSpace (C nd)
  , LinearSpace (C nc)
  , LinearSpace (DualVector (C nd))
  , TensorSpace (C nd)
  , TensorSpace (C nc)
  , TensorSpace (DualVector (C nd))
  , TensorSpace (DualVector (C nd) ⊗ C nc)
  , Scalar (C nd) ~ Complex Double
  , Scalar (C nc) ~ Complex Double
  )

-- | One Dual-left Hom per Irr sector: @Dual (C n_s(X)) ⊗ C n_s(Y)@.
data HomDualS (nsDom :: [Nat]) (nsCod :: [Nat]) where
  HomDualNil :: HomDualS '[] '[]
  HomDualCons
    :: SectorDual nd nc
    => DualVector (C nd) ⊗ C nc
    -> HomDualS nds ncs
    -> HomDualS (nd ': nds) (nc ': ncs)

sectorFromMap
  :: forall nd nc
   . SectorDual nd nc
  => (C nd +> C nc)
  -> DualVector (C nd) ⊗ C nc
sectorFromMap m = asTensor -+$=> m

sectorToMap
  :: forall nd nc
   . SectorDual nd nc
  => DualVector (C nd) ⊗ C nc
  -> (C nd +> C nc)
sectorToMap t = fromTensor -+$=> t

class BuildIdDual (ns :: [Nat]) where
  buildIdDual :: HomDualS ns ns

instance BuildIdDual '[] where
  buildIdDual = HomDualNil

instance (SectorDual n n, BuildIdDual ns) => BuildIdDual (n ': ns) where
  buildIdDual =
    HomDualCons (sectorFromMap @n @n id) (buildIdDual @ns)

idHomDual :: forall ns. BuildIdDual ns => HomDualS ns ns
idHomDual = buildIdDual @ns

-- | Build a rectangular spine by zipping two identity spines (same Irr
-- length). Mismatch is a theory invariant: both 'Mults' walk 'Irr t'.
fillHomDual
  :: HomDualS nsDom nsDom
  -> HomDualS nsCod nsCod
  -> ( forall nd nc
        . SectorDual nd nc
       => Int
       -> Proxy nd
       -> Proxy nc
       -> DualVector (C nd) ⊗ C nc
     )
  -> HomDualS nsDom nsCod
fillHomDual = go 0
  where
    go
      :: Int
      -> HomDualS nsD nsD
      -> HomDualS nsC nsC
      -> ( forall nd nc
            . SectorDual nd nc
           => Int
           -> Proxy nd
           -> Proxy nc
           -> DualVector (C nd) ⊗ C nc
         )
      -> HomDualS nsD nsC
    go _ HomDualNil HomDualNil _ = HomDualNil
    go i (HomDualCons (_ :: DualVector (C nd) ⊗ C nd) ds) (HomDualCons (_ :: DualVector (C nc) ⊗ C nc) cs) f =
      HomDualCons (f i (Proxy @nd) (Proxy @nc)) (go (i + 1) ds cs f)
    go _ _ _ _ = undefined

class BuildZeroDual (nsDom :: [Nat]) (nsCod :: [Nat]) where
  buildZeroDual :: HomDualS nsDom nsCod

instance BuildZeroDual '[] '[] where
  buildZeroDual = HomDualNil

instance (SectorDual nd nc, BuildZeroDual nds ncs) =>
  BuildZeroDual (nd ': nds) (nc ': ncs) where
  buildZeroDual =
    HomDualCons zeroV (buildZeroDual @nds @ncs)

zeroHomDual
  :: forall nsDom nsCod
   . BuildZeroDual nsDom nsCod
  => HomDualS nsDom nsCod
zeroHomDual = buildZeroDual @nsDom @nsCod

composeHomDual
  :: HomDualS nsY nsZ
  -> HomDualS nsX nsY
  -> HomDualS nsX nsZ
composeHomDual HomDualNil HomDualNil = HomDualNil
composeHomDual (HomDualCons g gs) (HomDualCons f fs) =
  HomDualCons
    (sectorFromMap (sectorToMap g . sectorToMap f))
    (composeHomDual gs fs)

-- | Equality by comparing Static unwraps of maps on the domain basis.
eqHomDual :: HomDualS nsDom nsCod -> HomDualS nsDom nsCod -> Bool
eqHomDual HomDualNil HomDualNil = True
eqHomDual (HomDualCons a as) (HomDualCons b bs) =
  sectorMapsEq a b && eqHomDual as bs

sectorMapsEq
  :: forall nd nc
   . SectorDual nd nc
  => DualVector (C nd) ⊗ C nc
  -> DualVector (C nd) ⊗ C nc
  -> Bool
sectorMapsEq ta tb =
  let fa = sectorToMap ta
      fb = sectorToMap tb
      n = fromIntegral (natVal (Proxy @nd)) :: Int
   in and
        [ unwrap (fa $ e i) == unwrap (fb $ e i)
        | i <- [0 .. n - 1]
        ]
  where
    e :: Int -> C nd
    e i =
      fromList
        [ if j == i then 1 else 0
        | j <- [0 .. fromIntegral (natVal (Proxy @nd)) - 1]
        ]
