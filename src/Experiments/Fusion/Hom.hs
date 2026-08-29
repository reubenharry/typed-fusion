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

-- | Sector Hom as an Irr-ordered spine of matrices.
module Experiments.Fusion.Hom
  ( HomS (..)
  , idHom
  , zeroHom
  , composeHom
  , eqHom
  , KnownMults
  , AllKnownNat
  , eyeM
  ) where

import Data.Kind (Constraint)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownNat, Nat, natVal)
import Numeric.LinearAlgebra.Static
  ( Domain (mul)
  , M
  , Sized (fromList, unwrap)
  , konst
  )
import Prelude

--------------------------------------------------------------------------------
-- KnownNat on a multiplicity list
--------------------------------------------------------------------------------

type family AllKnownNat (ns :: [Nat]) :: Constraint where
  AllKnownNat '[] = ()
  AllKnownNat (n ': ns) = (KnownNat n, AllKnownNat ns)

type KnownMults (ns :: [Nat]) = AllKnownNat ns

--------------------------------------------------------------------------------
-- Hom spine
--------------------------------------------------------------------------------

-- | One matrix per Irr sector: @Hom(X,Y)_s ∈ Mat_{n_s(Y), n_s(X)}@.
data HomS (nsDom :: [Nat]) (nsCod :: [Nat]) where
  HomNil :: HomS '[] '[]
  HomCons
    :: (KnownNat nd, KnownNat nc)
    => M nc nd
    -> HomS nds ncs
    -> HomS (nd ': nds) (nc ': ncs)

eyeM :: forall n. KnownNat n => M n n
eyeM =
  let n = fromIntegral (natVal (Proxy @n)) :: Int
   in fromList
        [ if i == j then 1 else 0
        | i <- [0 .. n - 1]
        , j <- [0 .. n - 1]
        ]

class BuildId (ns :: [Nat]) where
  buildId :: HomS ns ns

instance BuildId '[] where
  buildId = HomNil

instance (KnownNat n, BuildId ns) => BuildId (n ': ns) where
  buildId = HomCons (eyeM @n) (buildId @ns)

idHom :: forall ns. BuildId ns => HomS ns ns
idHom = buildId @ns

class BuildZero (nsDom :: [Nat]) (nsCod :: [Nat]) where
  buildZero :: HomS nsDom nsCod

instance BuildZero '[] '[] where
  buildZero = HomNil

instance (KnownNat nd, KnownNat nc, BuildZero nds ncs) =>
  BuildZero (nd ': nds) (nc ': ncs) where
  buildZero = HomCons (konst 0) (buildZero @nds @ncs)

zeroHom
  :: forall nsDom nsCod
   . BuildZero nsDom nsCod
  => HomS nsDom nsCod
zeroHom = buildZero @nsDom @nsCod

composeHom
  :: HomS nsY nsZ
  -> HomS nsX nsY
  -> HomS nsX nsZ
composeHom HomNil HomNil = HomNil
composeHom (HomCons g gs) (HomCons f fs) =
  HomCons (mul g f) (composeHom gs fs)

eqHom :: HomS nsDom nsCod -> HomS nsDom nsCod -> Bool
eqHom HomNil HomNil = True
eqHom (HomCons a as) (HomCons b bs) =
  unwrap a == unwrap b && eqHom as bs
