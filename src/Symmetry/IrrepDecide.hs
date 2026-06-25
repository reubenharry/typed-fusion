{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Singleton-level irrep equality, indexed by 'Group'.
module Symmetry.IrrepDecide
  ( IrrepEqResult (..)
  , IrrepDecide (..)
  ) where

import Data.Singletons (Sing)
import Symmetry.ChargeEq (NatEqResult (..), ZEqResult (..), sNatEq, sZEq)
import Symmetry.Group (Group (..), Irreps, IrrepEq)

data IrrepEqResult (g :: Group) (a :: Irreps g) (b :: Irreps g) where
  IrrepEqTrue  :: (IrrepEq g a b ~ 'True)  => IrrepEqResult g a b
  IrrepEqFalse :: (IrrepEq g a b ~ 'False) => IrrepEqResult g a b

class IrrepDecide (g :: Group) where
  sIrrepEq :: Sing (a :: Irreps g) -> Sing (b :: Irreps g) -> IrrepEqResult g a b

instance IrrepDecide U1 where
  sIrrepEq sa sb =
    case sZEq sa sb of
      ZEqTrue  -> IrrepEqTrue
      ZEqFalse -> IrrepEqFalse

instance IrrepDecide SU2 where
  sIrrepEq sa sb =
    case sNatEq sa sb of
      NatEqTrue  -> IrrepEqTrue
      NatEqFalse -> IrrepEqFalse
