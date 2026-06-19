{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

-- | Site-index witnesses for generic DMRG zipper moves.
--
-- These GADTs package the @CmpNat@ facts that distinguish interior vs
-- boundary environment updates when the orthogonality centre moves.
module TensorNetwork.DMRG.SiteIndex
  ( MoveRightEnv (..)
  , moveRightEnv3_1
  , moveRightEnv3_2
  ) where

import GHC.TypeLits (Nat, type (+))
import GHC.TypeNats (CmpNat)

-- | Witness for updating environments when moving the centre right from site
-- @i@ to site @i + 1@ in an @n@-site chain.
data MoveRightEnv (n :: Nat) (i :: Nat) where
  MoveRightInterior
    :: (CmpNat (i + 1) n ~ 'LT) => MoveRightEnv n i
  MoveRightBoundary
    :: (CmpNat (i + 1) n ~ 'EQ) => MoveRightEnv n i

moveRightEnv3_1 :: MoveRightEnv 3 1
moveRightEnv3_1 = MoveRightInterior

moveRightEnv3_2 :: MoveRightEnv 3 2
moveRightEnv3_2 = MoveRightBoundary
