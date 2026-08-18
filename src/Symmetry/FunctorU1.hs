{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | U(1) examples for the group-indexed forgetful category ('Symmetry.RepMor').
module Symmetry.FunctorU1
  ( module Symmetry.RepMor
  , example
  , example2
  , example3
  , example4
  , exampleFuseMult
  , exampleFuseMultMap
  ) where

import Prelude hiding ((.), id)
import Control.Category.Constrained (Category (..))
import Math.LinearMap.Category (type (⊗))
import Math.LinearMap.Asserted (type (-+>))
import Numeric.LinearAlgebra.Static (C, konst)
import Symmetry.FunctorExperiment
  ( IntertwinerG (..), IntertwinerSectorsG (..) )
import Symmetry.Group (Group (U1))
import Symmetry.HomBlock (CoeffBlock (..))
import Symmetry.RepMor
import Symmetry.RepObj (RepObj (..), type IrrepOf)
import Symmetry.Tensor (Tensor)
import Symmetry.Utils (Z (..))

example :: U1Mor ('REP '[ 1 `IrrepOf` Pos 2]) ('REP '[ 2 `IrrepOf` Pos 2])
example = RepInter (MkIntertwiner (InterCons (CoeffBlock (konst 1)) InterNil))

example2 :: C 1 -+> C 2
example2 = fmap' example

example3 :: U1Mor ('REP '[ 1 `IrrepOf` Pos 1] ':⊗: 'REP '[ 1 `IrrepOf` Pos 1]) ('REP '[ 2 `IrrepOf` Pos 2])
example3 = example . Fuse

example4 :: (C 1 ⊗ C 1) -+> C 2
example4 = fmap' example3

-- | Multiplicity: @C 2 ⊗ C 1 → C 2@ via general U(1) fuse.
exampleFuseMult
  :: U1Mor ('REP '[ 2 `IrrepOf` Pos 1] ':⊗: 'REP '[ 1 `IrrepOf` Pos 0])
           ('REP (Tensor U1 '[ 2 `IrrepOf` Pos 1] '[ 1 `IrrepOf` Pos 0]))
exampleFuseMult = Fuse

exampleFuseMultMap :: (C 2 ⊗ C 1) -+> C 2
exampleFuseMultMap = fmap' exampleFuseMult
