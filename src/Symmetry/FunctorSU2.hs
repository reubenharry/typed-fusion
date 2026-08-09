{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | SU(2) examples for the group-indexed forgetful category ('Symmetry.RepMor').
--
-- @fmap' Fuse@ uses Clebsch–Gordan ('Symmetry.CG.SU2').
module Symmetry.FunctorSU2 where

import Prelude hiding ((.), id)
import Control.Category.Constrained (Category (..))
import Control.Arrow.Constrained (arr)
import Data.Proxy (Proxy (..))
import Math.LinearMap.Category (type (⊗), type (+>))
import Math.LinearMap.Asserted (type (-+>))
import Numeric.LinearAlgebra.Static (C)
import qualified Test.QuickCheck as QC
import Random.Maps (genIntertwiner)
import Symmetry.FunctorExperiment
  ( IntertwinerG (..), IntertwinerSectorsG (..), mkIdHom )
import Symmetry.Group (Group (SU2))
import Symmetry.Intertwiner.Pretty (ppr)
import Symmetry.RepMor
import Symmetry.RepObj (RepObj (..), type IrrepOf)
import Symmetry.Tensor (Tensor)

-- | Singlet ⊕ triplet (the CG image of ½ ⊗ ½).
type SingletTriplet = '[ 2 `IrrepOf` 0, 3 `IrrepOf` 2]

type HalfSpine = '[ 1 `IrrepOf` 1]
type Half = ('REP HalfSpine :: RepObj SU2)

exampleId :: Mor SU2 Half Half
exampleId = RepInter (mkIdHom @SU2)

exampleIdMap :: C 2 -+> C 2
exampleIdMap = fmap' exampleId

-- | Two spin-½ fuse to singlet ⊕ triplet (CG).
exampleFuse :: Mor SU2 (Half ':⊗: Half) ('REP '[ 1 `IrrepOf` 0, 1 `IrrepOf` 2])
exampleFuse = Fuse

exampleFuseThenId :: Mor SU2 (Half ':⊗: Half) ('REP '[ 1 `IrrepOf` 0, 1 `IrrepOf` 2])
exampleFuseThenId = RepInter (mkIdHom @SU2 @'[ 1 `IrrepOf` 0, 1 `IrrepOf` 2]) . Fuse

exampleFuseMap :: (C 2 ⊗ C 2) -+> C 4
exampleFuseMap = fmap' exampleFuse

exampleFuseLM :: (C 2 ⊗ C 2) +> C 4
exampleFuseLM = arr exampleFuseMap

-- | Associator on three spin-½ factors.
exampleAssoc :: Mor SU2 (Half ':⊗: (Half ':⊗: Half)) ((Half ':⊗: Half) ':⊗: Half)
exampleAssoc = Assoc

exampleAssocMap :: (C 2 ⊗ (C 2 ⊗ C 2)) -+> ((C 2 ⊗ C 2) ⊗ C 2)
exampleAssocMap = fmap' exampleAssoc

exampleAssocInv :: Mor SU2 ((Half ':⊗: Half) ':⊗: Half) (Half ':⊗: (Half ':⊗: Half))
exampleAssocInv = AssocInv

-- | Swap two spin-½ factors.
exampleSwap :: Mor SU2 (Half ':⊗: Half) (Half ':⊗: Half)
exampleSwap = Swap

exampleSwapMap :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2)
exampleSwapMap = fmap' exampleSwap

-- | Right unitor on spin-½.
exampleRUnit :: Mor SU2 (Half ':⊗: 'I) Half
exampleRUnit = RUnit

exampleRUnitMap :: (C 2 ⊗ C 1) -+> C 2
exampleRUnitMap = fmap' exampleRUnit

exampleLUnit :: Mor SU2 ('I ':⊗: Half) Half
exampleLUnit = LUnit

exampleLUnitMap :: (C 1 ⊗ C 2) -+> C 2
exampleLUnitMap = fmap' exampleLUnit

-- | Monoidal product of two identity morphisms (stays symbolic until fmap').
exampleOTimes :: Mor SU2 (Half ':⊗: Half) (Half ':⊗: Half)
exampleOTimes = OTimes exampleId exampleId

exampleOTimesMap :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2)
exampleOTimesMap = fmap' exampleOTimes

-- | F-move on three spin-½ fusions: @(½⊗½)⊗½ → ½⊗(½⊗½)@.
-- Stays symbolic (@FMove@); @fmap'@ blocked on F-symbols \/ 6j.
exampleFMove
  :: Mor SU2
       ('REP (Tensor SU2 (Tensor SU2 HalfSpine HalfSpine) HalfSpine))
       ('REP (Tensor SU2 HalfSpine (Tensor SU2 HalfSpine HalfSpine)))
exampleFMove = FMove (Proxy @HalfSpine) (Proxy @HalfSpine) (Proxy @HalfSpine)

exampleFMoveInv
  :: Mor SU2
       ('REP (Tensor SU2 HalfSpine (Tensor SU2 HalfSpine HalfSpine)))
       ('REP (Tensor SU2 (Tensor SU2 HalfSpine HalfSpine) HalfSpine))
exampleFMoveInv = FMoveInv (Proxy @HalfSpine) (Proxy @HalfSpine) (Proxy @HalfSpine)

example :: Mor SU2 Half ('REP '[ 1 `IrrepOf` 2])
example = RepInter (MkIntertwiner InterNil)

example' :: C 2 +> C 3
example' = arr (fmap' example)

-- | Random endomorphism of singlet ⊕ triplet (independent Schur blocks).
genSingletTripletEndo :: QC.Gen (IntertwinerG SU2 SingletTriplet SingletTriplet)
genSingletTripletEndo = genIntertwiner @SU2

-- | Draw one sample and print Schur + dense block-diagonal forms.
exampleRandomIntertwiner :: IO ()
exampleRandomIntertwiner = do
  inter <- QC.generate genSingletTripletEndo
  ppr inter
  putStrLn "----"
  ppr inter
