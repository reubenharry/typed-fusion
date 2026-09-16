{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Ising fusion data (@IsingTh@) and the skeletal category @Ising = FinFusion IsingTh@.
--
-- F \/ R are the standard planar solution with Frobenius–Schur @ν_σ = +1@
-- (Bonderson; arXiv:2202.08207): the only non-1 F-symbols are the @σψσ@ \/
-- @ψσψ@ signs and the Hadamard block @F^{σσσ}_σ@. There is no
-- “allowed channel ⇒ F = 1” catch-all in front of those.
module Fusion.Ising
  ( IsingSimple (..)
  , IsingObj
  , IsingTh
  , Ising
  , pattern Ising
  , unIsing
  , sigmaDim
  , fuse
  , split
  ) where

import Control.Category.Constrained.Prelude (Category (..))
import Data.Complex (Complex (..))
import Fusion.Data (FusionData (..), fuseOutcomesFinite)
import Fusion.Finite (FinFusion (..))
import Fusion.Hom (HomDualS, idHomDual)
import Fusion.Obj (Mults, Obj (..))
import Fusion.Theory (FiniteIrr (..), FusionTheory (..), Label)

--------------------------------------------------------------------------------
-- Theory
--------------------------------------------------------------------------------

data IsingTh

-- | Simple labels @{𝟙, ψ, σ}@.
data IsingSimple
  = Vac
  | Psi
  | Sigma
  deriving (Eq, Ord, Show)

type instance Label IsingTh = IsingSimple

instance FusionTheory IsingSimple IsingTh where
  type UnitLab IsingTh = 'Vac
  type FuseN IsingTh 'Vac 'Vac = '[ '( 'Vac, 1)]
  type FuseN IsingTh 'Vac 'Psi = '[ '( 'Psi, 1)]
  type FuseN IsingTh 'Vac 'Sigma = '[ '( 'Sigma, 1)]
  type FuseN IsingTh 'Psi 'Vac = '[ '( 'Psi, 1)]
  type FuseN IsingTh 'Psi 'Psi = '[ '( 'Vac, 1)]
  type FuseN IsingTh 'Psi 'Sigma = '[ '( 'Sigma, 1)]
  type FuseN IsingTh 'Sigma 'Vac = '[ '( 'Sigma, 1)]
  type FuseN IsingTh 'Sigma 'Psi = '[ '( 'Sigma, 1)]
  type FuseN IsingTh 'Sigma 'Sigma = '[ '( 'Vac, 1), '( 'Psi, 1)]
  type DualLab IsingTh j = j

instance FiniteIrr IsingSimple IsingTh where
  type Irr IsingTh = '[ 'Vac, 'Psi, 'Sigma]
  irrVals _ = [Vac, Psi, Sigma]
  unitVal _ = Vac

-- | @d_σ = √2@.
sigmaDim :: Complex Double
sigmaDim = sqrt 2 :+ 0

invSqrt2 :: Complex Double
invSqrt2 = 1 / sqrt 2 :+ 0

-- | Non-1 F-symbols (standard gauge @ν_σ = +1@). @Nothing@ means the channel
-- is multiplicity-free with F = 1 when allowed.
specialF
  :: IsingSimple
  -> IsingSimple
  -> IsingSimple
  -> IsingSimple
  -> IsingSimple
  -> Maybe [(IsingSimple, Complex Double)]
specialF Sigma Sigma Sigma Sigma Vac =
  Just [(Vac, invSqrt2), (Psi, invSqrt2)]
specialF Sigma Sigma Sigma Sigma Psi =
  Just [(Vac, invSqrt2), (Psi, -invSqrt2)]
specialF Psi Sigma Psi Sigma Sigma =
  Just [(Sigma, -1)]
specialF Sigma Psi Sigma Psi Sigma =
  Just [(Sigma, -1)]
specialF _ _ _ _ _ = Nothing

instance FusionData IsingSimple IsingTh where
  type TermLab IsingTh = IsingSimple
  fuseOutcomes = fuseOutcomesFinite
  nSymbol _ Vac Vac Vac = 1
  nSymbol _ Vac Psi Psi = 1
  nSymbol _ Vac Sigma Sigma = 1
  nSymbol _ Psi Vac Psi = 1
  nSymbol _ Psi Psi Vac = 1
  nSymbol _ Psi Sigma Sigma = 1
  nSymbol _ Sigma Vac Sigma = 1
  nSymbol _ Sigma Psi Sigma = 1
  nSymbol _ Sigma Sigma Vac = 1
  nSymbol _ Sigma Sigma Psi = 1
  nSymbol _ _ _ _ = 0
  fSymbol p _inv a b c d e
    | not (canFuseD p a b e && canFuseD p e c d) = []
    | Just amps <- specialF a b c d e = amps
    | otherwise =
        [ (f, 1)
        | f <- irrVals p
        , canFuseD p b c f
        , canFuseD p a f d
        ]
  rSymbol p a b c
    | nSymbol p a b c == 0 = 0
    | (a, b, c) == (Sigma, Sigma, Vac) =
        let i = 0 :+ 1
         in exp (- (pi * i / 8))
    | (a, b, c) == (Sigma, Sigma, Psi) =
        let i = 0 :+ 1
         in exp (3 * pi * i / 8)
    | (a, b, c) == (Sigma, Psi, Sigma) = 0 :+ (-1)
    | (a, b, c) == (Psi, Sigma, Sigma) = 0 :+ (-1)
    | (a, b, c) == (Psi, Psi, Vac) = -1
    | otherwise = 1
  cupCoeff _ Sigma = sigmaDim
  cupCoeff _ _ = 1

--------------------------------------------------------------------------------
-- Category synonym
--------------------------------------------------------------------------------

type IsingObj = Obj IsingSimple

-- | Skeletal Ising category.
type Ising = FinFusion IsingSimple IsingTh

pattern Ising :: HomDualS (Mults IsingTh a) (Mults IsingTh b) -> Ising a b
pattern Ising h = FinFusion h

{-# COMPLETE Ising #-}

unIsing :: Ising a b -> HomDualS (Mults IsingTh a) (Mults IsingTh b)
unIsing = unFinFusion

fuse
  :: ( Object Ising ('Irrep 'Sigma :⊗: 'Irrep 'Sigma)
     , Object Ising ('Irrep 'Vac :⊕: 'Irrep 'Psi)
     )
  => Ising ('Irrep 'Sigma :⊗: 'Irrep 'Sigma) ('Irrep 'Vac :⊕: 'Irrep 'Psi)
fuse = Ising idHomDual

split
  :: ( Object Ising ('Irrep 'Vac :⊕: 'Irrep 'Psi)
     , Object Ising ('Irrep 'Sigma :⊗: 'Irrep 'Sigma)
     )
  => Ising ('Irrep 'Vac :⊕: 'Irrep 'Psi) ('Irrep 'Sigma :⊗: 'Irrep 'Sigma)
split = Ising idHomDual
