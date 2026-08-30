{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Ising fusion category (finite), second instance of the generic fusion core.
module Experiments.Ising
  ( IsingLab (..)
  , IsingTh
  , IsingObj
  , Ising (..)
  , cupSigma
  , braidSigmaSigma
  , associateSigma3
  , eqIsing
  , smokeIsing
  ) where

import Control.Category.Constrained.Prelude (Category (..))
import Data.Complex (Complex (..))
import Data.Proxy (Proxy (..))
import Experiments.Fusion.Data (FusionData (..), fuseOutcomesFinite)
import Experiments.Fusion.Hom
  ( HomS (..)
  , composeHom
  , eqHom
  , idHom
  )
import Experiments.Fusion.Obj (Mult, Mults, Obj (..))
import Experiments.Fusion.Ops
  ( PackHom (..)
  , associateSectors
  , braidSectors
  , packHom
  , unpackHom
  )
import Experiments.Fusion.Theory (FiniteIrr (..), FusionTheory (..))
import GHC.TypeLits (KnownNat)
import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra.Static (M, Sized (fromList), konst)
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------
-- Theory
--------------------------------------------------------------------------------

data IsingTh

data IsingLab
  = Vac
  | Psi
  | Sigma
  deriving (Eq, Ord, Show)

instance FusionTheory IsingLab IsingTh where
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

instance FiniteIrr IsingLab IsingTh where
  type Irr IsingTh = '[ 'Vac, 'Psi, 'Sigma]
  irrVals _ = [Vac, Psi, Sigma]

instance FusionData IsingLab IsingTh where
  type TermLab IsingTh = IsingLab
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
  fSymbol _ _ Sigma Sigma Sigma Vac Sigma =
    [(Sigma, 1 / sqrt 2 :+ 0)]
  fSymbol _ _ Sigma Sigma Sigma Psi Sigma =
    [(Sigma, 1 / sqrt 2 :+ 0)]
  fSymbol _ _ Sigma Sigma Sigma Sigma Vac =
    [(Vac, 1 / sqrt 2 :+ 0), (Psi, 1 / sqrt 2 :+ 0)]
  fSymbol _ _ Sigma Sigma Sigma Sigma Psi =
    [(Vac, 1 / sqrt 2 :+ 0), (Psi, (negate (1 / sqrt 2)) :+ 0)]
  fSymbol p _ a b c d e =
    [ (f, 1)
    | f <- irrVals p
    , canFuseD p a b e
    , canFuseD p e c d
    , canFuseD p b c f
    , canFuseD p a f d
    ]
  rSymbol _ Sigma Sigma Vac =
    let i = 0 :+ 1
     in exp (i * pi / 8)
  rSymbol _ Sigma Sigma Psi =
    let i = 0 :+ 1
     in exp (i * 3 * pi / 8)
  rSymbol _ Psi Sigma Sigma = 0 :+ (-1)
  rSymbol _ Sigma Psi Sigma = 0 :+ 1
  rSymbol _ _ _ _ = 1
  cupCoeff _ Sigma = sqrt 2 :+ 0
  cupCoeff _ _ = 1

--------------------------------------------------------------------------------
-- Objects \/ Hom
--------------------------------------------------------------------------------

type IsingObj = Obj IsingLab

newtype Ising (a :: IsingObj) (b :: IsingObj) = Ising
  { unIsing :: HomS (Mults IsingTh a) (Mults IsingTh b) }

type MultVac a = Mult IsingTh 'Vac a
type MultPsi a = Mult IsingTh 'Psi a
type MultSig a = Mult IsingTh 'Sigma a

type KnownIsing a =
  ( KnownNat (MultVac a)
  , KnownNat (MultPsi a)
  , KnownNat (MultSig a)
  , Mults IsingTh a ~ '[MultVac a, MultPsi a, MultSig a]
  )

eqIsing
  :: (KnownIsing a, KnownIsing b)
  => Ising a b
  -> Ising a b
  -> Bool
eqIsing (Ising f) (Ising g) = eqHom f g

instance Category Ising where
  type Object Ising a = KnownIsing a

  id :: forall a. Object Ising a => Ising a a
  id = Ising idHom

  (.)
    :: forall a b c
     . (Object Ising a, Object Ising b, Object Ising c)
    => Ising b c
    -> Ising a b
    -> Ising a c
  (.) (Ising g) (Ising f) = Ising (composeHom g f)

cupSigma :: Ising ('Atom 'Vac) ('Tensor ('Atom 'Sigma) ('Atom 'Sigma))
cupSigma =
  Ising $
    HomCons
      (fromList [sqrt 2 :+ 0] :: M 1 1) -- Vac channel
      ( HomCons
          (konst 0 :: M 1 0) -- Psi: codim 1, dom 0
          (HomCons (konst 0 :: M 0 0) HomNil) -- Sigma
      )

braidSigmaSigma
  :: Ising
      ('Tensor ('Atom 'Sigma) ('Atom 'Sigma))
      ('Tensor ('Atom 'Sigma) ('Atom 'Sigma))
braidSigmaSigma =
  Ising $
    packHom $
      braidSectors (Proxy @IsingTh) [0, 0, 1] [0, 0, 1]

associateSigma3
  :: Ising
      (Tensor (Tensor ('Atom 'Sigma) ('Atom 'Sigma)) ('Atom 'Sigma))
      (Tensor ('Atom 'Sigma) (Tensor ('Atom 'Sigma) ('Atom 'Sigma)))
associateSigma3 =
  Ising $
    packHom $
      associateSectors (Proxy @IsingTh) [0, 0, 1] [0, 0, 1] [0, 0, 1]

-- | Runtime smoke: three Irr sectors; associator \/ braid are well-formed.
smokeIsing :: Bool
smokeIsing =
  let Ising a = associateSigma3
      Ising r = braidSigmaSigma
      as = unpackHom a
      rs = unpackHom r
   in length as == 3
        && length rs == 3
        && all (\m -> let (x, y) = LA.size m in x >= 0 && y >= 0) as
        && all (\m -> let (x, y) = LA.size m in x >= 0 && y >= 0) rs
