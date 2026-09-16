{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Skeletal finite fusion category, parameterized by a 'FiniteIrr' theory.
--
-- @type Fib = FinFusion Simple FibTh@, @type Ising = FinFusion IsingSimple IsingTh@. Hom is the
-- Dual-left 'HomDualS' spine over 'Mults' \/ 'Irr'; tensor, associator, braid,
-- and cups are 'Fusion.Ops' morphisms from 'FusionData'.
module Fusion.Finite
  ( FiniteFusionC
  , FiniteObj
  , FinFusion (..)
  , eqFin
  , zeroMor
  , fuseMap
  , cup
  , cap
  ) where

import Control.Arrow.Constrained (arr)
import Control.Category.Constrained.Prelude (Category (..))
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (AdditiveGroup (zeroV), InnerSpace ((<.>)), VectorSpace ((*^)))
import Categorical.Associative (Associative (..))
import Categorical.Bifunctor (Bifunctor (..), PFunctor (..), QFunctor (..))
import Categorical.Braided (Braided (..))
import Categorical.CompactClosed (CompactClosed (..))
import Categorical.Monoidal (Monoidal (..))
import Fusion.Data (FusionData (..))
import Fusion.Hom
  ( BuildIdDual
  , HomDualS
  , KnownMults
  , MultsVal (..)
  , SectorDual
  , composeHomDual
  , eqHomDual
  , fillHomDual
  , idHomDual
  , sectorFromMap
  )
import Fusion.Obj (DualObj, Fuse, FuseIdemMult, Mults, Obj (..))
import Fusion.Ops
  ( associateHomDual
  , braidHomDual
  , disassociateHomDual
  , tensorHomDual
  , vacuumPairing
  )
import Fusion.Theory (FiniteIrr (..), FusionTheory (..), Label)
import Math.LinearMap.Category
  ( DualVector
  , pattern LinearFunction
  , type (+>)
  , type (⊗)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Math.OrphanInstances ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList, unwrap), konst)
import qualified Data.Vector.Storable as VS
import Numeric.LinearAlgebra.Static.COrphans ()
import Prelude hiding (id, (.))

-- | Term + type data needed to build skeletal morphisms from 'Fusion.Ops'.
type FiniteFusionC (t :: Type) =
  ( FiniteIrr (Label t) t
  , FusionData (Label t) t
  , Eq (Label t)
  , TermLab t ~ Label t
  )

-- | Object premise: multiplicity spine of @a@ is a known Irr-ordered 'HomDualS'.
type FiniteObj t a =
  ( KnownMults (Mults t a)
  , MultsVal (Mults t a)
  , BuildIdDual (Mults t a)
  )

newtype FinFusion (lab :: Type) (t :: Type) (a :: Obj lab) (b :: Obj lab) = FinFusion
  { unFinFusion :: HomDualS (Mults t a) (Mults t b) }

eqFin
  :: (FiniteObj t a, FiniteObj t b)
  => FinFusion lab t a b
  -> FinFusion lab t a b
  -> Bool
eqFin (FinFusion h) (FinFusion g) = eqHomDual h g

zeroMor
  :: forall lab t a c
   . (lab ~ Label t, FiniteObj t a, FiniteObj t c)
  => FinFusion lab t a c
zeroMor =
  FinFusion $
    fillHomDual
      (idHomDual @(Mults t a))
      (idHomDual @(Mults t c))
      (\_ _ _ -> zeroV)

fuseMap
  :: forall lab t a b
   . (lab ~ Label t, FuseIdemMult t a, FuseIdemMult t b)
  => FinFusion lab t a b
  -> FinFusion lab t (Fuse t a) (Fuse t b)
fuseMap (FinFusion h) = FinFusion h

--------------------------------------------------------------------------------
-- Cups \/ caps (cup = ε, cap = η)
--------------------------------------------------------------------------------

cup
  :: forall lab t a
   . ( lab ~ Label t
     , FiniteFusionC t
     , FiniteObj t a
     , FiniteObj t (DualObj t a)
     , FiniteObj t (a :⊗: DualObj t a)
     , FiniteObj t ('Irrep (UnitLab t :: lab))
     )
  => FinFusion lab t (a :⊗: DualObj t a) ('Irrep (UnitLab t :: lab))
cup =
  let p = Proxy @t
      nx = multsVal @(Mults t a)
      ny = multsVal @(Mults t (DualObj t a))
      w = vacuumPairing p nx ny (cupCoeff p)
      irr = irrVals p
      u = unitVal p
   in FinFusion $
        fillHomDual
          (idHomDual @(Mults t (a :⊗: DualObj t a)))
          (idHomDual @(Mults t ('Irrep (UnitLab t :: lab))))
          $ \i (Proxy :: Proxy nd) (Proxy :: Proxy nc) ->
            if irr !! i == u
              then
                let wVec = fromList w :: C nd
                 in sectorFromMap
                      ( arr (LinearFunction (\v -> konst (wVec <.> v)))
                          :: C nd +> C nc
                      )
              else zeroV

cap
  :: forall lab t a
   . ( lab ~ Label t
     , FiniteFusionC t
     , FiniteObj t a
     , FiniteObj t (DualObj t a)
     , FiniteObj t (DualObj t a :⊗: a)
     , FiniteObj t ('Irrep (UnitLab t :: lab))
     )
  => FinFusion lab t ('Irrep (UnitLab t :: lab)) (DualObj t a :⊗: a)
cap =
  let p = Proxy @t
      nx = multsVal @(Mults t (DualObj t a))
      ny = multsVal @(Mults t a)
      w = vacuumPairing p nx ny (const 1)
      irr = irrVals p
      u = unitVal p
   in FinFusion $
        fillHomDual
          (idHomDual @(Mults t ('Irrep (UnitLab t :: lab))))
          (idHomDual @(Mults t (DualObj t a :⊗: a)))
          $ \i (Proxy :: Proxy nd) (Proxy :: Proxy nc) ->
            if irr !! i == u
              then
                let wVec = fromList w :: C nc
                 in sectorFromMap
                      ( arr (LinearFunction (\s -> (konst 1 <.> s) *^ wVec))
                          :: C nd +> C nc
                      )
              else zeroV

--------------------------------------------------------------------------------
-- Category \/ monoidal
--------------------------------------------------------------------------------

instance (lab ~ Label t, FiniteFusionC t) => Category (FinFusion lab t) where
  type Object (FinFusion lab t) a = FiniteObj t a

  id :: forall a. Object (FinFusion lab t) a => FinFusion lab t a a
  id = FinFusion idHomDual

  (.)
    :: forall a b c
     . (Object (FinFusion lab t) a, Object (FinFusion lab t) b, Object (FinFusion lab t) c)
    => FinFusion lab t b c
    -> FinFusion lab t a b
    -> FinFusion lab t a c
  (.) (FinFusion g) (FinFusion f) = FinFusion (composeHomDual g f)

instance (lab ~ Label t, FiniteFusionC t) => PFunctor (:⊗:) (FinFusion lab t) (FinFusion lab t) where
  first
    :: forall a b c
     . ( Object (FinFusion lab t) a
       , Object (FinFusion lab t) b
       , Object (FinFusion lab t) c
       , Object (FinFusion lab t) (a :⊗: c)
       , Object (FinFusion lab t) (b :⊗: c)
       )
    => FinFusion lab t a b
    -> FinFusion lab t (a :⊗: c) (b :⊗: c)
  first f = bimap f (id :: FinFusion lab t c c)

instance (lab ~ Label t, FiniteFusionC t) => QFunctor (:⊗:) (FinFusion lab t) (FinFusion lab t) where
  second
    :: forall a b c
     . ( Object (FinFusion lab t) a
       , Object (FinFusion lab t) b
       , Object (FinFusion lab t) c
       , Object (FinFusion lab t) (c :⊗: a)
       , Object (FinFusion lab t) (c :⊗: b)
       )
    => FinFusion lab t a b
    -> FinFusion lab t (c :⊗: a) (c :⊗: b)
  second = bimap (id :: FinFusion lab t c c)

instance (lab ~ Label t, FiniteFusionC t) => Bifunctor (:⊗:) (FinFusion lab t) (FinFusion lab t) (FinFusion lab t) where
  bimap
    :: forall a b c d
     . ( Object (FinFusion lab t) a
       , Object (FinFusion lab t) b
       , Object (FinFusion lab t) c
       , Object (FinFusion lab t) d
       , Object (FinFusion lab t) (a :⊗: c)
       , Object (FinFusion lab t) (b :⊗: d)
       )
    => FinFusion lab t a b
    -> FinFusion lab t c d
    -> FinFusion lab t (a :⊗: c) (b :⊗: d)
  bimap (FinFusion f) (FinFusion g) =
    FinFusion $
      tensorHomDual
        (Proxy @t)
        (idHomDual @(Mults t (a :⊗: c)))
        (idHomDual @(Mults t (b :⊗: d)))
        f
        g

instance (lab ~ Label t, FiniteFusionC t) => Associative (FinFusion lab t) (:⊗:) where
  associate
    :: forall a b c
     . ( Object (FinFusion lab t) a
       , Object (FinFusion lab t) b
       , Object (FinFusion lab t) c
       , Object (FinFusion lab t) (a :⊗: b)
       , Object (FinFusion lab t) (b :⊗: c)
       , Object (FinFusion lab t) ((a :⊗: b) :⊗: c)
       , Object (FinFusion lab t) (a :⊗: (b :⊗: c))
       )
    => FinFusion lab t ((a :⊗: b) :⊗: c) (a :⊗: (b :⊗: c))
  associate =
    FinFusion $
      associateHomDual
        (Proxy @t)
        (idHomDual @(Mults t ((a :⊗: b) :⊗: c)))
        (idHomDual @(Mults t (a :⊗: (b :⊗: c))))
        (multsVal @(Mults t a))
        (multsVal @(Mults t b))
        (multsVal @(Mults t c))

  disassociate
    :: forall a b c
     . ( Object (FinFusion lab t) a
       , Object (FinFusion lab t) b
       , Object (FinFusion lab t) c
       , Object (FinFusion lab t) (a :⊗: b)
       , Object (FinFusion lab t) (b :⊗: c)
       , Object (FinFusion lab t) ((a :⊗: b) :⊗: c)
       , Object (FinFusion lab t) (a :⊗: (b :⊗: c))
       )
    => FinFusion lab t (a :⊗: (b :⊗: c)) ((a :⊗: b) :⊗: c)
  disassociate =
    FinFusion $
      disassociateHomDual
        (Proxy @t)
        (idHomDual @(Mults t (a :⊗: (b :⊗: c))))
        (idHomDual @(Mults t ((a :⊗: b) :⊗: c)))
        (multsVal @(Mults t a))
        (multsVal @(Mults t b))
        (multsVal @(Mults t c))

instance (lab ~ Label t, FiniteFusionC t) => Monoidal (FinFusion lab t) (:⊗:) where
  type Id (FinFusion lab t) (:⊗:) = 'Irrep (UnitLab t :: lab)

  idl
    :: forall a
     . ( Object (FinFusion lab t) a
       , Object (FinFusion lab t) ('Irrep (UnitLab t :: lab))
       , Object (FinFusion lab t) ('Irrep (UnitLab t :: lab) :⊗: a)
       )
    => FinFusion lab t ('Irrep (UnitLab t :: lab) :⊗: a) a
  idl =
    FinFusion $
      fillHomDual
        (idHomDual @(Mults t ('Irrep (UnitLab t :: lab) :⊗: a)))
        (idHomDual @(Mults t a))
        (\_ _ _ -> unitorSector)

  idr
    :: forall a
     . ( Object (FinFusion lab t) a
       , Object (FinFusion lab t) ('Irrep (UnitLab t :: lab))
       , Object (FinFusion lab t) (a :⊗: 'Irrep (UnitLab t :: lab))
       )
    => FinFusion lab t (a :⊗: 'Irrep (UnitLab t :: lab)) a
  idr =
    FinFusion $
      fillHomDual
        (idHomDual @(Mults t (a :⊗: 'Irrep (UnitLab t :: lab))))
        (idHomDual @(Mults t a))
        (\_ _ _ -> unitorSector)

  coidl
    :: forall a
     . ( Object (FinFusion lab t) a
       , Object (FinFusion lab t) ('Irrep (UnitLab t :: lab))
       , Object (FinFusion lab t) ('Irrep (UnitLab t :: lab) :⊗: a)
       )
    => FinFusion lab t a ('Irrep (UnitLab t :: lab) :⊗: a)
  coidl =
    FinFusion $
      fillHomDual
        (idHomDual @(Mults t a))
        (idHomDual @(Mults t ('Irrep (UnitLab t :: lab) :⊗: a)))
        (\_ _ _ -> unitorSector)

  coidr
    :: forall a
     . ( Object (FinFusion lab t) a
       , Object (FinFusion lab t) ('Irrep (UnitLab t :: lab))
       , Object (FinFusion lab t) (a :⊗: 'Irrep (UnitLab t :: lab))
       )
    => FinFusion lab t a (a :⊗: 'Irrep (UnitLab t :: lab))
  coidr =
    FinFusion $
      fillHomDual
        (idHomDual @(Mults t a))
        (idHomDual @(Mults t (a :⊗: 'Irrep (UnitLab t :: lab))))
        (\_ _ _ -> unitorSector)

-- | Skeletal unitor on one Irr sector: copy coordinates (dims agree for a
-- well-formed fusion theory; 'fromList' is the runtime check).
unitorSector
  :: forall nd nc
   . SectorDual nd nc
  => DualVector (C nd) ⊗ C nc
unitorSector =
  sectorFromMap $
    arr $
      LinearFunction $ \v ->
        fromList (VS.toList (unwrap v)) :: C nc

instance (lab ~ Label t, FiniteFusionC t) => Braided (FinFusion lab t) (:⊗:) where
  braid
    :: forall a b
     . ( Object (FinFusion lab t) a
       , Object (FinFusion lab t) b
       , Object (FinFusion lab t) (a :⊗: b)
       , Object (FinFusion lab t) (b :⊗: a)
       )
    => FinFusion lab t (a :⊗: b) (b :⊗: a)
  braid =
    FinFusion $
      braidHomDual
        (Proxy @t)
        (idHomDual @(Mults t (a :⊗: b)))
        (idHomDual @(Mults t (b :⊗: a)))
        (multsVal @(Mults t a))
        (multsVal @(Mults t b))

instance (lab ~ Label t, FiniteFusionC t) => CompactClosed (FinFusion lab t) (:⊗:) where
  type Dual (FinFusion lab t) (:⊗:) a = DualObj t a
  unit = cap @lab @t
  counit = cup @lab @t
