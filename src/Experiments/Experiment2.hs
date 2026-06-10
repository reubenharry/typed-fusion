{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoStarIsType #-}

module Experiments.Experiment2 where



import Data.Kind (Type)
import GHC.TypeLits
import Numeric.LinearAlgebra.Static (M, Sized (..), C)
import Linear.V (V (..), Finite (toV))
import Symmetry.Utils
import Math.LinearMap.Category (type (-+>), type (+>), LinearMap (..), AdditiveGroup, VectorSpace, DimensionAware (..), Dimensional, TensorSpace, PseudoAffine, Semimanifold)
import Control.Arrow.Constrained (EnhancedCat(..))
import Data.VectorSpace (AdditiveGroup(..), VectorSpace (..))
import Symmetry.Orphans hiding (Irrep)
import Data.Data (Proxy(..))
import Data.Complex (Complex)
import Math.VectorSpace.DimensionAware (DimensionalityWitness(..), Dimensional (..))
import Data.Singletons
import Math.LinearMap.Category.Instances.Deriving (TensorSpace(..), PseudoAffine (..), Semimanifold (..))
import Data.Basis (HasBasis(..))
import Linear (V2(..), V1 (..))
import qualified Data.Vector as V

-- todo: the Sector type should really have an abstract notion of a linear map

--------------------------------------------------------------------------------
-- Representation type
--------------------------------------------------------------------------------

type Irrep = Z
type Multiplicity = Nat

type family Dim (m :: Multiplicity) :: Nat where
  Dim p = p

type Mat = M
type Vector = C
type Product = V

type family RepToVectors
  (r :: [(Irrep, Multiplicity)])
  :: [Type] where

  RepToVectors '[] =
    '[]

  RepToVectors ('(i,m) ': rs) =
    Product (Dim m) (IrrepU1 i) ': RepToVectors rs

newtype Representation (r :: [(Irrep, Multiplicity)]) = Representation (HList (RepToVectors r))

deriving instance Show (HList (RepToVectors r)) => Show (Representation r)


--------------------------------------------------------------------------------
-- Tensor product of two representations
--------------------------------------------------------------------------------

type family Tensor
  (r :: [(Irrep, Multiplicity)])
  (q :: [(Irrep, Multiplicity)])
  :: [(Irrep, Nat)] where

  Tensor '[] q =
    '[]

  Tensor ('(i,m) ': rs) q =
    Append
      (TensorOne '(i,m) q)
      (Tensor rs q)

type family TensorOne
  (x :: (Irrep, Multiplicity))
  (q :: [(Irrep, Multiplicity)])
  :: [(Irrep, Nat)] where

  TensorOne x '[] =
    '[]

  TensorOne '(i,m) ('(j,n) ': qs) =
    '( Add i j
     , Scale m n
     )
    ': TensorOne '(i,m) qs

--------------------------------------------------------------------------------
-- Dual representation
--------------------------------------------------------------------------------

type family DualRep
  (r :: [(Irrep, Multiplicity)])
  :: [(Irrep, Nat)] where

  DualRep '[] =
    '[]

  DualRep ('(i,m) ': rs) =
    '(Negate i, m)
    ': DualRep rs

--------------------------------------------------------------------------------
-- Turn charge-zero sectors into actual matrices
--------------------------------------------------------------------------------

-- only keep the trivial blocks
type family TrivialIrreps
  (r :: [(Irrep, Multiplicity)])
  :: [Type] where

  TrivialIrreps '[] =
    '[]

  TrivialIrreps ('( 'Zero,m) ': rs) =
    Product (Dim m) (IrrepU1 'Zero) ': TrivialIrreps rs

  TrivialIrreps ('(i,m) ': rs) =
    TrivialIrreps rs

--------------------------------------------------------------------------------
-- Final intertwiner type
--------------------------------------------------------------------------------

newtype
  FlatIntertwiner
  (r :: [(Irrep, Multiplicity)])
  -- -$+>
  (q :: [(Irrep, Multiplicity)])
  =
  FlatIntertwiner
    (HList (TrivialIrreps
      (
        Tensor (DualRep r) q)))

-- type family Lookup
--   (i :: Irrep)
--   (r :: [(Irrep, Multiplicity)])
--   :: Maybe Multiplicity where
--   Lookup i '[] = 'Nothing
--   Lookup i ('(i,m) ': rs) = 'Just m
--   Lookup i ('(j,m) ': rs) = Lookup i rs


-- type family ToMapList
--   (r :: [(Irrep, Multiplicity)])
--   (q :: [(Irrep, Multiplicity)])
--   :: [Type] where

--   ToMapList r '[] =
--     '[]

--   ToMapList r ('(i,n) ': qs) =
--     AddMap i (Lookup i r) n (ToMapList r qs)


-- type family AddMap
--   (i :: Irrep)
--   (found :: Maybe Multiplicity)
--   (n :: Multiplicity)
--   (rest :: [Type])
--   :: [Type] where

--   AddMap i 'Nothing n rest =
--     rest

--   AddMap i ('Just m) n rest =
--     (C m +> C n) ': rest

-- newtype
  
--   (r :: [(Irrep, Multiplicity)])
--   -$+>
--   (q :: [(Irrep, Multiplicity)])
--   =
--   Intertwiner
--     (HList (ToMapList r q))

--------------------------------------------------------------------------------
-- Concrete tensor-product values
--------------------------------------------------------------------------------

-- One tensor-product sector
--
-- charge i
-- multiplicity m
--
-- newtype Sector
--   (i :: Irrep)
--   (m :: Multiplicity)
--   =
--   Sector (C (Dim m) +> C (Dim m))

-- instance KnownNat m => Show (Sector i m) where
--   show (Sector f) = "Sector " ++ show (getLinearMap f)

--------------------------------------------------------------------------------
-- Convert a representation description into concrete sectors
--------------------------------------------------------------------------------

-- type family Sectors
--   (r :: [(Irrep, Multiplicity)])
--   :: [Type] where

--   Sectors '[] =
--     '[]

--   Sectors ('(i,m) ': rs) =
--     Sector i m ': Sectors rs

-- type RepValue
--   (r :: [(Irrep, Multiplicity)])
--   =
--     (HList (Sectors r))

-- deriving instance
--   Show (HList (Sectors r))
--   => Show (RepValue r)



-- example2 :: Tensor R Q
-- example2 = undefined -- Intertwiner $ undefined

-- what do i want to be able to write... I'd like basis independent linear maps between representations

instance
  ( HPure AdditiveGroup (RepToVectors r)
  , HMap AdditiveGroup (RepToVectors r)
  , HZipWith AdditiveGroup (RepToVectors r)
  ) => AdditiveGroup (Representation r) where

  zeroV =
    Representation $
      hpureC (Proxy @AdditiveGroup) zeroV

  Representation xs ^+^ Representation ys =
    Representation $
      hzipWithC (Proxy @AdditiveGroup) (^+^) xs ys

  negateV (Representation xs) =
    Representation $
      hmapC (Proxy @AdditiveGroup) negateV xs

instance
  ( HPure VectorSpace (RepToVectors r), HPure AdditiveGroup (RepToVectors r)
  , HMap VectorSpace (RepToVectors r), HMap AdditiveGroup (RepToVectors r)
  , HZipWith VectorSpace (RepToVectors r), HZipWith AdditiveGroup (RepToVectors r)
  ) => VectorSpace (Representation r) where
  type Scalar (Representation r) = Complex Double
  (*^) f (Representation xs) =
    Representation $
      hmapC (Proxy @VectorSpace) (undefined *^) xs

type family RepDim (r :: [(Irrep, Multiplicity)]) :: Nat where
  RepDim '[] = 0

  RepDim ('(i,m) ': rs) =
    1 * Dim m + RepDim rs

instance (HPure VectorSpace (RepToVectors r), HPure AdditiveGroup (RepToVectors r), HMap VectorSpace (RepToVectors r), HMap AdditiveGroup (RepToVectors r), HZipWith VectorSpace (RepToVectors r), HZipWith AdditiveGroup (RepToVectors r), KnownNat (RepDim r)) => DimensionAware (Representation r) where
  type StaticDimension (Representation r) = 'Just (RepDim r)
  dimensionalityWitness = IsStaticDimensional

instance (KnownNat (RepDim r), n ~ RepDim r, HPure VectorSpace (RepToVectors r), HPure AdditiveGroup (RepToVectors r), HMap VectorSpace (RepToVectors r), HMap AdditiveGroup (RepToVectors r), HZipWith VectorSpace (RepToVectors r), HZipWith AdditiveGroup (RepToVectors r)) => n `Dimensional` Representation r where
  knownDimensionalitySing = sing
  unsafeFromArrayWithOffset i ar = undefined -- Representation (unsafeFromArrayWithOffset i ar)
  unsafeWriteArrayWithOffset = undefined --  ar i (IrrepU1 v) = unsafeWriteArrayWithOffset ar i v

instance (KnownNat (RepDim r), Scalar (Representation r) ~ Complex Double) => Eq (Representation r) where
  (==) = undefined
  (/=) = undefined
  
instance (KnownNat (RepDim r), n ~ RepDim r, HPure VectorSpace (RepToVectors r), HPure AdditiveGroup (RepToVectors r), HMap VectorSpace (RepToVectors r), HMap AdditiveGroup (RepToVectors r), HZipWith VectorSpace (RepToVectors r), HZipWith AdditiveGroup (RepToVectors r)) => Semimanifold (Representation r) where
  type Needle (Representation r) = C (RepDim r)
  Representation xs .+~^ δ = undefined -- Representation $ hzipWithC (Proxy @Semimanifold) (.+~^) xs ys

instance (KnownNat (RepDim r), n ~ RepDim r, HPure VectorSpace (RepToVectors r), HPure AdditiveGroup (RepToVectors r), HMap VectorSpace (RepToVectors r), HMap AdditiveGroup (RepToVectors r), HZipWith VectorSpace (RepToVectors r), HZipWith AdditiveGroup (RepToVectors r)) => PseudoAffine (Representation r) where
  Representation xs .-~! Representation ys = undefined --  Representation $ hzipWithC (Proxy @PseudoAffine) (.-~!) xs ys
  Representation xs .-~. Representation ys = undefined -- Representation $ hzipWithC (Proxy @PseudoAffine) (.-~.) xs ys

instance (KnownNat (RepDim r), Scalar (Representation r) ~ Complex Double, HPure VectorSpace (RepToVectors r), HPure AdditiveGroup (RepToVectors r), HMap VectorSpace (RepToVectors r), HMap AdditiveGroup (RepToVectors r), HZipWith VectorSpace (RepToVectors r), HZipWith AdditiveGroup (RepToVectors r)) => TensorSpace (Representation r) where
  type TensorProduct (Representation r) w = Complex Double --  HList (RepToVectors (Tensor ( r) w))
--   scalarSpaceWitness = undefined -- unsafeCoerce (scalarSpaceWitness @(RepDim r))
--   linearManifoldWitness = undefined
--   zeroTensor = undefined
--   toFlatTensor = undefined
--   fromFlatTensor = undefined
--   tensorProduct = undefined
--   transposeTensor = undefined
--   fmapTensor = undefined
--   fzipTensorWith = undefined
--   tensorUnsafeFromArrayWithOffset = undefined
--   tensorUnsafeWriteArrayWithOffset = undefined
--   coerceFmapTensorProduct = undefined
--   wellDefinedTensor = undefined
--   vectorConjugate = undefined
  -- type TensorProduct (IrrepU1 p) w = TensorProduct (C (U1IrrepDim p)) w



-- testcase = decompose rValue

  -- dimensionVal @(Representation '[ '(Pos 3,4)])

-- instance AdditiveGroup (Representation '[]) where
--   zeroV = Representation HNil
--   (^+^) a b = Representation HNil
--   (^-^) a b = Representation HNil
--   negateV a = Representation HNil

-- -- instance (AdditiveGroup (Representation r), KnownNat m) => AdditiveGroup (Representation ('(i,m) ': r)) where
--   zeroV :: (AdditiveGroup (Representation r), KnownNat m) => Representation ('(i, m) : r)
--   zeroV = case zeroV @(Representation r) of
--       Representation xs ->
--         Representation
--            (SectorVec (zeroV :: C (Dim m))
--          :& xs
--           )


--     -- Representation ((SectorVec (zeroV :: C (Dim m))) :& undefined) -- (SectorVec (zeroV :: C (Dim m)) :& HNil)
--   (^+^) = undefined
--   -- (^-^) a b = case a of
--   --     Representation xs ->
--   --       case b of
--   --         Representation ys ->
--   (^-^) = undefined
--   negateV = undefined

-- instance AdditiveGroup (Representation r) where
--   zeroV = undefined


--------------------------------------------------------------------------------
-- Example tensor product
--------------------------------------------------------------------------------

type R =
  '[ '( 'Pos 1, 2)
   , '( 'Pos 2, 1)
   ]

type Q =
  '[
    '( 'Pos 3, 1)
   , '( 'Pos 1, 1)
   ]


rValue :: Representation R
rValue =
  Representation
    ( toV @V2 (V2 (IrrepU1 @(Pos 1) (konst 1)) (IrrepU1 @(Pos 1) (konst 1)))   -- vector in charge +1 sector
   :& toV @V1 (V1 (IrrepU1 @(Pos 2) (konst 1)))   -- vector in charge +2 sector
   :& HNil
    )

tensorExample :: Representation (Tensor R Q)
tensorExample = Representation (
     (
        (toV @V2 (V2 (IrrepU1 (konst 1 :: C 1)) (IrrepU1 (konst 1 :: C 1))) )
        :& (toV @V2 (V2 (IrrepU1 (konst 1 :: C 1)) (IrrepU1 (konst 1 :: C 1))) )
     :& (toV @V1 (V1 (IrrepU1 (konst 1 :: C 1)))) 
     :& (toV @V1 (V1 (IrrepU1 (konst 1 :: C 1)))) 
     :& HNil)   -- charge +2
  --  :&  (LinearMap (konst 1) :: C (Dim 2) +> C (Dim 2))   -- charge +3
  --  :&  (LinearMap (konst 1) :: C (Dim 1) +> C (Dim 1))   -- charge +3
  --  :&  (LinearMap (konst 1) :: C (Dim 1) +> C (Dim 1))   -- charge +4
   )

example :: FlatIntertwiner R Q
example = FlatIntertwiner undefined 
  -- Intertwiner
  --   (  (undefined :: C (Dim 2) +> C (Dim 2))
  -- --  :& Block (undefined :: M 2 2)
  --  :& HNil
  --   )