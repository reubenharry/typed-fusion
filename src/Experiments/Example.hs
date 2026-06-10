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

module Experiments.Example where



import Data.Kind (Type)
import GHC.TypeLits
import Numeric.LinearAlgebra.Static (M, Sized (..), C, vector, R, build)
import Linear.V (V (..), Finite (toV))
import Utils
import Math.LinearMap.Category (type (-+>), type (+>), LinearMap (..), AdditiveGroup, VectorSpace, DimensionAware (..), Dimensional, TensorSpace, PseudoAffine, Semimanifold)
import Control.Arrow.Constrained (EnhancedCat(..))
import Data.VectorSpace (AdditiveGroup(..), VectorSpace (..))
import Orphans (SU2Irreps, IrrepSU2)
import Data.Data (Proxy(..))
import Data.Complex (Complex (..))
import Math.VectorSpace.DimensionAware (DimensionalityWitness(..), Dimensional (..))
import Data.Singletons
import Math.LinearMap.Category.Instances.Deriving (TensorSpace(..), PseudoAffine (..), Semimanifold (..))
import Data.Basis (HasBasis(..))
import Linear (V2(..), V1 (..), V3 (..))
import qualified Data.Vector as V
-- import SU2 hiding (Irrep)
-- import Orphans (IrrepSU2(..), Irreps, Group(..), Irrep(..))
import qualified Data.Vector.Sized as VS
import Data.IndexedListLiterals (IndexedListLiterals)
import Experiments.General
import Orphans hiding (U1, SU2, Irrep) 



example1 :: C 2
example1 = vec (1,2)

example2 :: C 3
example2 = vec (4,5,6)

-- example2' :: C 3 +> C 2
-- example2' = LinearMap ( undefined :: M 3 2 ) where
--     a = vec (1,2,3) :: C 3
--     b = 

example3 :: C 2
example3 = example1 ^+^ example1

example4 :: Irrep SU2 2 -- j = 1/2
example4 = Irrep (vec (1,2,3))

example4' :: Irrep U1 (Pos 2) -- j = 1/2
example4' = Irrep 1


example5 :: Irrep SU2 1 ⊗ Irrep SU2 3 -- 1/2 ⊗ 3/2 = 1 ⊕ 2
example5 = Representation (
    toV (V1 (Irrep (vec (1,2,3)))) :& toV (V1 (Irrep (vec (4,5,6,7,8)))) :& HNil
    )

example6 :: Irrep SU2 1 ⊗ Irrep SU2 3 -- 1/2 ⊗ 3/2 = 1 ⊕ 2
example6 = Representation undefined


example7 :: Irrep U1 (Pos 1) ⊗ Irrep U1 (Pos 1) -- 1/2 ⊗ 3/2 = 1 ⊕ 2
example7 = Representation undefined


example8 :: Representation U1 '[ '(Pos 1, 1)] --> Representation U1 '[ '(Pos 2, 1)] -- 1/2 ⊗ 3/2 = 1 ⊕ 2
example8 =  HNil

example8' :: Representation SU2 '[ '(3, 1)] --> Representation SU2 '[ '(2, 1)] -- 1/2 ⊗ 3/2 = 1 ⊕ 2
example8' =  HNil






















check :: VS.Vector 2 (Complex Double)
check = VS.fromTuple (1,2)

type a --> b = Intertwiner a b

foo :: C 2
foo = fromList $ VS.toList check

bar :: C 2
bar = vec (1,2)

-- vec :: (Sized t c d, KnownNat n) => a -> c
vec :: (Sized t c d, IndexedListLiterals    a n t,  KnownNat n, c ~ C n) => a -> c
vec a = (fromList . VS.toList . VS.fromTuple) a


