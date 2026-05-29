
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ViewPatterns #-}
{- HLINT ignore "Parenthesize unary negation" -}
{- HLINT ignore "Move brackets to avoid $" -}
{- HLINT ignore "Redundant $" -}

module TensorNetwork where

import Math.LinearMap.Category.Class
import Data.VectorSpace
import Control.Category.Constrained hiding (iso)
import Prelude hiding ((||), ($), id, (.))
import Math.LinearMap.Category (LinearFunction(..), adjoint, eigen, HilbertSpace, (·), Semimanifold(Needle), TensorDecomposable, RieszDecomposable, FiniteDimensional (..), SubBasis, constructEigenSystem, roughEigenSystem, Norm (Norm, applyNorm), Eigenvector (ev_Eigenvector, ev_Eigenvalue), euclideanNorm, pseudoInverse, (<$|), normSq, (|$|), riesz)
import GHC.TypeLits (Nat, KnownNat, type (*), type (<=))
import Linear.V (V)
import Linear (V2 (V2), V1 (V1), V3 (V3), E (..))
import GHC.Generics (Rep)
import Data.Void (Void)
import Data.Coerce (coerce, Coercible)
import Math.LinearMap.Asserted
import Math.VectorSpace.Dual (Dual)
import Control.Arrow.Constrained (arr, Morphism (..), ($), Function)
import Control.Arrow ((&&&))
import Data.Foldable (minimumBy)
import Data.Ord (comparing)
import Math.Manifold.Core.Types (ℝ)
import qualified Control.Arrow.Constrained as C
import qualified Test.QuickCheck as QC
import Data.Complex (Complex ((:+)))
import Math.VectorSpace.DimensionAware
import Math.LinearMap.Category.Instances.Deriving (PseudoAffine)
import Data.VectorSpace.Free (FreeVectorSpace, AffineSpace(Diff, (.+^), (.-.)), (^*^), vmap, V4, HasBasis (..))
import Math.OrphanInstances
import qualified Data.Complex as C
import Numeric.IEEE (IEEE)
import Linear.V (V(..))
import Control.Lens (_1, _2, (^.), (^?), (^..), cosmos, to, (.~), (&))
import Control.Lens (from)
import Data.Kind (Type)
import System.Random (random, RandomGen, getStdRandom, mkStdGen, StdGen, uniformR, randomR)
import Math.LinearMap.Category (orthogonalComplementProj)
import Data.Fixed (mod')
import System.Random.Internal (UniformRange, uniformRM, StatefulGen)
import qualified Debug.Trace
import System.Random.Stateful (globalStdGen)
import Control.Monad.Trans.State
import Data.Singletons (SingKind(..))
import Math.VectorSpace.Initializable
import Data.Functor.Identity (runIdentity)
import Data.Functor.Rep (tabulate, index)
import Control.Lens (to, iso, from, Iso')
import Math.LinearMap.Category.Instances
import Data.Number.NormedAlgebra (NormedAlgebra(RealPart))
import Numeric.LinearAlgebra.Static (C, Sized (..), M, R, svdTall, L, svdFlat, diag, Domain (diagR), complex)
import Numeric.LinearAlgebra.Static.COrphans
import Math.TensorNetwork (svd)
import qualified Numeric.LinearAlgebra as H
import Numeric.LinearAlgebra (Matrix, Transposable (..))
import Data.Maybe (fromMaybe)

(*<.>) :: (InnerSpace v, TensorSpace v) => v -> v -> Scalar v
x *<.> y = applyAntilinearFunction vectorConjugate x <.> y

applyAntilinearFunction (AntilinearFunction f) = f

checkInnerProduct :: Complex Double
checkInnerProduct = innerProduct where 
    u = V1 (0 :+ (1))
    v = V1 (0 :+ 1)
    innerProduct = (applyAntilinearFunction vectorConjugate u) <.> v

checkTensorInnerProduct :: Complex Double
checkTensorInnerProduct = innerProduct where 
    u = Tensor $ V2 (V2 (0 :+ 1) (0 :+ 1)) (V2 (0 :+ 1) (0 :+ 1)) :: V2 Field ⊗ V2 Field
    v = Tensor $ V2 (V2 (0 :+ 1) (0 :+ 1)) (V2 (0 :+ 1) (0 :+ 1)) :: V2 Field ⊗ V2 Field
    innerProduct = u *<.> v

checkConjugate = applyAntilinearFunction vectorConjugate (V1 (0 :+ 1) :: V1 Field)

type Field = Complex Double

type VP = V2
type VB = V3

data TN vp vb = TensorNetwork  {leftTN :: LinearMap Field (vp Field) (vb Field), rightTN :: LinearMap Field (vp Field) (vb Field)}

type Ham vp = LinearMap Field (vp Field ⊗ vp Field) (vp Field ⊗ vp Field)

getBasis = baz where

    bar :: V2 Field ⊗ V2 Field
    bar = Tensor $ V2 (V2 1 2) (V2 3 4)

    baz = decompose' bar (E _1, E _2)

ham :: Ham VP
ham = fst $ recomposeLinMap entireBasis [
    undefined
 ]

example :: Tensor Field (VP Field) (VP Field)
example = undefined

(||) :: forall f a b. (Function f, Object f a, Object f b) => f a b -> a -> b
(||) = ($)



ex1 :: (VP Field ⊗ VP Field)
ex1 = Tensor $ V2 (V2 (1 :+ 2) (3 :+ 4)) (V2 (5 :+ 6) (7 :+ 8))

ex4 :: Field
ex4 = ex1 <.> ex1


-- converts a tensor network intox a tensor
tnToTensor :: TN VP VB -> (VP Field ⊗ VP Field)
tnToTensor (TensorNetwork a b) = coerce ((adjoint $ b) . a)


computeEnergy :: Ham VP -> TN VP VB -> Field
computeEnergy ham tn@(TensorNetwork a b) = m <.> (ham || m)
    where m = tnToTensor tn

test :: Field
test = (0 :+ 1) <.> (0 :+ 1)

im = 0 :+ 1

test2 = a <.> a where
    a = (V1 im) :: V1 Field
    -- a :: Tensor Field (V2 Field) (V2 Field)
    -- a = Tensor $ V2 (V2 (im) (im)) (V2 (im) (im))
    -- a :: Tensor Field (V2 Field) (V2 Field)
    -- a = Tensor $ V2 (V2 (0 :+ 1) (0 :+ 1)) (V2 (0 :+ 1) (0 :+ 1))
    -- b :: Tensor Field (V2 Field) (V2 Field)
    -- b = Tensor $ V2 (V2 (0 :+ 1) (0 :+ 1)) (V2 (0 :+ 1) (0 :+ 1))

test3 = baz where
    foo ::  V2 (V2 Field)
    foo = V2 (V2 (1 :+ 2) (3 :+ 4)) (V2 (5 :+ 6) (7 :+ 8))

    bar :: V2 Field ⊗ V2 Field
    bar = Tensor foo

    baz = bar ^.. to getTensorProduct . traverse . traverse

    foo2 :: V2 (V2 Field)
    foo2 = foo & traverse . traverse .~ undefined

test4 :: V2 Field +> Field
test4 = LinearMap $ V2 undefined undefined

test5 :: V2 Field
test5 = coerce test4

-- test6 = bar where
--     baz = coerce test5 :: V2 Field +> Field
--     foo = adjointCorrect baz
--     bar = coerce foo :: V2 Field

type W' = V2 Field
type V' = V3 Field

derivedNorm :: V' -> DualSpace' V'
derivedNorm v = dagger v'  where
    v' :: (Complex Double) -+> V'
    v' = undefined


class Category k => DaggerCategory (k :: κ -> κ -> Type) where

    dagger :: forall (v :: κ) (w :: κ). k v w -> k w v


instance DaggerCategory (LinearFunction s) where
    dagger = undefined



-- adjoint' :: (W' -+> V') -> (V' -+> W')
-- adjoint' lm = applyCoNorm coNorm . vectorConjugate . flipBilin rhoA where
--     rhoA = LinearFunction (applyNorm' norm)  . lm

norm :: Norm' V'
norm = undefined

coNorm :: CoNorm W'
coNorm = undefined

type DualSpace' v = v -+> Scalar v

newtype Norm' v = Norm' {
    applyNorm' :: v -> DualSpace' v
}

newtype CoNorm v = CoNorm {
  applyCoNorm :: DualSpace' v -+> v
}


-- monoidalproduct :: forall u u' v v' s. (TensorSpace u, TensorSpace u', TensorSpace v, TensorSpace v') => LinearMap s u v -> LinearMap s u' v' -> LinearMap s (u ⊗ u') (v ⊗ v')
monoidalunit :: LinearMap Field (VP Field) (VB Field) -> LinearMap Field (VP Field ⊗ VB Field) (VP Field ⊗ VP Field)
monoidalunit l1 = undefined where

    l1' :: VP Field ⊗ VB Field
    l1' = coerce l1


    l3 :: VP Field ⊗ (VP Field ⊗ VB Field) ⊗ VP Field
    l3 = undefined ⊗ undefined

    foo :: TensorProduct (VP Field ⊗ VB Field) (VP Field ⊗ VP Field)
    foo = coerce bar

    bar :: TensorProduct (DualVector (VP Field ⊗ VB Field)) (VP Field ⊗ VP Field)
    bar = undefined
    -- foo :: LinearFunction Field (VP Field ⊗ VP Field) (VP Field ⊗ VP Field)
    -- foo = getLinearFunction fmapTensor (arr ex1 :: LinearFunction Field (VP Field) (VP Field))

mat :: (V2 Field ⊗ V2 Field) +> (V2 Field ⊗ V2 Field)
mat = undefined -- LinearMap $ (V2 (V2 (1 :+ 2) (3 :+ 4)) (V2 (5 :+ 6) (7 :+ 8)))

mat2 :: VP Field +> VP Field
mat2 = LinearMap $ (V2 (V2 (1 :+ 2) (3 :+ 4)) (V2 (5 :+ 6) (7 :+ 8)))


-- bar2 = eigen mat

-- Conjugate every complex entry in the tensor (VP Field ⊗ VP Field).
-- Needed because adjoint is transpose-only; conjugate transpose = conjugateMap . adjoint.
-- conjugateMap :: (VP Field +> VP Field) -> (VP Field +> VP Field)
-- conjugateMap m = fromTensor $ conjugateTensor -+$> coerce m
--   where
--     conjugateTensor :: (VP Field ⊗ VP Field) -+> (VP Field ⊗ VP Field)
--     conjugateTensor = LinearFunction $ \(Tensor m) ->
--       Tensor (vmap (vmap C.conjugate) m)

matdag :: VP Field +> VP Field
matdag =  adjoint -+$> mat2

-- instance Show (LinearMap Field (VP Field) (VP Field)) where
--     show = show . getLinearMap

matreal :: VP Field +> VP Field
matreal = LinearMap $ (V2 (V2 1 2) (V2 3 4))

eigenDecomp = eigen euclideanNorm matreal

-- instance TensorDecomposable (LinearMap Field (VP Field) (VP Field))
-- instance RieszDecomposable (VP Field)

adjointF :: forall v w. (Coercible v (DualVector v), Scalar v ~ Scalar w, Coercible w (DualVector w), Coercible
                      (TensorProduct (DualVector v) w) (TensorProduct v w), TensorSpace v, TensorSpace w, Coercible
                      (TensorProduct (DualVector w) v) (TensorProduct w v)) => (v +> w) -> (w +> v)
adjointF m = coerce $ switched where

    switched :: (w) ⊗ (v)
    switched = transposeTensor $ coerce m


-- adjointRiesz :: (V2 Field +> V3 Field) -> (V3 Field +> V2 Field)
-- adjointRiesz ( f) = undefined  where 

--     adj = adjoint $ f :: DualVector (V3 Field) +> DualVector (V2 Field)
--     comp = arr riesz . coerce adj :: LinearMap Field (DualVector (V3 Field)) (V2 Field)

    -- unwrapped = (Tensor f) :: Tensor (Complex Double) (DualVector (V2 Field)) (V3 Field)
    -- Tensor adj = transposeTensor $ unwrapped :: Tensor (Complex Double) (V3 Field) (DualVector (V2 Field))
    -- wrapped = LinearMap adj  
    -- comp = riesz . adj
    -- foo :: (v) ⊗ (w)
    -- foo = coerce m

drmg :: Ham VP -> TN VP VB -> TN VP VB
drmg ham(TensorNetwork a b) = undefined
    where
        m :: LinearMap Field (VP Field ⊗ VB Field) (VP Field ⊗ VP Field)
        m = arr $ fmapTensor $ arr $ adjoint $ a

        heff :: (VP Field ⊗ VB Field) +> (VP Field ⊗ VB Field)
        heff = adjointF m . ham . m

        adj' :: (DualVector ((VP Field ⊗ VP Field))) +> (DualVector ((VP Field ⊗ VB Field)))
        adj' = (adjoint $ m)

        eigenvals :: [(Field, VP Field ⊗ VB Field)]
        eigenvals = eigen euclideanNorm heff

        newA :: (VP Field ⊗ VB Field)
        newA = snd $ minimumBy (comparing $ C.magnitude . fst) eigenvals



-- instance QC.Arbitrary (TN VP VB) where
--     arbitrary = TensorNetwork <$> QC.arbitrary <*> QC.arbitrary


-- instance QC.Arbitrary (VB Field) where
--     arbitrary = do
--         V3 <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary

-- instance QC.Arbitrary (VB Double) where
--     arbitrary = do
--         V3 <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary

-- | Draw a real number from a standard normal N(0,1) using the Box-Muller transform.
randomGaussian :: RandomGen g => g -> (Double, g)
randomGaussian g =
  let (u1, g') = random g
      (u2, g'') = random g'
      u1' = if u1 == 0 then 1e-10 else u1  -- avoid log 0
      r = sqrt (-2 * log u1')
      theta = 2 * pi * u2
  in (r * cos theta, g'')

-- | Draw a real number from N(0,1) using the global random generator.
randomGaussianIO :: IO Double
randomGaussianIO = getStdRandom randomGaussian

randomComplex :: QC.Gen Field
randomComplex = QC.arbitrary

-- randomMatrixIO :: IO (Ham VP)
-- randomMatrixIO = QC.generate randomMatrix

-- instance QC.Arbitrary field => QC.Arbitrary (V2 field) where
--     arbitrary = V2 <$> QC.arbitrary <*> QC.arbitrary

-- randomMatrix :: QC.Gen (Ham VP)
-- randomMatrix = QC.arbitrary



-- instance Semimanifold (Complex Double) where
--     -- semimanifoldWitness = SemimanifoldWitness BoundarylessWitness

-- instance PseudoAffine (Complex Double) where

-- instance AffineSpace (Complex Double) where
--     type Diff (Complex Double) = Complex Double
--     (.+^) = (^+^)
--     (.-.) = (^-^)

-- instance TensorSpace (Complex Double) where




data MPS vp vb = MPS {
    leftMPS :: (C vb) +> (C vp),
    rightMPS :: (C vb) +> (C vp),
    center :: (C vb) +> (C vb ⊗  C vp )} 

instance (KnownNat vb, KnownNat (vb*vp)) => Show (MPS vp vb) where
    show = show . getLinearMap . center

data MPO vp vb = MPO {
    leftMPO :: (C vb ⊗ C vp) +> (C vp),
    rightMPO :: (C vb ⊗ C vp) +> (C vp),
    centerMPO :: (C vb ⊗ C vp) +> (C vb ⊗  C vp )}

p = 3
b = 2

type Center vp vb = (C vb) +> (C vb ⊗ C vp)

solveAtSite :: forall p b. (KnownNat p, KnownNat b) => MPO p b -> MPS p b -> MPS p b
solveAtSite ham@(MPO h1 h2 h3) mps@(MPS m1 m2 m3) =  MPS m1 m2 minimal
    where
        m :: (C vb +> (C vb ⊗ C vp)) +> (C p ⊗ C p ⊗ C p )
        m = undefined 

        heff :: Center p b +> Center p b
        heff = undefined
        -- heff = adjointF m . ham . m

        eigenvals :: [(Field, Center p b)]
        eigenvals = eigen euclideanNorm heff

        minimal :: (Center p b)
        minimal = snd $ minimumBy (comparing $ C.magnitude . fst) eigenvals

move :: forall p b. (KnownNat p, KnownNat b, KnownNat (b * p), KnownNat (p * (b * p)), b <= b*p) => MPO p b -> MPS p b -> MPS p b
move ham mps@(MPS m1 m2 m3) = MPS m1 m2' m3' where
    -- (u, s, v) = undefined m3
    -- foo = svd undefined m3 3
    unpackedm3 = (getLinearMap m3) :: M (b) (b*p)
    -- bar = unwrap unpackedm3 :: Matrix (Complex Double)
    -- -- (u,s,v) = H.thinSVD bar
    -- -- u' = LinearMap $ fromMaybe undefined $ (create u :: Maybe (M b b)) :: C b +> C b 
    -- -- v' = LinearMap $ fromMaybe undefined $ (create v :: Maybe (M (b) (p*(b*p)))) :: (C b ⊗ C p) +> (C b ⊗ C p)
    -- newh2 = undefined -- undefined (undefined s v) m2
    -- newh3 = undefined


    (u,s,v) = svdTallC (tr unpackedm3 :: M (b*p) b)
    ch = LinearMap (diagR 0 (complex s) :: M b b) :: C b +> C b
    m2' = m2 . ch .  LinearMap  (tr v) :: C b +> C p
    m3' = LinearMap (tr u) ::  C b +> (C b ⊗ C p )

svdTallC :: forall (m :: Nat) (n :: Nat). (KnownNat m, KnownNat n, n <= m) => M m n -> (M m n, R n, M n n)
svdTallC (extract -> m) = (fromMaybe undefined $ create u, fromMaybe undefined $ create $ s, fromMaybe undefined $ create v)
  where
    (u,s,v) = H.thinSVD m

embedCenter
  :: MPS vp vb
  -> Center vp vb +> (C vp ⊗ C vp ⊗ C vp)
embedCenter psi =
  -- takes a variable center tensor
  -- contracts its left virtual leg with leftMPS
  -- contracts its right virtual leg with rightMPS
  -- exposes the three physical legs
  undefined

exampleMPS :: MPS 3 2
exampleMPS = MPS (LinearMap (konst 1)) (LinearMap (konst 1)) (LinearMap $ konst 2)