
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
{-# OPTIONS_GHC -Wno-orphans #-}
{- HLINT ignore "Parenthesize unary negation" -}
{- HLINT ignore "Move brackets to avoid $" -}
{- HLINT ignore "Redundant $" -}

module TensorNetwork.DMRG.Concrete where

import Math.LinearMap.Category.Class
import Data.VectorSpace
import Control.Category.Constrained hiding (iso)
import Prelude hiding ((||), ($), id, (.))
import Math.LinearMap.Category (LinearFunction(..), adjoint, eigen, HilbertSpace, (·), Semimanifold(Needle), TensorDecomposable, RieszDecomposable, FiniteDimensional (..), SubBasis, constructEigenSystem, roughEigenSystem, Norm (Norm, applyNorm), Eigenvector (ev_Eigenvector, ev_Eigenvalue), euclideanNorm, pseudoInverse, (<$|), normSq, (|$|), riesz)
import GHC.TypeLits (Nat, KnownNat, type (*), type (<=), natVal)
import Linear.V (V)
import Linear (V2 (V2), V1 (V1), V3 (V3), E (..), V0 (V0))
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
import Data.Singletons (SingKind(..), Proxy (..))
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
import Numeric.LinearAlgebra.Static (toComplex)
import Data.Vector.Generic (replicateM)

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

-- checkConjugate = applyAntilinearFunction vectorConjugate (V1 (0 :+ 1) :: V1 Field)

type Field = Complex Double

type VP = V2
type VB = V3

-- data TN vp vb = TensorNetwork  {leftTN :: LinearMap Field (vp Field) (vb Field), rightTN :: LinearMap Field (vp Field) (vb Field)}
-- type Ham vp = LinearMap Field (vp Field ⊗ vp Field) (vp Field ⊗ vp Field)

getBasis = baz where

    bar :: V2 Field ⊗ V2 Field
    bar = Tensor $ V2 (V2 1 2) (V2 3 4)

    baz = decompose' bar (E _1, E _2)

-- ham :: Ham VP
-- ham = fst $ recomposeLinMap entireBasis [
--     undefined
--  ]

example :: Tensor Field (VP Field) (VP Field)
example = undefined

-- (||) :: forall f a b. (Function f, Object f a, Object f b) => f a b -> a -> b
-- (||) = ($)




-- -- converts a tensor network intox a tensor
-- tnToTensor :: TN VP VB -> (VP Field ⊗ VP Field)
-- tnToTensor (TensorNetwork a b) = coerce ((adjoint $ b) . a)


-- computeEnergy :: Ham VP -> TN VP VB -> Field
-- computeEnergy ham tn@(TensorNetwork a b) = m <.> (ham || m)
--     where m = tnToTensor tn

test :: Field
test = (0 :+ 1) <.> (0 :+ 1)

im = 0 :+ 1


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


-- derivedNorm :: V' -> DualSpace' V'
-- derivedNorm v = dagger v'  where
--     v' :: (Complex Double) -+> V'
--     v' = undefined


-- class Category k => DaggerCategory (k :: κ -> κ -> Type) where

--     dagger :: forall (v :: κ) (w :: κ). k v w -> k w v


-- instance DaggerCategory (LinearFunction s) where
--     dagger = undefined

-- norm :: Norm' V'
-- norm = undefined

-- coNorm :: CoNorm W'
-- coNorm = undefined

-- type DualSpace' v = v -+> Scalar v

-- newtype Norm' v = Norm' {
--     applyNorm' :: v -> DualSpace' v
-- }

-- newtype CoNorm v = CoNorm {
--   applyCoNorm :: DualSpace' v -+> v
-- }


-- monoidalproduct :: forall u u' v v' s. (TensorSpace u, TensorSpace u', TensorSpace v, TensorSpace v') => LinearMap s u v -> LinearMap s u' v' -> LinearMap s (u ⊗ u') (v ⊗ v')
-- monoidalunit :: LinearMap Field (VP Field) (VB Field) -> LinearMap Field (VP Field ⊗ VB Field) (VP Field ⊗ VP Field)
-- monoidalunit l1 = undefined where

--     l1' :: VP Field ⊗ VB Field
--     l1' = coerce l1


--     l3 :: VP Field ⊗ (VP Field ⊗ VB Field) ⊗ VP Field
--     l3 = undefined ⊗ undefined

--     foo :: TensorProduct (VP Field ⊗ VB Field) (VP Field ⊗ VP Field)
--     foo = coerce bar

--     bar :: TensorProduct (DualVector (VP Field ⊗ VB Field)) (VP Field ⊗ VP Field)
--     bar = undefined
--     -- foo :: LinearFunction Field (VP Field ⊗ VP Field) (VP Field ⊗ VP Field)
--     -- foo = getLinearFunction fmapTensor (arr ex1 :: LinearFunction Field (VP Field) (VP Field))

mat :: (V2 Field ⊗ V2 Field) +> (V2 Field ⊗ V2 Field)
mat = undefined -- LinearMap $ (V2 (V2 (1 :+ 2) (3 :+ 4)) (V2 (5 :+ 6) (7 :+ 8)))

mat2 :: VP Field +> VP Field
mat2 = LinearMap $ (V2 (V2 (1 :+ 2) (3 :+ 4)) (V2 (5 :+ 6) (7 :+ 8)))


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
-- eigenDecomp = eigen euclideanNorm matreal


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

-- drmg :: Ham VP -> TN VP VB -> TN VP VB
-- drmg ham(TensorNetwork a b) = undefined
--     where
--         m :: LinearMap Field (VP Field ⊗ VB Field) (VP Field ⊗ VP Field)
--         m = arr $ fmapTensor $ arr $ adjoint $ a

--         heff :: (VP Field ⊗ VB Field) +> (VP Field ⊗ VB Field)
--         heff = adjointF m . ham . m

--         adj' :: (DualVector ((VP Field ⊗ VP Field))) +> (DualVector ((VP Field ⊗ VB Field)))
--         adj' = (adjoint $ m)

--         eigenvals :: [(Field, VP Field ⊗ VB Field)]
--         eigenvals = eigen euclideanNorm heff

--         newA :: (VP Field ⊗ VB Field)
--         newA = snd $ minimumBy (comparing $ C.magnitude . fst) eigenvals

data MPS vp vb = MPS {
    -- leftMPS :: (C vb) +> (C vp),
    -- rightMPS :: (C vb) +> (C vp),
    -- center :: (C vb) +> (C vb ⊗  C vp )} 
    leftMPS :: C vp +> C vb,
    centerMPS :: (C vb ⊗ C vp) +> C vb,
    rightMPS :: (C vb ⊗ C vp) +> C 1
}

-- instance (KnownNat vb, KnownNat (vb*vp)) => Show (MPS vp vb) where
--     show = show . getLinearMap . center

-- instance HasBasis (C n) where



data MPO vp vb = MPO {
    leftMPO :: C vp +> (C vb ⊗ C vp),
    centerMPO :: (C vb ⊗ C vp) +> (C vb ⊗ C vp ),
    rightMPO :: (C vb ⊗ C vp) +> C vp
    }


compoGeneral :: forall va vb vc vd. (HilbertSpace va, HilbertSpace vb, HilbertSpace vc, HilbertSpace vd, Scalar va ~ Scalar vb, Scalar vb ~ Scalar vc, Scalar vc ~ Scalar vd) => (va +> (vb ⊗ vc)) -> (vc +> vd) -> (va +> (vb ⊗ vd))
compoGeneral (LinearMap f) g = c' where
    -- h = coerce g :: (DualVector ( (va) ⊗ vb)) ⊗ C c

    h'' :: (va ⊗ vb) +> vc
    h'' = coerce f
    c :: (va ⊗ vb) +> vd
    c = g . h''
    c' :: (va +> (vb ⊗ vd))
    c' = coerce c

compo' :: (C a +> (C b ⊗ C c)) -> (C b +> C d) -> (C a +> (C d ⊗ C c))
compo' f g = undefined

precompoGeneral :: forall va vb vc vd. (HilbertSpace va, HilbertSpace vb, HilbertSpace vc, HilbertSpace vd, Scalar va ~ Scalar vb, Scalar vb ~ Scalar vc, Scalar vc ~ Scalar vd) => ((va ⊗ vb) +> vc) -> (vd +> va) -> ((vd ⊗ vb) +> vc)
precompoGeneral f g = coerce c where
    h'' :: va +> (vb ⊗ vc)
    h'' = coerce f
    c :: vd +> (vb ⊗ vc)
    c = h'' . g


type Center vp vb = (C vb ⊗ C vp) +> C vb

solveAtSite :: forall p b. (KnownNat p, KnownNat b) => MPO p b -> MPS p b -> MPS p b
solveAtSite ham@(MPO leftMPO centerMPO rightMPO) mps@(MPS leftMPS centerMPS rightMPS) =  MPS leftMPS minimal rightMPS
    where
        -- m :: (C vb +> (C vb ⊗ C vp)) +> (C p ⊗ C p ⊗ C p )
        -- m = undefined 

        j1 :: C p +> (C b ⊗ C b)
        j1 = compoGeneral leftMPO leftMPS

        j2 :: C b +> (C b ⊗ C b)
        j2 = j1 . adjointF leftMPS

        j1r :: (C b ⊗ C p ⊗ C b) +> C 1
        j1r = undefined

        j2r :: (C b ⊗ C b ⊗ C b) +> C 1
        j2r = undefined

        withMiddle :: (C b ⊗ C p) +> (C b ⊗ (C b ⊗ C p))
        withMiddle = undefined

        j3 :: ((C b ⊗ C p) ⊗ C b) +> ((C b ⊗ C p) ⊗ C b)
        j3 = undefined

        j3' :: ((C b ⊗ C p) +> C b) +> ((C b ⊗ C p) +> C b)
        j3' = coerce j3

        heff :: Center p b +> Center p b
        heff = j3'
        -- heff = adjointF m . ham . m

        eigenvals :: [(Field, Center p b)]
        eigenvals = eigen euclideanNorm heff

        minimal :: (Center p b)
        minimal = snd $ minimumBy (comparing $ C.magnitude . fst) eigenvals

move :: forall p b. (KnownNat p, KnownNat b, KnownNat (b * p), KnownNat (p * b), KnownNat (p * (b * p)), b <= p*b) => MPS p b -> MPS p b
move (MPS leftMPS (LinearMap centerMPS) rightMPS) = MPS {
    leftMPS = leftMPS,
    rightMPS = precompoGeneral rightMPS foo,
    centerMPS = LinearMap $ tr u
} where
    (u,s,v) = svdTallC ( tr centerMPS :: M  (p*b) b)
    ch = LinearMap (diagR 0 (complex s) :: M b b) :: C b +> C b
    -- foo = m2 . ch .  LinearMap  (tr v)
    foo = ch .  LinearMap  (tr v) :: C b +> C b
    -- foo = centerMPS


svdTallC :: forall (m :: Nat) (n :: Nat). (KnownNat m, KnownNat n, n <= m) => M m n -> (M m n, R n, M n n)
svdTallC (extract -> m) = (fromMaybe undefined $ create u, fromMaybe undefined $ create $ s, fromMaybe undefined $ create v)
  where
    (u,s,v) = H.thinSVD m





-- dagger :: (KnownNat n, KnownNat m) => (C n +> C m) -> (C m +> C n)
-- dagger :: Transposable   (TensorProduct (DualVector v1) w1)   (TensorProduct (DualVector v2) w2) => LinearMap s1 v1 w1 -> LinearMap s2 v2 w2
dagger (LinearMap f) = LinearMap $ tr f 

mpsInnerProduct :: forall p b. (KnownNat p, KnownNat b, KnownNat (p * b)) => MPS p b -> MPS p b -> Field
mpsInnerProduct (MPS leftMPS centerMPS rightMPS) (MPS leftMPS' centerMPS' rightMPS') = undefined where

    dualLeftMPS' = adjointF leftMPS' :: C b +> C p
    --    dualCenterMPS' = (tr $ getLinearMap centerMPS') :: M (p * b) b
    -- dualCenterMPS' = (tr $ getLinearMap centerMPS') :: M (p * b) b
    dualCenterMPS' = (adjointF centerMPS') :: (C b) +> (C b ⊗ C p)

    baz = getLinearMap (undefined :: C b +> (C p ⊗ C b)) :: M  b (p * b)

    bar = getLinearMap leftMPS :: M p b

    j1 = leftMPS . dualLeftMPS'


    -- j2 :: (C b ⊗ C p)
    -- j2 = adjointF centerMPS' . adjointF j1

    -- j3 
    

main :: IO ()
main = do
    -- mps <- QC.generate (QC.arbitrary @(MPS 3 2))
    let mps = MPS (LinearMap $ konst 1 :: C 3 +> C 2) (LinearMap $ konst 1 :: (C 2 ⊗ C 3) +> C 2) (LinearMap $ konst 1 :: (C 2 ⊗ C 3) +> C 1) :: MPS 3 2
    -- print (getLinearMap (leftMPS mps))
    let LinearMap l = leftMPS mps
    -- let a = decompose' l (E _1, E _2)
    
    print l



testNum = undefined where
    a :: C 3 -+> C 2
    a = undefined
    a' :: C 3 ⊗ C 2
    a' = undefined
    b :: C 3
    b = konst 1
    c = a $ b
    d = first a :: (C 3, C 1) -+> (C 2, C 1)
    -- e = decompose' a' (undefined, undefined)

-- exampleMPS :: MPS 3 2
-- exampleMPS = (MPS (LinearMap (konst 1)) (LinearMap (konst 1)) (LinearMap $ konst 2))

-- exampleMPS' :: MPS 3 2
-- exampleMPS' = move exampleMPS