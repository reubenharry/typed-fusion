
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{- HLINT ignore "Redundant $" -}

module Quantum (someFunc, hoppingHamiltonianTwoSite) where

import Control.Category.Constrained (id, (.))
import Math.LinearMap.Category (LinearMap(..), type (⊗), (⊕), InnerSpace ((<.>)), (<.>^), (<$|), euclideanNorm, Norm (Norm), Tensor (Tensor), DualVector, TensorSpace (TensorProduct), LinearSpace (..), VectorSpace (..), Scalar, AdditiveGroup (..), Semimanifold, type (+>), adjoint)
import Math.OrphanInstances ()
import Linear (V2 (V2), V3 (V3), E (..), V1 (V1))
import Data.Functor.Rep (tabulate, index)
import Control.Lens (Iso', (^.), _1, Ixed (ix), (^?))
import Math.VectorSpace.DimensionAware
import Data.Singletons (Sing, SingI (..), fromSing, sing)
import Data.Singletons.TH (genSingletons)
import TensorNetwork (TN, VP, VB, computeEnergy)
import qualified Test.QuickCheck as QC
import Prelude hiding ((||), ($), id, (.))
import Math.LinearMap.Asserted
import Data.Complex
import Math.LinearMap.Category.Backend.HMatrix (HMatrixImpl, asHMatrixImpl)
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static.Orphans ()
import Control.Arrow.Constrained (($), EnhancedCat (arr), Morphism ((***)))
import Data.Coerce (coerce)
import GHC.TypeLits (Nat, type (+), KnownNat, SNat, natVal)
import Linear.V (V, Finite (toV))
import Numeric.LinearAlgebra.Static (R(..), C, L, unrow, vector, M, Sized (fromList, unwrap, create, konst, extract), Domain (dvmap, mul))
import Data.Data (Proxy(..))
import Data.Kind (Type)
import qualified Data.Vector as ArB
import Numeric.LinearAlgebra.HMatrix (Vector, Matrix, Indexable ((!)))
import qualified Data.Vector.Generic as VG
import Data.Maybe (fromMaybe)
import qualified Numeric.LinearAlgebra.Static as LA
import qualified Numeric.LinearAlgebra.Static as G
import qualified Control.Category.Constrained as C
import Unsafe.Coerce (unsafeCoerce)
import Orphans
import Utils

-- todos 
-- tensors of representations 
-- make maps reifiable
-- get U(1) rep correct:
--- check that tensor product adds 
-- check that equivariance holds: i.e. try to find a definition that would violate it! first on 1 \otimes 1 -> 3 map
-- SU(2) reps
-- how to define an intertwiner between a direct sum of irreps? : 
  -- the sum of two irreps has a type which depends on if the irreps are equal


representationZ2 :: With (p :: Z2Irreps) -> Z2 -> IrrepZ2 p -+> IrrepZ2 p
representationZ2 p = case p of
  SOdd -> \case
    Flip -> LinearFunction negateV
    Id -> LinearFunction id
  SEven -> \case
    Flip -> LinearFunction id
    Id -> LinearFunction id

representationU1 :: forall p . Double -> IrrepU1 p -+> IrrepU1 p
representationU1 theta = LinearFunction $ \v -> scalar *^ v
  where
    -- n = natVal (Proxy @p)
    -- n' = fromIntegral n
    scalar = undefined
    -- scalar = exp ((0 :+ 1) * (theta * n' :+ 0))

-- check :: (IrrepZ2 Odd , IrrepZ2 Even) ⊗ IrrepZ2 Odd   -> (IrrepZ2 Odd ⊗ IrrepZ2 Odd , IrrepZ2 Even ⊗ IrrepZ2 Odd)
-- check = coerce

-- | Both factors are @C 1@-backed; fusion lands in @IrrepZ2 (N p q)@ via the same @M 1 1@ spine as @intertwinerU1@.
intertwinerZ2 ::
  forall (p :: Z2Irreps) (q :: Z2Irreps) n . (KnownNat n, n ~ Z2IrrepDim p, n ~ Z2IrrepDim q) =>
  With p -> With q -> (IrrepZ2 p ⊗ IrrepZ2 q) -+> IrrepZ2 (N p q)
intertwinerZ2 _ _ = LinearFunction $ \(Tensor l) ->
  IrrepZ2 (undefined ( l :: M n n))


intertwinerU1 :: forall p q . (IrrepU1 p ⊗ IrrepU1 q) -+> IrrepU1 (Add p q)
intertwinerU1 = LinearFunction \inp ->
  let Tensor (l) = inp
   in IrrepU1 (undefined l)

-- intertwinerSU2 :: forall i j i' j' i'' j'' . (KnownNat i, KnownNat j, KnownNat i', KnownNat j', KnownNat i'', KnownNat j'') => (IrrepSU2 i j ⊗ IrrepSU2 i' j') -+>  (With '(i'', j'') ->
--    ( SU2_N '(i, j) '(i', j') '(i'', j'') `X` IrrepSU2 i'' j''))
-- intertwinerSU2 = undefined
-- intertwinerU1' :: forall p q . (KnownNat p, KnownNat q) => ((IrrepU1 p ⊗ IrrepU1 q) -+> IrrepU1 (p + q))
-- intertwinerU1' = LinearFunction intertwinerU1



testProd = w ^+^ w
  where
    u :: V2 Double
    u = V2 1 2
    v :: V2 Double
    v = V2 3 4
    w :: V 2 (V2 Double)
    w = toV $ V2 u v

split :: forall p . (IrrepU1 p, IrrepU1 p) -+> (IrrepU1 p, IrrepU1 p)
split = (representationU1 @p 1 :: IrrepU1 p -+> IrrepU1 p) *** (representationU1 @p 1 :: IrrepU1 p -+> IrrepU1 p)


tensorRep :: forall p q . (IrrepU1 p ⊗ IrrepU1 q) -+> (IrrepU1 p ⊗ IrrepU1 q)
-- | Placeholder until the true tensor product of @representationU1@ on each factor is wired.
-- tensorRep :: (IrrepU1 (Pos 1) ⊗ IrrepU1 (Pos 1)) -+> (IrrepU1 (Pos 1) ⊗ IrrepU1 (Pos 1))
tensorRep = undefined -- (tensor' @p @p @q @q) (representationU1 @p 1) (representationU1 @q 1)

dir1 :: forall p q . (IrrepU1 p ⊗ IrrepU1 q) -+> IrrepU1 (Add p q)
dir1 = representationU1 @(Add p q) 1 . intertwinerU1 @p @q


-- main2 :: IO ()
-- main2 = print (arr (representationU1 1 :: (IrrepU1 (Pos 1)) -+> (IrrepU1 (Pos 1))) :: ((IrrepU1 (Pos 1)) +> (IrrepU1 (Pos 1))))

-- main3 :: IO ()
-- main3 = print (undefined :: IrrepU1 (Pos 1) +> IrrepU1 (Pos 1))

-- commutes :: forall {κ} {k :: κ -> κ -> Type} {b :: κ}. (C.Object k b, AdditiveGroup (k b b), C.Category k) => k b b -> k b b -> k b b
-- commutes :: (a -+> b) -> (b -+> a) -> (a -+> a)
-- commutes a b = a . b ^-^ b .a
-- sumRep

example = (representationZ2 SOdd Flip) $ val'  where
  val = konst 1 :: C 1
  val' = IrrepZ2 val

example2 :: (IrrepZ2 Odd , IrrepZ2 Even)
example2 = (IrrepZ2 (fromList [1]), IrrepZ2 (fromList [1]))

example3 :: (IrrepZ2 Odd, IrrepZ2 Even)
example3 = example2 ^+^ example2

example4 :: IrrepU1 (Pos 1)
example4 = representationU1 @(Pos 1) 1 $ IrrepU1 (konst 1)

example4' :: IrrepU1 (Pos 2)
example4' = representationU1 @(Pos 2) 1 $ (IrrepU1 (konst 1) :: IrrepU1 (Pos 2))

example5 :: forall p q . (IrrepU1 p ⊗ IrrepU1 q) -+> IrrepU1 (Add p q)
example5 = dir1 @p @q ^-^ dir1 @p @q

-- example6 :: Tensor (Complex Double) (IrrepU1 (Pos 1)) (IrrepU1 2)
-- example6 = tensorRep @1 @2 $ foo where
--   foo :: (IrrepU1 (Pos 1) ⊗ IrrepU1 2)
--   foo = Tensor $ undefined

example7 :: forall p q . (IrrepU1 p ⊗ IrrepU1 q)  -+>  IrrepU1 (Add p q)
example7 = intertwinerU1 @p @q . tensorRep @p @q


repThenNatTrans :: (IrrepU1 (Pos 1) ⊗ IrrepU1 (Pos 1))  +>  IrrepU1 (Add (Pos 1) (Pos 1))
repThenNatTrans = arr (example7 @(Pos 1) @(Pos 1))

natTransThenrep ::  (IrrepU1 (Pos 1) ⊗ IrrepU1 (Pos 1))  +>  IrrepU1 (Add (Pos 1) (Pos 1))
natTransThenrep = arr (representationU1 @(Pos 2) 1 . intertwinerU1 @(Pos 1) @(Pos 1))

example8 :: IrrepU1 (Pos 1) ⊗ IrrepU1 (Pos 2)
example8 = Tensor $ (IrrepU1 (konst 1))

example8' :: (IrrepU1 (Pos 1), IrrepU1 (Pos 2))
example8' = (IrrepU1 (konst 1), IrrepU1 (konst 1))

example9 :: (IrrepU1 (Pos 1) ⊗ IrrepU1 (Pos 2))  +>  IrrepU1 (Add (Pos 1) (Pos 2))
example9 = arr (intertwinerU1 @(Pos 1) @(Pos 2) . tensorRep @(Pos 1) @(Pos 2))

example10 :: (IrrepU1 (Pos 1) , IrrepU1 (Pos 1)) +> (IrrepU1 (Pos 1) , IrrepU1 (Pos 1))
example10 = arr (representationU1 @(Pos 1) 1 *** representationU1 @(Pos 1) 1)

example11 = print $ getLinearMap example10

example12 :: IrrepU1 (Add (Pos 1) (Pos 2))
example12 = example7 @(Pos 1) @(Pos 2) $ example8

example13 :: (IrrepU1 (Pos 1) ⊗ IrrepU1 (Pos 1))  +>  (IrrepU1 (Pos 1) ⊗ IrrepU1 (Pos 1))
example13 = arr (tensorRep @(Pos 1) @(Pos 1))

example14 :: ((IrrepU1 (Pos 1) +> IrrepU1 (Pos 1)), (IrrepU1 (Pos 1) +> IrrepU1 (Pos 1)))
example14 =  (adjoint $ arr  (representationU1 @(Pos 1) 1), arr  (representationU1 @(Pos 1) 1))




-- klebsch :: (s :: Sing Int) -> (s2 ::Sing Int )-> (IrrepZ2 s ⊗ IrrepZ2 s2 -> IrrepZ2 (Klebsch s s2))


-- data IntertwinerZ2 = IntertwinerZ2 (IrrepZ2_1 -> IrrepZ2_2)

-- comp :: V1 (Complex Double) ⊗ V1 (Complex Double)
-- comp = Tensor $ V1 undefined 

hMatrixVec :: HMatrixImpl (V2 Double ⊗ V2 Double)
hMatrixVec = asHMatrixImpl $ Tensor $ V2 (V2 1 2) (V2 3 4)

someFunc = undefined

shiftOperator :: LinearFunction Double (V3 Double) (V3 Double)
shiftOperator = LinearFunction $ \v -> let f = index v in tabulate (f . id)

tfoo :: E V2 -> Integer
tfoo = index (V2 1 2 )

g :: E V3 -> E V3
g (E e) = E (e . isom)

isom :: Iso' x x
isom = undefined -- iso (+1) (-1)

test20 :: Int
test20 = baz where
    foo = V2 1 2
    bar = dimensionalitySing @(V2 Double)
    baz = fromIntegral $ fromSing bar


type Field = Complex Double
type Ham vp = LinearMap Field (vp Field ⊗ vp Field) (vp Field ⊗ vp Field)

type Spin = V2 Field

-- | Nearest-neighbour hopping on two sites (one bond), with amplitude @-t@ between
-- product states @(0,1)@ and @(1,0)@ in the @'Tensor' ('V2' …)@ layout used elsewhere
-- here (outer @'V2'@ index is the first site). For more sites, tensor larger spaces
-- or use a tensor-network Hamiltonian; @'Ham' 'VP'@ is the two-site tensor factor.
hoppingHamiltonianTwoSite :: Field -> Ham VP
hoppingHamiltonianTwoSite t =
  arr $
    LinearFunction $
      \(Tensor (V2 (V2 _ a01) (V2 a10 _))) ->
        Tensor $ V2 (V2 0 (- (t * a10))) (V2 (- (t * a01)) 0)

-- let's minimize the energy of a single spin

-- norm :: Norm (V2 Field ⊗ V3 Field)
-- norm = Norm (LinearFunction $ \(Tensor x) -> ( arr (LinearFunction (\u -> ( undefined :: DualVector (V3 Field))))))

-- foobar :: TensorProduct (V3 Field) (V2 Field)
-- foobar = V3 (V2 undefined undefined) undefined undefined

-- main :: IO ()
-- main = do
--     -- tn <- QC.generate (QC.arbitrary @(TN VP VB))

--     -- tensor <- QC.generate (QC.arbitrary @(Tensor Double (VP Field) (VP Field)))
--     -- ham <- QC.generate (QC.arbitrary @(LinearMap Field (Tensor Field (VP Field) (VP Field)) (Tensor Field (VP Field) (VP Field))))

--     state <- QC.generate (QC.arbitrary @(V2 Double ⊗ V2 Double))
--     let ham = id
--         hstate = asHMatrixImpl $ state

--     let energy = (euclideanNorm <$| hstate) <.>^ ham hstate
--     print energy


    -- print (hMatrixVec <.> hMatrixVec)

