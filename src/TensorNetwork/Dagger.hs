{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Hilbert-space adjoint (†) for finite-dimensional complex spaces.
--
-- @dagger f@ is the conjugate transpose: 'conjugateMap' composed with
-- 'transposeMap' (categorical adjoint on self-dual spaces).
--
-- 'siteDagger' is the MPS-site bra pullback in transfer orientation. The
-- categorical definition flattens the tensor domain to a self-dual
-- 'ApplicationFlat' space (resolving @DualVector (bl ⊗ phys) ≠ bl ⊗ phys@ at
-- the type level), applies 'dagger', then unflattens:
--
-- @siteDagger f = isoInv ∘ dagger (f ∘ isoInv)@
--
-- The only type-specific hook is 'ApplicationTensorIso'.
module TensorNetwork.Dagger
  ( dagger
  , transposeMap
  , transposeMapSelfDual
  , hilbertFromDual
  , ApplicationTensorIso (..)
  , ApplicationFlat
  , ConjugateFlat (..)
  , SiteDaggerCtx
  , siteDagger
  , siteDaggerVec
  , conjugateCoefficients
  , siteTensorIso
  , siteTensorIsoInv
  , siteTensorIsoFlat
  ) where

import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import qualified Control.Functor.Constrained as CF
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (arr, ($))
import Math.LinearMap.Category
  ( type (-+>), type (+>), type (⊗), (⊗), adjoint, (-+$>), Tensor (..)
  , LinearFunction, pattern LinearFunction, LinearMap (LinearMap)
  , Scalar, TensorSpace, LinearSpace, DualVector, HilbertSpace
  , DualSpaceWitness (..), dualSpaceWitness
  , FiniteDimensional, uncanonicallyFromDual, Num'
  , TensorProduct, getTensorProduct )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList, unwrap, create), extract)
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Data.Maybe (fromJust)
import Data.Kind (Type)
import GHC.TypeLits (KnownNat, natVal, type (*))
import Data.Proxy (Proxy (..))
import Data.Complex (Complex, conjugate)
import Data.VectorSpace (VectorSpace ((*^)), sumV)
import qualified Data.Vector.Storable as VS
import TensorNetwork.Categorical
  ( conjugateMap, BoundaryUnit (..), lunitScalarLeg, lunitScalarLegInv
  , fuseBond, splitBond )
import qualified Numeric.LinearAlgebra.HMatrix as HM

type ℂ = Complex Double

-- | Identify a dual vector with its primal Hilbert representative.
hilbertFromDual
  :: forall v. (TensorSpace v, FiniteDimensional v) => DualVector v -+> v
hilbertFromDual = uncanonicallyFromDual

-- | Transpose on self-dual spaces (@DualVector v ~ v@, @DualVector w ~ w@) via
-- categorical 'adjoint'.
transposeMapSelfDual
  :: forall v w.
     ( LinearSpace v, LinearSpace w
     , DualVector v ~ v, DualVector w ~ w
     , Scalar v ~ ℂ, Scalar w ~ ℂ )
  => (v +> w) -> (w +> v)
transposeMapSelfDual f = case dualSpaceWitness @v of
  DualSpaceWitness -> (adjoint @v @w) -+$> f

-- | Transpose of @f : v +> w@. When @DualVector v ~ v@, use
-- 'transposeMapSelfDual'. Otherwise the domain needs a primal/dual identification
-- (in linearmap this comes from 'FiniteDimensional' via 'uncanonicallyFromDual';
-- not a constraint on abstract MPS operands — resolved from instances at @C n@).
transposeMap
  :: forall v w.
     ( LinearSpace v, FiniteDimensional v
     , LinearSpace w, DualVector w ~ w
     , Scalar v ~ ℂ, Scalar w ~ ℂ )
  => (v +> w) -> (w +> v)
transposeMap f = case dualSpaceWitness @v of
  DualSpaceWitness ->
    (CF.fmap (hilbertFromDual @v) Cat.. adjoint @v @w) -+$> f

-- | Conjugate transpose @f†@ of @f : v +> w@, for a self-dual codomain.
dagger
  :: forall v w.
     ( LinearSpace v, FiniteDimensional v
     , LinearSpace w, DualVector w ~ w
     , Scalar v ~ ℂ, Scalar w ~ ℂ )
  => (v +> w) -> (w +> v)
dagger f = transposeMap (conjugateMap f)

-- | Application-layout isomorphism @bl ⊗ phys ≅ flat@, where @flat@ is
-- self-dual (@DualVector flat ~ flat@). This is the small type hook that
-- resolves @DualVector (Tensor …)@ vs primal tensor types for 'siteDagger'.
class ApplicationTensorIso bl phys where
  type ApplicationFlat bl phys :: Type
  applicationTensorIso :: (bl ⊗ phys) +> ApplicationFlat bl phys
  applicationTensorIsoInv :: ApplicationFlat bl phys +> (bl ⊗ phys)

-- | Coefficient conjugation on flat application maps (bra pullback hook).
class ConjugateFlat flat br where
  conjugateFlatMap :: (flat +> br) -> (flat +> br)

-- | Constraints for categorical 'siteDagger'.
type SiteDaggerCtx bl br phys =
  ( ApplicationTensorIso bl phys
  , ConjugateFlat (ApplicationFlat bl phys) br
  , TensorSpace bl, TensorSpace phys, TensorSpace (bl ⊗ phys)
  , TensorSpace (ApplicationFlat bl phys)
  , LinearSpace (bl ⊗ phys), LinearSpace (ApplicationFlat bl phys)
  , HilbertSpace br
  , DualVector br ~ br, DualVector (ApplicationFlat bl phys) ~ ApplicationFlat bl phys
  , Scalar bl ~ ℂ, Scalar phys ~ ℂ, Scalar br ~ ℂ
  , Scalar (ApplicationFlat bl phys) ~ ℂ
  )

-- | Entry-wise complex conjugation on a static @C@ linear map (@M cod dom@).
conjugateCoefficients
  :: forall dom cod.
     (KnownNat dom, KnownNat cod)
  => (C dom +> C cod) -> (C dom +> C cod)
conjugateCoefficients (LinearMap m) =
  LinearMap (fromJust (create (HM.cmap conjugate (extract m))))

-- | MPS site bra pullback in transfer orientation:
-- @((bl ⊗ phys) +> br) ↦ (br +> (bl ⊗ phys))@.
--
-- Flatten to self-dual 'ApplicationFlat', apply transpose with coefficient
-- conjugation (bra pullback, not 'vectorConjugate' on Hom), unflatten.
siteDagger
  :: forall bl br phys.
     SiteDaggerCtx bl br phys
  => ((bl ⊗ phys) +> br) -> (br +> (bl ⊗ phys))
siteDagger f =
  applicationTensorIsoInv @bl @phys
    . transposeMapSelfDual
        (conjugateFlatMap @(ApplicationFlat bl phys) @br (f . applicationTensorIsoInv @bl @phys))

-- | Flatten @C bl ⊗ C p@ to @C (bl·p)@ (co-lex: index @l·p + s@).
siteTensorIsoFlat
  :: forall bl p.
     (KnownNat bl, KnownNat p, KnownNat (p * bl), p * bl ~ bl * p)
  => (C bl ⊗ C p) -> C (bl * p)
siteTensorIsoFlat (Tensor t) =
  let mat = extract t
      blI = fromIntegral $ natVal (Proxy @bl)
      pI  = fromIntegral $ natVal (Proxy @p)
  in unsafeFromArray @(C (bl * p)) $
       HM.fromList
         [ HM.atIndex mat (s, l) | l <- [0 .. blI - 1], s <- [0 .. pI - 1] ]

-- | Isomorphism @C bl ⊗ C p ≅ C (bl·p)@ (co-lex: index @l·p + s@).
siteTensorIso
  :: forall bl p.
     (KnownNat bl, KnownNat p, KnownNat (p * bl), p * bl ~ bl * p)
  => ((C bl ⊗ C p) +> C (bl * p))
siteTensorIso = applicationTensorIso @(C bl) @(C p)

-- | Inverse of 'siteTensorIso'.
siteTensorIsoInv
  :: forall bl p.
     (KnownNat bl, KnownNat p, KnownNat (p * bl), p * bl ~ bl * p)
  => (C (bl * p) +> (C bl ⊗ C p))
siteTensorIsoInv = applicationTensorIsoInv @(C bl) @(C p)

instance
  ( KnownNat bl, KnownNat p, KnownNat (p * bl), p * bl ~ bl * p
  ) =>
  ApplicationTensorIso (C bl) (C p)
  where
  type ApplicationFlat (C bl) (C p) = C (bl * p)
  applicationTensorIso = fuseBond @bl @p
  applicationTensorIsoInv = splitBond @bl @p @(C bl) @(C p) @(C (bl * p))

instance (KnownNat dom, KnownNat cod) => ConjugateFlat (C dom) (C cod) where
  conjugateFlatMap = conjugateCoefficients @dom @cod

instance KnownNat dom => ConjugateFlat (C dom) (Complex Double) where
  conjugateFlatMap = conjugateMap

instance ConjugateFlat (Complex Double) (Complex Double) where
  conjugateFlatMap = conjugateMap

instance
  ( BoundaryUnit (Complex Double), Num' (Complex Double)
  , LinearSpace v, TensorSpace v, TensorSpace (Complex Double ⊗ v)
  , Scalar v ~ Complex Double
  , TensorProduct (Complex Double) v ~ v
  ) =>
  ApplicationTensorIso (Complex Double) v
  where
  type ApplicationFlat (Complex Double) v = v
  applicationTensorIso = lunitScalarLeg @v
  applicationTensorIsoInv = lunitScalarLegInv @v

-- | Oracle: explicit basis pullback (for QuickCheck only — not production).
siteDaggerVec
  :: forall bl p br.
     ( KnownNat bl, KnownNat p, KnownNat br
     , KnownNat (bl * p), KnownNat (p * br), p * bl ~ bl * p )
  => ((C bl ⊗ C p) +> C br) -> C br -> (C bl ⊗ C p)
siteDaggerVec f w =
  sumV
    [ (unwrap w VS.! r) *^ pullbackAt r
    | r <- [0 .. br - 1]
    ]
  where
    bl = fromIntegral $ natVal (Proxy @bl)
    p  = fromIntegral $ natVal (Proxy @p)
    br = fromIntegral $ natVal (Proxy @br)
    pullbackAt r =
      sumV
        [ conjugate (siteEntry l s r) *^ (cBasis l ⊗ pBasis s)
        | l <- [0 .. bl - 1], s <- [0 .. p - 1]
        ]
    siteEntry l s r =
      unwrap (f $ (cBasis l ⊗ pBasis s)) VS.! r
    cBasis i = fromList [ if j == i then 1 else 0 | j <- [0 .. bl - 1] ]
    pBasis i = fromList [ if j == i then 1 else 0 | j <- [0 .. p - 1] ]
