{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Hilbert-space adjoint (†) for finite-dimensional complex spaces.
--
-- @dagger f@ is the conjugate transpose: 'conjugateMap' (entry-wise
-- 'vectorConjugate' on the map's own vector-space structure) composed with the
-- categorical 'adjoint' (transpose) and the dual→primal identification
-- 'hilbertFromDual'. Note † is /antilinear/, so it is exposed as a plain
-- function, not a @-+>@ morphism.
--
-- 'siteDagger' is the MPS-site special case: pullback in /application/
-- layout via column storage ('siteDaggerLin'), not 'recomposeLinMap'.
module TensorNetwork.Dagger
  ( dagger
  , transposeMap
  , hilbertFromDual
  , siteDagger
  , siteDaggerVec
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
  , LinearFunction, pattern LinearFunction
  , Scalar, TensorSpace, LinearSpace, DualVector
  , DualSpaceWitness (..), dualSpaceWitness
  , FiniteDimensional, uncanonicallyFromDual )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList, unwrap), M, extract, create)
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Data.Maybe (fromJust)
import Unsafe.Coerce (unsafeCoerce)
import TensorNetwork.MPS.LinmapStorage (siteDaggerLin)
import GHC.TypeLits (KnownNat, natVal, type (*))
import Data.Proxy (Proxy (..))
import Data.Complex (Complex, conjugate)
import Data.VectorSpace (VectorSpace ((*^)), sumV)
import qualified Data.Vector.Storable as VS
import TensorNetwork.Categorical (conjugateMap)
import qualified Numeric.LinearAlgebra.HMatrix as HM

-- | Identify a dual vector with its primal Hilbert representative.
hilbertFromDual
  :: forall v. (TensorSpace v, FiniteDimensional v) => DualVector v -+> v
hilbertFromDual = uncanonicallyFromDual

-- | Plain (unconjugated) transpose of @f : v +> w@, for a self-dual codomain.
transposeMap
  :: forall v w.
     ( LinearSpace v, FiniteDimensional v
     , LinearSpace w, DualVector w ~ w
     , Scalar v ~ Complex Double, Scalar w ~ Complex Double )
  => (v +> w) -> (w +> v)
transposeMap f = case dualSpaceWitness @v of
  DualSpaceWitness ->
    (CF.fmap (hilbertFromDual @v) Cat.. adjoint @v @w) -+$> f

-- | Conjugate transpose @f†@ of @f : v +> w@, for a self-dual codomain.
dagger
  :: forall v w.
     ( LinearSpace v, FiniteDimensional v
     , LinearSpace w, DualVector w ~ w
     , Scalar v ~ Complex Double, Scalar w ~ Complex Double )
  => (v +> w) -> (w +> v)
dagger f = transposeMap (conjugateMap f)

-- | Flatten @C bl ⊗ C p@ to @C (bl·p)@ (co-lex: index @l·p + s@).
siteTensorIsoFlat
  :: forall bl p.
     (KnownNat bl, KnownNat p, KnownNat (p * bl), p * bl ~ bl * p)
  => (C bl ⊗ C p) -> C (bl * p)
siteTensorIsoFlat (Tensor t) =
  let mat = extract (unsafeCoerce t :: M p bl)
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
siteTensorIso = arr $ LinearFunction siteTensorIsoFlat

-- | Inverse of 'siteTensorIso'.
siteTensorIsoInv
  :: forall bl p.
     (KnownNat bl, KnownNat p, KnownNat (p * bl), p * bl ~ bl * p)
  => (C (bl * p) +> (C bl ⊗ C p))
siteTensorIsoInv = arr $ LinearFunction $ \v ->
  let blI = fromIntegral $ natVal (Proxy @bl)
      pI  = fromIntegral $ natVal (Proxy @p)
      flat = HM.toList (extract v)
      cols = [ HM.fromList [ flat !! (l * pI + s) | l <- [0 .. blI - 1] ]
             | s <- [0 .. pI - 1] ]
  in Tensor (fromJust (create (HM.fromColumns cols)))

-- | MPS site †: column storage from pullback images ('siteDaggerVec').
siteDagger
  :: forall bl p br.
     ( KnownNat bl, KnownNat p, KnownNat br
     , KnownNat (bl * p), KnownNat (p * br), p * bl ~ bl * p )
  => ((C bl ⊗ C p) +> C br) -> (C br +> (C bl ⊗ C p))
siteDagger f =
  siteDaggerLin @bl @p @br
    [ fromList (VS.toList (toArray (siteDaggerVec f (cBasis r))))
    | r <- [0 .. br - 1] ]
  where
    br = fromIntegral $ natVal (Proxy @br)
    cBasis i = fromList [ if j == i then 1 else 0 | j <- [0 .. br - 1] ]

-- | Same pullback body, applied directly (diagnostic).
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
