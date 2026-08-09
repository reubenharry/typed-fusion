{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | R-symbols as @IntertwinerG@ between @Tensor r q@ and @Tensor q r@.
--
-- Definition matching the forgetful braiding: @R = Fuse_{q,r} ∘ Swap ∘ Fuse_{r,q}†@.
--
-- * __U(1):__ coalesced spines coincide and fuse is charge-permutation; R is
--   @eye@ on multiplicity blocks (bosonic forgetful braiding).
-- * __SU(2):__ densify that conjugation against 'fuseSU2Flat', then pack Schur
--   blocks ('PackSchur'). Closed-form @(-1)^{j₁+j₂-j}@ on single channels is
--   equivalent; the dense path stays CG-coherent for general spines.
module Symmetry.CG.RSymbol
  ( rSymbolHomU1
  , rSymbolHomU1Inv
  , rSymbolHomSU2
  , rSymbolHomSU2Inv
  ) where

import Data.Complex (Complex (..))
import Data.Proxy (Proxy (..))
import qualified Data.Vector.Storable as VS
import qualified Numeric.LinearAlgebra as HM
import Symmetry.CG.FSymbol (BuildEyeHomG (..), PackSchur (..))
import Symmetry.CG.SU2 (fuseSU2Flat, repDimOf, sectorsSU2)
import Symmetry.FunctorExperiment (IntertwinerG (..))
import Symmetry.Group (Group (..), IntertwinerHom)
import Symmetry.RepSingleton (KnownRep (..), SRep)
import Symmetry.Tensor (Tensor)

type ℂ = Complex Double

--------------------------------------------------------------------------------
-- U(1)
--------------------------------------------------------------------------------

rSymbolHomU1
  :: forall r q.
     ( KnownRep U1 r, KnownRep U1 q
     , KnownRep U1 (Tensor U1 r q)
     , KnownRep U1 (Tensor U1 q r)
     , BuildEyeHomG U1
         (IntertwinerHom U1 (Tensor U1 r q) (Tensor U1 q r))
     )
  => Proxy r -> Proxy q
  -> IntertwinerG U1 (Tensor U1 r q) (Tensor U1 q r)
rSymbolHomU1 _ _ =
  MkIntertwiner
    (eyeHom @U1 @(IntertwinerHom U1 (Tensor U1 r q) (Tensor U1 q r)))

rSymbolHomU1Inv
  :: forall r q.
     ( KnownRep U1 r, KnownRep U1 q
     , KnownRep U1 (Tensor U1 r q)
     , KnownRep U1 (Tensor U1 q r)
     , BuildEyeHomG U1
         (IntertwinerHom U1 (Tensor U1 q r) (Tensor U1 r q))
     )
  => Proxy r -> Proxy q
  -> IntertwinerG U1 (Tensor U1 q r) (Tensor U1 r q)
rSymbolHomU1Inv _ _ =
  MkIntertwiner
    (eyeHom @U1 @(IntertwinerHom U1 (Tensor U1 q r) (Tensor U1 r q)))

--------------------------------------------------------------------------------
-- SU(2): dense Fuse ∘ Swap ∘ Fuse†
--------------------------------------------------------------------------------

-- | Swap factors in a second-factor-fastest product flat (@r⊗q → q⊗r@).
swapFlat :: Int -> Int -> VS.Vector ℂ -> VS.Vector ℂ
swapFlat dr dq v =
  VS.generate (dr * dq) $ \i' ->
    let iQ = i' `div` dr
        iR = i' `mod` dr
     in v VS.! (iR * dq + iQ)

matFromMap :: Int -> Int -> (VS.Vector ℂ -> VS.Vector ℂ) -> HM.Matrix ℂ
matFromMap _nRows nCols f =
  HM.fromColumns
    [ VS.convert (f (e i))
    | i <- [0 .. nCols - 1]
    ]
  where
    e i = VS.generate nCols $ \j -> if i == j then 1 else 0

-- | Dense R: @Tensor r q → Tensor q r@.
denseRMove
  :: SRep SU2 r -> SRep SU2 q
  -> SRep SU2 rq -> SRep SU2 qr
  -> HM.Matrix ℂ
denseRMove sr sq srq sqr =
  let dr = repDimOf (sectorsSU2 sr)
      dq = repDimOf (sectorsSU2 sq)
      dimP = dr * dq
      dimRQ = repDimOf (sectorsSU2 srq)
      dimQR = repDimOf (sectorsSU2 sqr)
      mRQ = matFromMap dimRQ dimP (fuseSU2Flat sr sq)
      mQR = matFromMap dimQR dimP (fuseSU2Flat sq sr . swapFlat dr dq)
   in mQR HM.<> HM.tr mRQ

rSymbolHomSU2
  :: forall r q.
     ( KnownRep SU2 r, KnownRep SU2 q
     , KnownRep SU2 (Tensor SU2 r q)
     , KnownRep SU2 (Tensor SU2 q r)
     , PackSchur
         (IntertwinerHom SU2 (Tensor SU2 r q) (Tensor SU2 q r))
     )
  => Proxy r -> Proxy q
  -> IntertwinerG SU2 (Tensor SU2 r q) (Tensor SU2 q r)
rSymbolHomSU2 _ _ =
  let sr = repSing @SU2 @r
      sq = repSing @SU2 @q
      srq = repSing @SU2 @(Tensor SU2 r q)
      sqr = repSing @SU2 @(Tensor SU2 q r)
      mat = denseRMove sr sq srq sqr
      hom =
        packSchur
          @(IntertwinerHom SU2 (Tensor SU2 r q) (Tensor SU2 q r))
          (sectorsSU2 srq)
          (sectorsSU2 sqr)
          mat
   in MkIntertwiner hom

rSymbolHomSU2Inv
  :: forall r q.
     ( KnownRep SU2 r, KnownRep SU2 q
     , KnownRep SU2 (Tensor SU2 r q)
     , KnownRep SU2 (Tensor SU2 q r)
     , PackSchur
         (IntertwinerHom SU2 (Tensor SU2 q r) (Tensor SU2 r q))
     )
  => Proxy r -> Proxy q
  -> IntertwinerG SU2 (Tensor SU2 q r) (Tensor SU2 r q)
rSymbolHomSU2Inv _ _ =
  let sr = repSing @SU2 @r
      sq = repSing @SU2 @q
      srq = repSing @SU2 @(Tensor SU2 r q)
      sqr = repSing @SU2 @(Tensor SU2 q r)
      mat = denseRMove sr sq srq sqr
      matInv = HM.tr mat
      hom =
        packSchur
          @(IntertwinerHom SU2 (Tensor SU2 q r) (Tensor SU2 r q))
          (sectorsSU2 sqr)
          (sectorsSU2 srq)
          matInv
   in MkIntertwiner hom
