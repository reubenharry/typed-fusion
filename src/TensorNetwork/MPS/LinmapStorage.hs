{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Column-major assembly of static @'C'@ linear maps (mirrors @'R' n@ /
-- 'Numeric.LinearAlgebra.Static.Orphans' 'recomposeLinMap').
--
-- Production MPS paths use these helpers instead of 'recomposeLinMap', which
-- routes through tensor-domain 'uncurryLinearMap' and can disagree with
-- 'applyTensorLinMap' storage (@M codomain domain@).
module TensorNetwork.MPS.LinmapStorage
  ( colsToM
  , linMapFromColumnImages
  , envLinFromTensorImages
  , siteLinFromRows
  , siteDaggerLin
  , tensorCodomainLinFromFlatRows
  ) where

import Prelude
import GHC.TypeLits (KnownNat, type (*))
import Data.Maybe (fromMaybe)
import Unsafe.Coerce (unsafeCoerce)
import Math.LinearMap.Category (type (+>), type (⊗), LinearMap (..))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, M, Sized (create, fromList), extract)
import Math.VectorSpace.DimensionAware (toArray)
import qualified Data.Vector.Storable as VS
import qualified Numeric.LinearAlgebra.HMatrix as HM

-- | Assemble @M m n@ from @n@ column vectors of length @m@.
colsToM :: forall m n. (KnownNat m, KnownNat n) => [C m] -> M m n
colsToM cs =
  fromMaybe (error "colsToM") $
    create (HM.fromColumns (map extract cs))

-- | @C dom +> cod@ from domain-basis images stored as columns (@M cod dom@).
linMapFromColumnImages
  :: forall dom cod
   . (KnownNat dom, KnownNat cod)
  => [C cod] -> C dom +> C cod
linMapFromColumnImages imgs = LinearMap (colsToM @cod @dom imgs)

-- | Typed MPO environment @C a +> (C w ⊗ C b)@ from tensor basis images.
envLinFromTensorImages
  :: forall a w b
   . (KnownNat a, KnownNat w, KnownNat b, KnownNat (w * b))
  => [C w ⊗ C b] -> C a +> (C w ⊗ C b)
envLinFromTensorImages ts =
  let flats = [ fromList (VS.toList (toArray t)) | t <- ts ]
  in LinearMap (unsafeCoerce (colsToM @(w * b) @a flats))

-- | Site transfer map @(C bl ⊗ C p) +> C br@ ('siteMatrix' row order).
siteLinFromRows
  :: forall bl p br
   . (KnownNat bl, KnownNat p, KnownNat br, KnownNat (bl * p), KnownNat (p * br))
  => [C br] -> (C bl ⊗ C p) +> C br
siteLinFromRows rows =
  LinearMap (unsafeCoerce (colsToM @br @(bl * p) rows))

-- | Site dagger @C br +> (C bl ⊗ C p)@ from flat codomain images (@bl·p@ each).
siteDaggerLin
  :: forall bl p br
   . (KnownNat bl, KnownNat p, KnownNat br, KnownNat (bl * p), KnownNat (p * br))
  => [C (bl * p)] -> C br +> (C bl ⊗ C p)
siteDaggerLin flatImgs =
  LinearMap (unsafeCoerce (colsToM @(bl * p) @br flatImgs))

-- | @(C wl ⊗ C p) +> (C wr ⊗ C p)@ from flat tensor rows (@wr·p@ each).
tensorCodomainLinFromFlatRows
  :: forall wl p wr
   . (KnownNat wl, KnownNat p, KnownNat wr, KnownNat (wl * p), KnownNat (wr * p))
  => [C (wr * p)] -> (C wl ⊗ C p) +> (C wr ⊗ C p)
tensorCodomainLinFromFlatRows rows =
  LinearMap (unsafeCoerce (colsToM @(wr * p) @(wl * p) rows))
