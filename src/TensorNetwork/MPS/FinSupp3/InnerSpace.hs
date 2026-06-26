{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Sesquilinear 'InnerSpace' for complex 'FinSuppSeq' bonds.
--
-- The generic 'free-vector-spaces' instance is bilinear even for complex
-- entries; this orphan matches 'Numeric.LinearAlgebra.Static.COrphans' and
-- the DMRG convention (bra conjugation via 'dagger' / 'vectorConjugate', not
-- via a bilinear bond '<.>').
module TensorNetwork.MPS.FinSupp3.InnerSpace
  ( bondToC
  ) where

import Data.Complex (Complex, conjugate)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (InnerSpace ((<.>)))
import Data.VectorSpace.Free.FiniteSupportedSequence (FinSuppSeq (..))
import GHC.TypeLits (KnownNat, natVal)
import Numeric.LinearAlgebra.Static (C, Sized (create))
import Numeric.LinearAlgebra.Static.COrphans ()
import qualified Data.Vector.Unboxed as U
import qualified Numeric.LinearAlgebra as LA

type Field = Complex Double
type Bond = FinSuppSeq Field

finsuppInner :: U.Vector Field -> U.Vector Field -> Field
finsuppInner u v =
  go 0 0
  where
    lu = U.length u
    lv = U.length v
    go i acc
      | i >= lu && i >= lv = acc
      | otherwise =
          let ui = if i < lu then u U.! i else 0
              vi = if i < lv then v U.! i else 0
          in go (i + 1) (acc + conjugate ui * vi)

instance InnerSpace Bond where
  FinSuppSeq u <.> FinSuppSeq v = finsuppInner u v

-- | Embed a bond vector into @C n@ (zero-padded); @n@ must cover active support.
bondToC :: forall n. KnownNat n => Bond -> C n
bondToC (FinSuppSeq v) =
  fromMaybe (error "bondToC: dimension too small for bond support") $
    create (LA.fromList (padTo dim (U.toList v)))
  where
    dim = fromIntegral (natVal (Proxy @n))
    padTo k xs = xs ++ replicate (max 0 (k - length xs)) 0
