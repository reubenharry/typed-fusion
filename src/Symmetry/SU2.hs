{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | SU(2) group elements and irrep action (Wigner @D^j@).
--
-- Magnetic-index convention matches 'Symmetry.CG.SU2': @tj@ is twice the spin,
-- dimension @tj + 1@, and index @k = 0 .. tj@ is @tm = tj - 2k@ (highest weight
-- first). The defining representation (@tj = 1@) is left-multiplication by the
-- Cayley–Klein matrix @[[α, β], [-conj β, conj α]]@.
module Symmetry.SU2
  ( SU2Element
  , su2Alpha
  , su2Beta
  , su2Ident
  , su2CayleyKlein
  , su2FromQuaternion
  , su2Mul
  , su2Inv
  , applyWigner
  ) where

import Data.Complex (Complex (..), conjugate, magnitude)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import qualified Data.Vector.Storable as VS
import GHC.TypeLits (KnownNat, natVal)
import Numeric.LinearAlgebra.Static (C, Sized (create, extract))

-- | Cayley–Klein parameters: @[[α, β], [-conj β, conj α]]@ with
-- @|α|² + |β|² = 1@. Active rotations are @R_n(φ) = exp(-i φ n·σ / 2)@.
data SU2Element = SU2Element
  { su2Alpha :: !(Complex Double)
  , su2Beta  :: !(Complex Double)
  }
  deriving (Eq, Show)

-- | Identity: @α = 1@, @β = 0@.
su2Ident :: SU2Element
su2Ident = SU2Element 1 0

-- | Parse Cayley–Klein parameters, normalizing onto SU(2). @Nothing@ if both
-- entries vanish.
su2CayleyKlein :: Complex Double -> Complex Double -> Maybe SU2Element
su2CayleyKlein a b =
  let n2 = magnitude a * magnitude a + magnitude b * magnitude b
  in  if n2 < 1e-32
        then Nothing
        else
          let s = (1 / sqrt n2) :+ 0
          in  Just (SU2Element (s * a) (s * b))

-- | Unit quaternion @(w, x, y, z)@ on @S³ ≅ SU(2)@, corresponding to the
-- active rotation with @w = cos(φ/2)@ and @(x,y,z) = sin(φ/2) n@.
-- @Nothing@ if the quaternion is zero.
su2FromQuaternion :: Double -> Double -> Double -> Double -> Maybe SU2Element
su2FromQuaternion w x y z =
  let nrm = sqrt (w * w + x * x + y * y + z * z)
  in  if nrm < 1e-16
        then Nothing
        else
          let w' = w / nrm
              x' = x / nrm
              y' = y / nrm
              z' = z / nrm
              -- α = w − i z,  β = −y − i x
              α = w' :+ (-z')
              β = (-y') :+ (-x')
          in  Just (SU2Element α β)

-- | Group multiplication (matrix product of Cayley–Klein forms).
su2Mul :: SU2Element -> SU2Element -> SU2Element
su2Mul (SU2Element a1 b1) (SU2Element a2 b2) =
  SU2Element (a1 * a2 - b1 * conjugate b2) (a1 * b2 + b1 * conjugate a2)

-- | Inverse, equal to the adjoint on SU(2).
su2Inv :: SU2Element -> SU2Element
su2Inv (SU2Element a b) = SU2Element (conjugate a) (-b)

-- | Apply @D^{tj/2}(g)@ to a vector in the CG magnetic basis.
--
-- The static dimension @n@ must equal @tj + 1@.
applyWigner
  :: forall n. KnownNat n
  => Int
  -> SU2Element
  -> C n
  -> C n
applyWigner tj g v =
  let n = fromIntegral (natVal (Proxy @n))
      xs = VS.toList (extract v)
      ys = applyWignerList tj g xs
  in  if n /= tj + 1
        then error $
          "Symmetry.SU2.applyWigner: irrep dim " ++ show n
            ++ " ≠ tj+1 = " ++ show (tj + 1)
        else fromMaybe (error "Symmetry.SU2.applyWigner: static size mismatch")
          (create (VS.fromList ys))

applyWignerList :: Int -> SU2Element -> [Complex Double] -> [Complex Double]
applyWignerList tj g vin
  | length vin /= tj + 1 =
      error $
        "Symmetry.SU2.applyWigner: expected length "
          ++ show (tj + 1)
          ++ ", got "
          ++ show (length vin)
  | otherwise =
      let n = tj
          α = su2Alpha g
          β = su2Beta g
          αc = conjugate α
          βc = conjugate β
      in  [ sum [ wignerElem n α β αc βc k' k * (vin !! k) | k <- [0 .. n] ]
          | k' <- [0 .. n]
          ]

-- | Matrix element @⟨k'| D^{n/2} |k⟩@ in the highest-weight-first basis
-- (@k@ = number of downs). Derived from @U^{⊗ n}@ on the symmetric subspace,
-- so @tj = 1@ recovers the Cayley–Klein matrix.
wignerElem
  :: Int
  -> Complex Double
  -> Complex Double
  -> Complex Double
  -> Complex Double
  -> Int
  -> Int
  -> Complex Double
wignerElem n α β αc βc k' k =
  let rLo = max 0 (k' - k)
      rHi = min k' (n - k)
      pref = sqrt (binom n k / binom n k') :+ 0
      term r =
        (binom k (k' - r) * binom (n - k) r :+ 0)
          * cpow α (n - k - r)
          * cpow (-βc) r
          * cpow β (k - k' + r)
          * cpow αc (k' - r)
  in  pref * sum [ term r | r <- [rLo .. rHi] ]

cpow :: Complex Double -> Int -> Complex Double
cpow _ p | p < 0 = error "Symmetry.SU2.cpow: negative exponent"
cpow _ 0 = 1
cpow z p = z ^ p

-- | @C(n, k)@ as a 'Double' (exact for the small @tj@ used here).
binom :: Int -> Int -> Double
binom n k
  | n < 0 || k < 0 || k > n = 0
  | k == 0 || k == n = 1
  | otherwise =
      let k' = min k (n - k)
          go acc i
            | i > k' = acc
            | otherwise =
                go (acc * fromIntegral (n - k' + i) / fromIntegral i) (i + 1)
      in  go 1.0 1
