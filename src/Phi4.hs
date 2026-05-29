{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Discrete @\\phi^4@ scalar field on a 1D lattice.
--
-- * __Kinetic term.__ On the site basis (one coordinate per vertex), nearest-neighbour
--   squared differences are exactly a quadratic form @\\phi \\mapsto \\langle \\phi, L\\phi\\rangle@
--   with @L@ the (positive semidefinite) 1D chain Laplacian — the same operator as the
--   continuum @\\int (\\nabla\\phi)^2@ after minimal coupling to the graph. That part is
--   basis-independent once the Hilbert space is fixed as @\\ell^2(V)@ on the vertex set @V@
--   with the usual inner product: @L@ is the unique self-adjoint operator whose quadratic
--   form is @\\sum_{\\{i,j\\}\\in E} (\\phi_i-\\phi_j)^2@ for our periodic \/ open conventions
--   (see 'phi4ChainLaplacian').
--
-- * __Potential.__ @\\sum_i V(\\phi_i)@ is local in the /site/ (vertex) basis: it is invariant
--   under permutations of sites only if @V@ is the same on every site, but it is not a
--   quadratic form and has no equally simple coordinate-free formula on @\\ell^2(V)@ alone.
module Phi4 (
    Phi4Params (..),
    defaultPhi4Params,
    -- * List-based API (site values in list order)
    phi4Energy,
    phi4KineticEnergy,
    phi4PotentialEnergy,
    phi4DoubleWellEnergy,
    -- * @V n@ + @linearmap-category@
    Phi4Config,
    phi4ChainLaplacian,
    phi4DotSites,
    phi4KineticEnergyLin,
    phi4PotentialEnergyLin,
    phi4EnergyLin,
    phi4DoubleWellEnergyLin,
    main,
) where

import Control.Applicative (liftA2)
import Data.AdditiveGroup (AdditiveGroup (..))
import Data.Foldable (foldl', toList)
import Data.Functor.Rep (index, tabulate)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownNat, Nat)
import GHC.TypeNats (natVal)
import Linear.V (V, Dim)
import Math.LinearMap.Asserted (linearFunction, getLinearFunction, type (-+>), (-+$>))
import Data.VectorSpace (AdditiveGroup (..), VectorSpace (..), InnerSpace ((<.>)))
import Math.OrphanInstances ()

-- | Field values on @n@ lattice sites, using the standard inner product on @'V' n 'Double'@.
type Phi4Config (n :: Nat) = V n Double

-- Site-valued fields as an @n@-tuple vector space (componentwise). Unlike @'Linear.V2'@–@'V4'@,
-- @'Linear.V.V' n@ has no @'VectorSpace'@ instance in @linearmap-category@ by default.
instance (KnownNat n, Dim n) => AdditiveGroup (V n Double) where
    zeroV = pure 0
    (^+^) = liftA2 (+)
    (^-^) = liftA2 (-)
    negateV = fmap negate

instance (KnownNat n, Dim n) => VectorSpace (V n Double) where
    type Scalar (V n Double) = Double
    μ *^ v = fmap (μ *) v

-- | Euclidean dot product @\\sum_i \\phi_i \\psi_i@ in the site basis (@'index'@-wise).
phi4DotSites :: forall n. (KnownNat n, Dim n) => Phi4Config n -> Phi4Config n -> Double
phi4DotSites u v =
    sum
        [ index u i * index v i
        | i <- [0 .. fromIntegral (natVal (Proxy @n)) - 1]
        ]

data Phi4Params = Phi4Params
    { kineticCoeff :: Double
    , massSquared :: Double
    , quartic :: Double
    , periodic :: Bool
    }
    deriving (Eq, Show)

defaultPhi4Params :: Phi4Params
defaultPhi4Params =
    Phi4Params
        { kineticCoeff = 1
        , massSquared = 1
        , quartic = 1
        , periodic = True
        }

-- | Graph Laplacian @L@ for the 1D open path or periodic ring, such that
-- @\\langle \\phi, L\\phi\\rangle = \\sum_{\\text{bonds}} (\\phi_i-\\phi_j)^2@ with the same
-- bonds as 'phi4KineticEnergy' on lists (including periodic @n=2@).
phi4ChainLaplacian ::
    forall n.
    (KnownNat n, Dim n, VectorSpace (Phi4Config n)) =>
    Bool ->
    Phi4Config n -+> Phi4Config n
phi4ChainLaplacian periodic =
    linearFunction $ \phi ->
        tabulate $ \i ->
            sum
                [ coeff i j * index phi j
                | j <- [0 .. nSites - 1]
                ]
  where
    nSites = fromIntegral (natVal (Proxy @n))
    coeff i j =
        if periodic
            then lapPeriodic nSites i j
            else lapOpen nSites i j

lapOpen :: Int -> Int -> Int -> Double
lapOpen n i j
    | n <= 1 = 0
    | i == j =
        if i == 0 || i == n - 1
            then 1
            else 2
    | abs (i - j) == 1 = -1
    | otherwise = 0

lapPeriodic :: Int -> Int -> Int -> Double
lapPeriodic n i j
    | n <= 1 = 0
    | i == j = 2
    | otherwise =
        let jp = (i + 1) `mod` n
            jm = (i - 1) `mod` n
         in if jp == jm
                then
                    if j == jp then -2 else 0
                else
                    if j == jp || j == jm then -1 else 0

phi4KineticEnergyLin ::
    forall n.
    (KnownNat n, Dim n, VectorSpace (V n Double)) =>
    Phi4Params ->
    Phi4Config n ->
    Double
phi4KineticEnergyLin Phi4Params{kineticCoeff, periodic} phi =
    -- kineticCoeff * realToFrac (phi <.> ((phi4ChainLaplacian periodic) -+$> phi))
    kineticCoeff * phi4DotSites phi (getLinearFunction (phi4ChainLaplacian periodic) phi)

phi4PotentialEnergyLin :: forall n. KnownNat n => Phi4Params -> Phi4Config n -> Double
phi4PotentialEnergyLin Phi4Params{massSquared, quartic} phi =
    foldl' (\acc x -> acc + localPotential massSquared quartic x) 0 phi
  where
    localPotential m2 lam x = 0.5 * m2 * x * x + 0.25 * lam * x * x * x * x

phi4EnergyLin ::
    forall n.
    (KnownNat n, Dim n, VectorSpace (V n Double)) =>
    Phi4Params ->
    Phi4Config n ->
    Double
phi4EnergyLin p phi = phi4KineticEnergyLin p phi + phi4PotentialEnergyLin p phi

phi4DoubleWellEnergyLin ::
    forall n.
    (KnownNat n, Dim n, VectorSpace (V n Double)) =>
    Double ->
    Double ->
    Bool ->
    Phi4Config n ->
    Double
phi4DoubleWellEnergyLin kappa lam isPeriodic phi =
    phi4KineticEnergyLin
        (Phi4Params{kineticCoeff = kappa, massSquared = 0, quartic = 0, periodic = isPeriodic})
        phi
        + lam * foldl' (\acc x -> acc + dw x) 0 phi
  where
    dw x = let p2 = x * x in (p2 - 1) * (p2 - 1)

-- | Full @\\phi^4@ energy (list = site basis in index order).
phi4Energy :: Phi4Params -> [Double] -> Double
phi4Energy p xs = phi4KineticEnergy p xs + phi4PotentialEnergy p xs

phi4KineticEnergy :: Phi4Params -> [Double] -> Double
phi4KineticEnergy Phi4Params{kineticCoeff, periodic} xs =
    kineticCoeff * case xs of
        [] -> 0
        [_] -> 0
        x0 : xsTail@(_ : _) ->
            sum (zipWith (\a b -> (a - b) ^ (2 :: Int)) xs xsTail)
                + if periodic
                    then (last xs - x0) ^ (2 :: Int)
                    else 0

phi4PotentialEnergy :: Phi4Params -> [Double] -> Double
phi4PotentialEnergy Phi4Params{massSquared, quartic} =
    sum . map (\phi -> 0.5 * massSquared * phi * phi + 0.25 * quartic * phi * phi * phi * phi)

phi4DoubleWellEnergy :: Double -> Double -> Bool -> [Double] -> Double
phi4DoubleWellEnergy kappa lam isPeriodic xs =
    phi4KineticEnergy
        (Phi4Params{kineticCoeff = kappa, massSquared = 0, quartic = 0, periodic = isPeriodic})
        xs
        + lam * sum (map (\phi -> let p2 = phi * phi in (p2 - 1) * (p2 - 1)) xs)

-- | Demo: @'phi4EnergyLin'@ on a periodic @n = 5@ ring (run from GHCi: @Phi4.main@).
main :: IO ()
main = do
    let phi :: Phi4Config 5
        phi = tabulate (\i -> 0.15 * fromIntegral i)
        p = defaultPhi4Params
        eKin = phi4KineticEnergyLin p phi
        ePot = phi4PotentialEnergyLin p phi
        eTot = phi4EnergyLin p phi
    putStrLn "Phi4 linear API demo (V 5, defaultPhi4Params):"
    putStrLn $ "  φ = " ++ show (toList phi)
    putStrLn $ "  phi4KineticEnergyLin   = " ++ show eKin
    putStrLn $ "  phi4PotentialEnergyLin = " ++ show ePot
    putStrLn $ "  phi4EnergyLin          = " ++ show eTot

