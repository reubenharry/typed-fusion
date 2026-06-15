{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Categorical three-site MPS/MPO algebra over abstract 'LinearSpace' operands.
--
-- Unlike 'TensorNetwork.MPS.Fixed3', this module never uses 'C n', 'unwrap',
-- or list-comprehension matmul. Coefficients are read only through the
-- finite-dimensional basis API ('enumerateSubBasis', '<.>', 'recomposeLinMap').
-- Explicit basis sums live in 'TensorNetwork.MPS.Fixed3.Reference' only.
module TensorNetwork.MPS.Fixed3General
  -- ( Site (..)
  -- , MPS (..)
  -- , OpSite (..)
  -- , MPO (..)
  --   -- * Site maps
  -- , applySite
  -- , applyOpSite
  -- , oneUnit
  --   -- * Physical state
  -- , mpsStateMap
  -- , mpsToTensor
  --   -- * Hilbert structure
  -- , conjugateSite
  -- , mpsConjugate
  -- , transferStep
  -- , mpsInner
  -- , mpsNorm
  --   -- * MPO expectations
  -- , mpoTransferStep
  -- , mpsMPOInner
  -- , identityMPO
  -- , mpoApplyMPS
  --   -- * Bridge + tests
  -- , toFixedMPS
  -- , genSiteV2
  -- , genMPSV222
  -- , prop_generalInnerConjugateSymmetric
  -- , prop_generalNormNonNegative
  -- , prop_generalInnerMatchesFixed3Reference
  -- ) where
where

import Prelude hiding (($))
import qualified Control.Category.Constrained as Cat
import Control.Arrow.Constrained (($))
import Data.Complex (Complex, conjugate, realPart, imagPart)
import Data.VectorSpace (InnerSpace ((<.>)), Scalar, (*^), sumV)
import Math.LinearMap.Asserted (AntilinearFunction (..))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗)
  , Tensor (..)
  , FiniteDimensional (..), SubBasis, entireBasis
  , TensorSpace, HilbertSpace
  , vectorConjugate, getAntilinearFunction
  , enumerateSubBasis, recomposeLinMap )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Instances.Deriving ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import TensorNetwork.MPS.Fixed3 ()
import qualified TensorNetwork.MPS.Fixed3 as F3
import qualified TensorNetwork.MPS.Fixed3.Internal as F3 (Site (..), MPS (..))
import Linear.V (V)
import GHC.TypeLits (KnownNat)
import Control.Monad (replicateM)
import qualified Test.QuickCheck as QC

-- type Field = Complex Double
-- type Unit = V 1

-- --------------------------------------------------------------------------------
-- -- Types
-- --------------------------------------------------------------------------------

-- data Site bondL phys bondR = Site
--   { siteLin :: (bondL ⊗ phys) +> bondR }
--   deriving (Show)

-- data MPS bond1 phys bond2 = MPS
--   { siteL :: Site Unit phys bond1
--   , siteC :: Site bond1 phys bond2
--   , siteR :: Site bond2 phys Unit
--   }
--   deriving (Show)

-- data OpSite bondL phys bondR = OpSite
--   { opSiteLin :: (bondL ⊗ phys) +> (bondR ⊗ phys) }
--   deriving (Show)

-- data MPO w1 phys w2 = MPO
--   { opL :: OpSite Unit phys w1
--   , opC :: OpSite w1 phys w2
--   , opR :: OpSite w2 phys Unit
--   }
--   deriving (Show)

--------------------------------------------------------------------------------
-- Basis helpers
--------------------------------------------------------------------------------

-- basisList :: forall v. FiniteDimensional v => [v]
-- basisList = enumerateSubBasis (entireBasis :: SubBasis v)

-- basisAt :: forall v. FiniteDimensional v => Int -> v
-- basisAt i = basisList @v !! i

-- dim :: forall v. FiniteDimensional v => Int
-- dim = length (basisList @v)

-- tensorBasisPairs :: (FiniteDimensional u, FiniteDimensional v) => [u ⊗ v]
-- tensorBasisPairs =
--   [ u ⊗ v | u <- basisList @u, v <- basisList @v ]

-- conjugateVec :: HilbertSpace v => v -> v
-- conjugateVec = applyAntilinearFunction (AntilinearFunction vectorConjugate)

-- oneUnit :: Unit
-- oneUnit = basisAt @Unit 0

-- scalarCoeff :: (HilbertSpace v, Scalar v ~ Field) => v -> v -> Field
-- scalarCoeff u w = u <.> w

-- --------------------------------------------------------------------------------
-- -- Site application
-- --------------------------------------------------------------------------------

-- applySite
--   :: ( TensorSpace bondL, TensorSpace phys, TensorSpace bondR
--      , Scalar bondL ~ Field, Scalar phys ~ Field, Scalar bondR ~ Field )
--   => Site bondL phys bondR -> bondL -> phys -> bondR
-- applySite (Site f) bond s = f $ (bond ⊗ s)

-- applyOpSite
--   :: ( TensorSpace bondL, TensorSpace phys, TensorSpace bondR
--      , FiniteDimensional bondR, FiniteDimensional phys
--      , HilbertSpace bondR, HilbertSpace phys
--      , Scalar bondL ~ Field, Scalar phys ~ Field, Scalar bondR ~ Field )
--   => OpSite bondL phys bondR -> bondL -> phys -> phys -> bondR
-- applyOpSite (OpSite f) bond sIn sOut =
--   sumV
--     [ scalarCoeff (basisAt @bondR r ⊗ basisAt @phys sOut) applied *^ basisAt @bondR r
--     | r <- [0 .. dim @bondR - 1] ]
--   where
--     applied :: bondR ⊗ phys = f $ (bond ⊗ sIn)

-- --------------------------------------------------------------------------------
-- -- Physical state map
-- --------------------------------------------------------------------------------

-- centerRightSlice
--   :: ( TensorSpace bond1, TensorSpace phys, TensorSpace bond2
--      , FiniteDimensional phys, Scalar bond1 ~ Field, Scalar phys ~ Field
--      , Scalar bond2 ~ Field )
--   => Site bond1 phys bond2 -> Site bond2 phys Unit -> bond1 -> phys ⊗ phys
-- centerRightSlice center right bond =
--   Tensor (map (\s2 -> applySite right (applySite center bond s2)) (basisList @phys))

-- mpsStateMap
--   :: ( TensorSpace bond1, TensorSpace phys, TensorSpace bond2
--      , FiniteDimensional phys, FiniteDimensional bond1
--      , FiniteDimensional (phys ⊗ phys)
--      , HilbertSpace phys, Scalar bond1 ~ Field, Scalar phys ~ Field
--      , Scalar bond2 ~ Field )
--   => MPS bond1 phys bond2 -> phys +> (phys ⊗ phys)
-- mpsStateMap (MPS l c r) =
--   fst $
--     recomposeLinMap (entireBasis :: SubBasis phys)
--       [ centerRightSlice c r (applySite l oneUnit s1) | s1 <- basisList @phys ]

-- mpsToTensor
--   :: ( TensorSpace bond1, TensorSpace phys, TensorSpace bond2
--      , FiniteDimensional phys, FiniteDimensional bond1
--      , FiniteDimensional (phys ⊗ phys)
--      , HilbertSpace phys, Scalar bond1 ~ Field, Scalar phys ~ Field
--      , Scalar bond2 ~ Field )
--   => MPS bond1 phys bond2 -> phys ⊗ (phys ⊗ phys)
-- mpsToTensor mps =
--   sumV
--     [ scalarCoeff (basisAt @phys s1) (mpsStateMap mps $ basisAt @phys s1)
--         *^ (basisAt @phys s1 ⊗ mpsStateMap mps $ basisAt @phys s1)
--     | s1 <- basisList @phys ]

-- --------------------------------------------------------------------------------
-- -- Conjugation and MPS inner product
-- --------------------------------------------------------------------------------

-- conjugateSite
--   :: ( TensorSpace bondL, TensorSpace phys, TensorSpace bondR
--      , FiniteDimensional bondL, FiniteDimensional phys, FiniteDimensional bondR
--      , HilbertSpace bondL, HilbertSpace phys, HilbertSpace bondR
--      , Scalar bondL ~ Field, Scalar phys ~ Field, Scalar bondR ~ Field )
--   => Site bondL phys bondR -> Site bondL phys bondR
-- conjugateSite (Site f) =
--   Site $
--     fst $
--       recomposeLinMap (entireBasis :: SubBasis (bondL ⊗ phys))
--         [ conjugateVec (f $ xy) | xy <- tensorBasisPairs @bondL @phys ]

-- mpsConjugate
--   :: ( TensorSpace bond1, TensorSpace phys, TensorSpace bond2
--      , FiniteDimensional bond1, FiniteDimensional phys, FiniteDimensional bond2
--      , HilbertSpace bond1, HilbertSpace phys, HilbertSpace bond2
--      , Scalar bond1 ~ Field, Scalar phys ~ Field, Scalar bond2 ~ Field )
--   => MPS bond1 phys bond2 -> MPS bond1 phys bond2
-- mpsConjugate (MPS l c r) =
--   MPS (conjugateSite l) (conjugateSite c) (conjugateSite r)

-- transferCoeff
--   :: ( TensorSpace bondL, TensorSpace phys, TensorSpace bondR
--      , FiniteDimensional bondL, FiniteDimensional phys, FiniteDimensional bondR
--      , HilbertSpace bondL, HilbertSpace phys, HilbertSpace bondR
--      , Scalar bondL ~ Field, Scalar phys ~ Field, Scalar bondR ~ Field )
--   => Site bondL phys bondR -> Site bondL phys bondR -> (bondL +> bondL)
--   -> Int -> Int -> Field
-- transferCoeff bra ket env rOut rIn =
--   sumV
--     [ scalarCoeff (basisAt @bondR rOut) (applySite bra l s)
--         *^ (scalarCoeff l' (env $ l) *^ scalarCoeff (basisAt @bondR rIn) (applySite ket l' s))
--     | l <- basisList @bondL
--     , l' <- basisList @bondL
--     , s <- basisList @phys ]

-- transferStep
--   :: ( TensorSpace bondL, TensorSpace phys, TensorSpace bondR
--      , FiniteDimensional bondL, FiniteDimensional phys, FiniteDimensional bondR
--      , HilbertSpace bondL, HilbertSpace phys, HilbertSpace bondR
--      , Scalar bondL ~ Field, Scalar phys ~ Field, Scalar bondR ~ Field )
--   => Site bondL phys bondR -> Site bondL phys bondR -> (bondL +> bondL) -> (bondR +> bondR)
-- transferStep bra ket env =
--   fst $
--     recomposeLinMap (entireBasis :: SubBasis bondR)
--       [ sumV
--           [ transferCoeff bra ket env rOut rIn *^ basisAt @bondR rOut
--           | rOut <- [0 .. dim @bondR - 1] ]
--       | rIn <- [0 .. dim @bondR - 1] ]

-- mpsInner
--   :: ( TensorSpace bond1, TensorSpace bond2, TensorSpace phys
--      , FiniteDimensional bond1, FiniteDimensional bond2, FiniteDimensional phys
--      , HilbertSpace bond1, HilbertSpace bond2, HilbertSpace phys
--      , Scalar bond1 ~ Field, Scalar phys ~ Field, Scalar bond2 ~ Field )
--   => MPS bond1 phys bond2 -> MPS bond1 phys bond2 -> Field
-- mpsInner psi phi =
--   scalarCoeff oneUnit $
--     transferStep (siteR bra) (siteR ket) $
--       transferStep (siteC bra) (siteC ket) $
--         transferStep (siteL bra) (siteL ket) Cat.id
--         $ oneUnit
--   where
--     bra = mpsConjugate psi
--     ket = phi

-- mpsNorm
--   :: ( TensorSpace bond1, TensorSpace bond2, TensorSpace phys
--      , FiniteDimensional bond1, FiniteDimensional bond2, FiniteDimensional phys
--      , HilbertSpace bond1, HilbertSpace phys, HilbertSpace bond2
--      , Scalar bond1 ~ Field, Scalar phys ~ Field, Scalar bond2 ~ Field )
--   => MPS bond1 phys bond2 -> Double
-- mpsNorm psi = sqrt (realPart (mpsInner psi psi))

-- --------------------------------------------------------------------------------
-- -- Nested bond spaces for MPO transfer
-- --------------------------------------------------------------------------------

-- type Bond3 bondM bondB bondK = bondM ⊗ (bondB ⊗ bondK)

-- bond3Basis :: (FiniteDimensional bondM, FiniteDimensional bondB, FiniteDimensional bondK)
--   => Int -> Int -> Int -> Bond3 bondM bondB bondK
-- bond3Basis iW iB iK = basisAt @bondM iW ⊗ (basisAt @bondB iB ⊗ basisAt @bondK iK)

-- bond3Split
--   :: (FiniteDimensional bondM, FiniteDimensional bondB, FiniteDimensional bondK)
--   => Int -> (Int, Int, Int)
-- bond3Split idx =
--   let nBK = dim @bondK
--       nB = dim @bondB
--       stride = nBK * nB
--       iW = idx `div` stride
--       rem1 = idx `mod` stride
--       iB = rem1 `div` nBK
--       iK = rem1 `mod` nBK
--   in (iW, iB, iK)

-- envScalar
--   :: (FiniteDimensional env, HilbertSpace env, Scalar env ~ Field)
--   => (env +> env) -> env -> env -> Field
-- envScalar env ketIn braIn = scalarCoeff ketIn (env $ braIn)

-- opCoeff
--   :: ( TensorSpace wl, TensorSpace phys, TensorSpace wr
--      , FiniteDimensional wl, FiniteDimensional phys, FiniteDimensional wr
--      , HilbertSpace wl, HilbertSpace phys, HilbertSpace wr
--      , Scalar wl ~ Field, Scalar phys ~ Field, Scalar wr ~ Field )
--   => OpSite wl phys wr -> Int -> Int -> Int -> Int -> Field
-- opCoeff (OpSite f) lW sIn rW sOut =
--   scalarCoeff (basisAt @wr rW ⊗ basisAt @phys sOut) (f $ (basisAt @wl lW ⊗ basisAt @phys sIn))

-- mpoTransferCoeff
--   :: ( TensorSpace wl, TensorSpace blB, TensorSpace blK, TensorSpace phys
--      , TensorSpace wr, TensorSpace brB, TensorSpace brK
--      , FiniteDimensional wl, FiniteDimensional blB, FiniteDimensional blK
--      , FiniteDimensional wr, FiniteDimensional brB, FiniteDimensional brK
--      , FiniteDimensional phys
--      , HilbertSpace wl, HilbertSpace blB, HilbertSpace blK, HilbertSpace phys
--      , HilbertSpace wr, HilbertSpace brB, HilbertSpace brK
--      , Scalar wl ~ Field, Scalar blB ~ Field, Scalar blK ~ Field, Scalar phys ~ Field
--      , Scalar wr ~ Field, Scalar brB ~ Field, Scalar brK ~ Field )
--   => Site blB phys brB -> OpSite wl phys wr -> Site blK phys brK
--   -> (Bond3 wl blB blK +> Bond3 wl blB blK)
--   -> Int -> Int -> Field
-- mpoTransferCoeff bra op ket env rOut rIn =
--   let (rWOut, rBOut, rKCarry) = bond3Split @wr @brB @brK rOut
--       (rWIn, rBCarry, rKIn) = bond3Split @wr @brB @brK rIn
--   in if rWOut /= rWIn || rKCarry >= dim @blK || rBCarry >= dim @blB
--        then 0
--        else
--          sumV
--            [ scalarCoeff (basisAt @brB rBOut) (applySite bra lB sOut)
--                *^ ( envScalar env
--                       (bond3Basis @wl @blB @blK lW' rBCarry lK')
--                       (bond3Basis @wl @blB @blK lW lB rKCarry)
--                     *^ ( opCoeff op lW sIn rWOut sOut
--                        *^ scalarCoeff (basisAt @brK rKIn) (applySite ket lK' sIn) ) )
--            | lW <- [0 .. dim @wl - 1]
--            , lB <- [0 .. dim @blB - 1]
--            , lW' <- [0 .. dim @wl - 1]
--            , lK' <- [0 .. dim @blK - 1]
--            , sIn <- [0 .. dim @phys - 1]
--            , sOut <- [0 .. dim @phys - 1] ]

-- mpoTransferStep
--   :: ( TensorSpace wl, TensorSpace blB, TensorSpace blK, TensorSpace phys
--      , TensorSpace wr, TensorSpace brB, TensorSpace brK
--      , FiniteDimensional wl, FiniteDimensional blB, FiniteDimensional blK
--      , FiniteDimensional wr, FiniteDimensional brB, FiniteDimensional brK
--      , FiniteDimensional phys
--      , HilbertSpace wl, HilbertSpace blB, HilbertSpace blK, HilbertSpace phys
--      , HilbertSpace wr, HilbertSpace brB, HilbertSpace brK
--      , Scalar wl ~ Field, Scalar blB ~ Field, Scalar blK ~ Field, Scalar phys ~ Field
--      , Scalar wr ~ Field, Scalar brB ~ Field, Scalar brK ~ Field )
--   => Site blB phys brB -> OpSite wl phys wr -> Site blK phys brK
--   -> (Bond3 wl blB blK +> Bond3 wl blB blK)
--   -> (Bond3 wr brB brK +> Bond3 wr brB brK)
-- mpoTransferStep bra op ket env =
--   fst $
--     recomposeLinMap (entireBasis :: SubBasis (Bond3 wr brB brK))
--       [ sumV
--           [ mpoTransferCoeff bra op ket env rOut rIn
--               *^ bond3Basis @wr @brB @brK iW iB iK
--           | rOut <- [0 .. dim @(Bond3 wr brB brK) - 1]
--           , let (iW, iB, iK) = bond3Split @wr @brB @brK rOut
--           ]
--       | rIn <- [0 .. dim @(Bond3 wr brB brK) - 1] ]

-- applyOpSiteToSiteCoeff
--   :: ( TensorSpace wl, TensorSpace phys, TensorSpace wr, TensorSpace bl, TensorSpace br
--      , FiniteDimensional wl, FiniteDimensional phys, FiniteDimensional wr
--      , FiniteDimensional bl, FiniteDimensional br
--      , HilbertSpace wl, HilbertSpace phys, HilbertSpace wr, HilbertSpace bl, HilbertSpace br
--      , Scalar wl ~ Field, Scalar phys ~ Field, Scalar wr ~ Field
--      , Scalar bl ~ Field, Scalar br ~ Field )
--   => OpSite wl phys wr -> Site bl phys br -> Int -> Int -> Int -> Int -> Int -> Field
-- applyOpSiteToSiteCoeff op site lW lB sIn rW rB =
--   sumV
--     [ opCoeff op lW s sIn rW s
--         *^ scalarCoeff (basisAt @br rB) (applySite site (basisAt @bl lB) s)
--     | s <- [0 .. dim @phys - 1] ]

-- applyOpSiteToSite
--   :: ( TensorSpace wl, TensorSpace phys, TensorSpace wr, TensorSpace bl, TensorSpace br
--      , FiniteDimensional wl, FiniteDimensional phys, FiniteDimensional wr
--      , FiniteDimensional bl, FiniteDimensional br
--      , FiniteDimensional (wl ⊗ bl ⊗ phys)
--      , HilbertSpace wl, HilbertSpace phys, HilbertSpace wr, HilbertSpace bl, HilbertSpace br
--      , Scalar wl ~ Field, Scalar phys ~ Field, Scalar wr ~ Field
--      , Scalar bl ~ Field, Scalar br ~ Field )
--   => OpSite wl phys wr -> Site bl phys br -> Site (wl ⊗ bl) phys (wr ⊗ br)
-- applyOpSiteToSite op site =
--   Site $
--     fst $
--       recomposeLinMap (entireBasis :: SubBasis (wl ⊗ bl ⊗ phys))
--         [ sumV
--             [ applyOpSiteToSiteCoeff op site lW lB sIn rW rB
--                 *^ (basisAt @wr rW ⊗ basisAt @br rB)
--             | rW <- [0 .. dim @wr - 1]
--             , rB <- [0 .. dim @br - 1]
--             ]
--         | lW <- [0 .. dim @wl - 1]
--         , lB <- [0 .. dim @bl - 1]
--         , sIn <- [0 .. dim @phys - 1]
--         ]

-- mpoApplyMPS
--   :: ( TensorSpace bond1, TensorSpace bond2, TensorSpace phys
--      , TensorSpace w1, TensorSpace w2
--      , FiniteDimensional bond1, FiniteDimensional bond2, FiniteDimensional phys
--      , FiniteDimensional w1, FiniteDimensional w2
--      , FiniteDimensional (Unit ⊗ bond1), FiniteDimensional (w1 ⊗ bond1)
--      , FiniteDimensional (w2 ⊗ bond2), FiniteDimensional (w2 ⊗ Unit)
--      , FiniteDimensional (Unit ⊗ phys), FiniteDimensional (w1 ⊗ phys), FiniteDimensional (w2 ⊗ phys)
--      , HilbertSpace bond1, HilbertSpace bond2, HilbertSpace phys
--      , HilbertSpace w1, HilbertSpace w2
--      , Scalar bond1 ~ Field, Scalar bond2 ~ Field, Scalar phys ~ Field
--      , Scalar w1 ~ Field, Scalar w2 ~ Field )
--   => MPO w1 phys w2 -> MPS bond1 phys bond2 -> MPS (w1 ⊗ bond1) phys (w2 ⊗ bond2)
-- mpoApplyMPS (MPO lOp cOp rOp) (MPS lSite cSite rSite) =
--   MPS
--     (applyOpSiteToSite lOp lSite)
--     (applyOpSiteToSite cOp cSite)
--     (applyOpSiteToSite rOp rSite)

-- mpsMPOInner
--   :: ( TensorSpace a1, TensorSpace a2, TensorSpace b1, TensorSpace b2, TensorSpace phys
--      , TensorSpace w1, TensorSpace w2
--      , FiniteDimensional a1, FiniteDimensional a2, FiniteDimensional b1, FiniteDimensional b2
--      , FiniteDimensional phys, FiniteDimensional w1, FiniteDimensional w2
--      , FiniteDimensional (Bond3 Unit Unit Unit)
--      , FiniteDimensional (Bond3 w1 a1 b1), FiniteDimensional (Bond3 w2 a2 b2)
--      , FiniteDimensional (Bond3 w2 a2 b2), FiniteDimensional (Bond3 Unit Unit Unit)
--      , HilbertSpace a1, HilbertSpace a2, HilbertSpace b1, HilbertSpace b2, HilbertSpace phys
--      , HilbertSpace w1, HilbertSpace w2
--      , Scalar a1 ~ Field, Scalar a2 ~ Field, Scalar b1 ~ Field, Scalar b2 ~ Field
--      , Scalar phys ~ Field, Scalar w1 ~ Field, Scalar w2 ~ Field )
--   => MPS a1 phys a2 -> MPO w1 phys w2 -> MPS b1 phys b2 -> Field
-- mpsMPOInner psi mpo phi =
--   envScalar finalEnv oneBond3 oneBond3
--   where
--     MPS lBra cBra rBra = mpsConjugate psi
--     MPS lKet cKet rKet = phi
--     MPO lOp cOp rOp = mpo
--     oneBond3 = bond3Basis @Unit @Unit @Unit 0 0 0
--     finalEnv =
--       mpoTransferStep (siteR rBra) (opR rOp) (siteR rKet) $
--         mpoTransferStep (siteC cBra) (opC cOp) (siteC cKet) $
--           mpoTransferStep (siteL lBra) (opL lOp) (siteL lKet) Cat.id

-- identityMPO
--   :: ( TensorSpace phys, Scalar phys ~ Field )
--   => MPO Unit phys Unit
-- identityMPO =
--   let ident = OpSite (Cat.id :: (Unit ⊗ phys) +> (Unit ⊗ phys))
--   in MPO ident ident ident

-- --------------------------------------------------------------------------------
-- -- Bridge to Fixed3 (oracle tests only)
-- --------------------------------------------------------------------------------

-- toFixedSite
--   :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br)
--   => Site (V bl) (V p) (V br) -> F3.Site bl p br
-- toFixedSite (Site lin) = F3.Site lin

-- toFixedMPS
--   :: forall b1 p b2. (KnownNat b1, KnownNat p, KnownNat b2)
--   => MPS (V b1) (V p) (V b2) -> F3.MPS p b1 b2
-- toFixedMPS (MPS l c r) = F3.MPS (toFixedSite l) (toFixedSite c) (toFixedSite r)

-- --------------------------------------------------------------------------------
-- -- Property tests
-- --------------------------------------------------------------------------------

-- smallComplex :: QC.Gen Field
-- smallComplex = do
--   r <- QC.elements [-2 .. 2 :: Int]
--   i <- QC.elements [-2 .. 2 :: Int]
--   pure (fromIntegral r :+ fromIntegral i)

-- genV :: forall v. (FiniteDimensional v, HilbertSpace v, Scalar v ~ Field) => QC.Gen v
-- genV = do
--   coeffs <- replicateM (dim @v) smallComplex
--   pure (sumV [ c *^ basisAt @v i | (c, i) <- zip coeffs [0 ..] ])

-- genLinMap
--   :: forall dom cod. (FiniteDimensional dom, FiniteDimensional cod, HilbertSpace cod, Scalar cod ~ Field)
--   => QC.Gen (dom +> cod)
-- genLinMap = do
--   imgs <- replicateM (dim @dom) (genV @cod)
--   pure (fst (recomposeLinMap (entireBasis :: SubBasis dom) imgs))

-- genSiteV2
--   :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br)
--   => QC.Gen (Site (V bl) (V p) (V br))
-- genSiteV2 = Site <$> genLinMap @(V bl ⊗ V p) @(V br)

-- genMPSV222 :: QC.Gen (MPS (V 2) (V 2) (V 2))
-- genMPSV222 =
--   MPS <$> genSiteV2 @1 @2 @2 <*> genSiteV2 @2 @2 @2 <*> genSiteV2 @2 @2 @1

-- prop_generalInnerConjugateSymmetric :: QC.Property
-- prop_generalInnerConjugateSymmetric =
--   QC.forAll genMPSV222 $ \psi ->
--   QC.forAll genMPSV222 $ \phi ->
--     mpsInner psi phi QC.=== conjugate (mpsInner phi psi)

-- prop_generalNormNonNegative :: QC.Property
-- prop_generalNormNonNegative =
--   QC.forAll genMPSV222 $ \psi ->
--     let z = mpsInner psi psi
--     in QC.counterexample (show z) (imagPart z == 0 && realPart z >= 0)

-- prop_generalInnerMatchesFixed3Reference :: QC.Property
-- prop_generalInnerMatchesFixed3Reference =
--   QC.forAll genMPSV222 $ \psi ->
--   QC.forAll genMPSV222 $ \phi ->
--     mpsInner psi phi QC.=== mpsInnerReference (toFixedMPS psi) (toFixedMPS phi)
