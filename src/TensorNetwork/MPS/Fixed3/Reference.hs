{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | Reference / oracle implementations for 'TensorNetwork.MPS.Fixed3'.
--
-- Coefficient reads, basis sums and explicit index formulas used only as
-- QuickCheck oracles — never the production contraction path. Coefficients
-- are defined by /application to basis vectors/; tensor components are read
-- through the canonical 'toArray' order ('Dimensional'), the same order
-- 'TensorNetwork.Categorical.fuseBond' uses, so there is a single flat-index
-- convention in play.
--
-- Flat-space convention (matches 'toArray' on nested tensors,
-- co-lexicographic: first factor varies fastest):
--
--   @flat index of (s₁,s₂,s₃) = s₁ + p·s₂ + p²·s₃@
module TensorNetwork.MPS.Fixed3.Reference
  ( -- * Site application and coefficients
    applySite
  , applyOpSite
  , siteCoeff
  , opSiteCoeff
  , envCoeff
  , env3Coeff
    -- * Amplitudes and operator elements
  , amplitude
  , mpoElement
    -- * Whole-state oracles
  , mpsToTensorReference
  , mpsToFlatReference
  , flatIndex3
  , mpsInnerReference
  , mpsMPOInnerReference
    -- * Transfer-step oracles
  , matrixTransferCoeff
  , matrixMPOTransferCoeff
    -- * Dense operator oracles
  , mpoToMatrix
  , mpoApplyFlat
  ) where

import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import TensorNetwork.MPS.Fixed3.Internal
  ( Site (..), MPS (..), OpSite (..), MPO (..), cdim, basis, one1 )
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗) )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, M, Sized (fromList, unwrap))
import GHC.TypeLits (KnownNat, type (*))
import Data.Complex (Complex, conjugate)
import Data.VectorSpace (VectorSpace ((*^)), sumV)
import qualified Data.Vector.Storable as VS

--------------------------------------------------------------------------------
-- Site application and coefficient reads
--------------------------------------------------------------------------------

-- | Apply a site map to @(bond, |s⟩)@.
applySite
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br))
  => Site bl p br -> C bl -> Int -> C br
applySite site bond s = siteLin site $ (bond ⊗ basis @p s)

-- | Apply an MPO site to @(bond, |t⟩)@ — @t@ is the /bra-side/ (output)
-- physical index in transfer orientation — and project the codomain tensor
-- @C wr ⊗ C p@ onto ket-side physical index @s@.
applyOpSite
  :: forall wl p wr.
     (KnownNat wl, KnownNat p, KnownNat wr, KnownNat (wr * p))
  => OpSite wl p wr -> C wl -> Int -> Int -> C wr
applyOpSite site bond t s =
  let arr' = toArray (opSiteLin site $ (bond ⊗ basis @p t)) :: VS.Vector (Complex Double)
  in fromList [ arr' VS.! (r + cdim @wr * s) | r <- [0 .. cdim @wr - 1] ]

-- | Coefficient @site[(lB, s) ↦ r]@, read off by application.
siteCoeff
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br))
  => Site bl p br -> Int -> Int -> Int -> Complex Double
siteCoeff site lB s r = unwrap (applySite site (basis @bl lB) s) VS.! r

-- | Coefficient @op[(lW, t) ↦ (r, s)]@ in transfer orientation.
opSiteCoeff
  :: forall wl p wr.
     (KnownNat wl, KnownNat p, KnownNat wr, KnownNat (wr * p))
  => OpSite wl p wr -> Int -> Int -> Int -> Int -> Complex Double
opSiteCoeff site lW t r s =
  unwrap (applyOpSite site (basis @wl lW) t s) VS.! r

-- | Coefficient of @e_lOut@ in @env e_lIn@ for a bond environment.
envCoeff
  :: forall a b. (KnownNat a, KnownNat b)
  => (C a +> C b) -> Int -> Int -> Complex Double
envCoeff env lIn lOut = unwrap (env $ basis @a lIn) VS.! lOut

-- | Coefficient of @e_lW ⊗ e_lK@ in @env e_lB@ for a typed MPO environment
-- @C a +> (C w ⊗ C b)@ (canonical 'toArray' component order).
env3Coeff
  :: forall a w b. (KnownNat a, KnownNat w, KnownNat b, KnownNat (w * b))
  => (C a +> (C w ⊗ C b)) -> Int -> Int -> Int -> Complex Double
env3Coeff env lB lW lK =
  (toArray (env $ basis @a lB) :: VS.Vector (Complex Double))
    VS.! (lW + cdim @w * lK)

--------------------------------------------------------------------------------
-- Amplitudes and operator elements (bond threading)
--------------------------------------------------------------------------------

amplitude
  :: forall p b.
     ( KnownNat p, KnownNat b
     , KnownNat (p * b), KnownNat (p * b), KnownNat (p * 1) )
  => MPS p b -> Int -> Int -> Int -> Complex Double
amplitude (MPS sL sC sR) s1 s2 s3 =
  let v1 = applySite @1 @p @b sL one1 s1
      v2 = applySite @b @p @b sC v1 s2
      r  = applySite @b @p @1 sR v2 s3
  in unwrap r VS.! 0

-- | Dense operator matrix element @H[t₁,t₂,t₃; s₁,s₂,s₃] = ⟨t|H|s⟩@ via bond
-- threading (transfer orientation: @t@ enters the domain, @s@ is read off).
mpoElement
  :: forall p w.
     ( KnownNat p, KnownNat w, KnownNat w
     , KnownNat (w * p), KnownNat (1 * p) )
  => MPO p w
  -> Int -> Int -> Int
  -> Int -> Int -> Int
  -> Complex Double
mpoElement (MPO l c r) t1 t2 t3 s1 s2 s3 =
  let v1 = applyOpSite @1 @p @w l one1 t1 s1
      v2 = applyOpSite @w @p @w c v1 t2 s2
      v3 = applyOpSite @w @p @1 r v2 t3 s3
  in unwrap v3 VS.! 0

--------------------------------------------------------------------------------
-- Whole-state oracles (explicit basis sums)
--------------------------------------------------------------------------------

-- | Physical state as @C p ⊗ (C p ⊗ C p)@ via explicit basis sum (oracle).
mpsToTensorReference
  :: forall p b.
     ( KnownNat p, KnownNat b, KnownNat b
     , KnownNat (p * b), KnownNat (p * b), KnownNat (p * 1) )
  => MPS p b -> C p ⊗ (C p ⊗ C p)
mpsToTensorReference mps =
  sumV
    [ amplitude mps s1 s2 s3 *^ (basis @p s1 ⊗ (basis @p s2 ⊗ basis @p s3))
    | s1 <- [0 .. p - 1], s2 <- [0 .. p - 1], s3 <- [0 .. p - 1] ]
  where p = cdim @p

-- | Flat index of @(s₁,s₂,s₃)@, co-lexicographic (first index fastest).
flatIndex3 :: Int -> Int -> Int -> Int -> Int
flatIndex3 p s1 s2 s3 = s1 + p * s2 + p * p * s3

-- | Flattened physical state @C (p³)@ in the canonical co-lexicographic
-- order, @(s₁,s₂,s₃) ↦ s₁ + p·s₂ + p²·s₃@ (oracle).
mpsToFlatReference
  :: forall p b.
     ( KnownNat p, KnownNat b, KnownNat (p * p * p)
     , KnownNat (p * b), KnownNat (p * 1) )
  => MPS p b -> C (p * p * p)
mpsToFlatReference mps =
  fromList
    [ amplitude mps s1 s2 s3
    | s3 <- [0 .. p - 1], s2 <- [0 .. p - 1], s1 <- [0 .. p - 1] ]
  where p = cdim @p

-- | Reference implementation of ⟨ψ|φ⟩ as an explicit physical-basis sum.
mpsInnerReference
  :: forall p a.
     ( KnownNat p
     , KnownNat a, KnownNat a
     , KnownNat (p * a), KnownNat (p * a)
     , KnownNat (p * 1) )
  => MPS p a -> MPS p a -> Complex Double
mpsInnerReference psi phi =
  sum
    [ conjugate (amplitude psi s1 s2 s3) * amplitude phi s1 s2 s3
    | s1 <- [0 .. cdim @p - 1]
    , s2 <- [0 .. cdim @p - 1]
    , s3 <- [0 .. cdim @p - 1]
    ]

-- | Reference @⟨ψ|H|φ⟩@ as an explicit physical-basis sum (oracle).
mpsMPOInnerReference
  :: forall p a w b.
     ( KnownNat p
     , KnownNat a, KnownNat b
     , KnownNat w, KnownNat w
     , KnownNat (p * a), KnownNat (p * a)
     , KnownNat (p * b), KnownNat (p * b)
     , KnownNat (p * 1)
     , KnownNat (w * p), KnownNat (w * p), KnownNat (1 * p) )
  => MPS p a -> MPO p w -> MPS p b -> Complex Double
mpsMPOInnerReference psi mpo phi =
  sum
    [ conjugate (amplitude psi t1 t2 t3)
        * mpoElement mpo t1 t2 t3 s1 s2 s3
        * amplitude phi s1 s2 s3
    | t1 <- ix, t2 <- ix, t3 <- ix
    , s1 <- ix, s2 <- ix, s3 <- ix
    ]
  where ix = [0 .. cdim @p - 1]

--------------------------------------------------------------------------------
-- Transfer-step oracles
--------------------------------------------------------------------------------

-- | Explicit formula for one inner-product transfer update. Environments map
-- the /bra/ bond to the /ket/ bond; the bra site enters conjugated:
--
--   @env'[rB → rK] = Σ_{l,l',s} conj(bra[(l,s)→rB]) · env[l→l'] · ket[(l',s)→rK]@
matrixTransferCoeff
  :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br))
  => Site bl p br -> Site bl p br -> (C bl +> C bl) -> Int -> Int -> Complex Double
matrixTransferCoeff bra ket env rBra rKet =
  sum
    [ conjugate (siteCoeff @bl @p @br bra l s rBra)
        * envCoeff @bl @bl env l l'
        * siteCoeff @bl @p @br ket l' s rKet
    | l <- [0 .. cdim @bl - 1]
    , l' <- [0 .. cdim @bl - 1]
    , s <- [0 .. cdim @p - 1] ]

-- | Explicit formula for one MPO transfer update with /typed/ environments
-- @C a +> (C w ⊗ C b)@ (bra bond in, MPO ⊗ ket bonds out):
--
--   @env'[rB → (rW,rK)] = Σ conj(bra[(lB,t)→rB]) · env[lB→(lW,lK)]
--                            · op[(lW,t)→(rW,s)] · ket[(lK,s)→rK]@
matrixMPOTransferCoeff
  :: forall p wl wr a b.
     ( KnownNat p, KnownNat wl, KnownNat wr, KnownNat a, KnownNat b
     , KnownNat (p * a), KnownNat (p * b)
     , KnownNat (wl * a), KnownNat (wr * p), KnownNat (wl * b) )
  => Site a p a -> OpSite wl p wr -> Site b p b
  -> (C a +> (C wl ⊗ C b))
  -> Int -> Int -> Int -> Complex Double
matrixMPOTransferCoeff bra op ket env rB rW rK =
  sum
    [ conjugate (siteCoeff @a @p @a bra lB t rB)
        * env3Coeff @a @wl @b env lB lW lK
        * opSiteCoeff @wl @p @wr op lW t rW s
        * siteCoeff @b @p @b ket lK s rK
    | lB <- [0 .. cdim @a - 1]
    , lW <- [0 .. cdim @wl - 1]
    , lK <- [0 .. cdim @b - 1]
    , t <- [0 .. cdim @p - 1]
    , s <- [0 .. cdim @p - 1]
    ]

--------------------------------------------------------------------------------
-- Dense operator oracles
--------------------------------------------------------------------------------

-- | Matrix form of the 3-site MPO on flattened physical states; row index
-- @t₁ + p·t₂ + p²·t₃@, column index @s₁ + p·s₂ + p²·s₃@ ('flatIndex3').
mpoToMatrix
  :: forall p w.
     ( KnownNat p, KnownNat w, KnownNat (p * p * p)
     , KnownNat (w * p), KnownNat (1 * p) )
  => MPO p w -> M (p * p * p) (p * p * p)
mpoToMatrix mpo =
  fromList
    [ mpoElement mpo t1 t2 t3 s1 s2 s3
    | t3 <- ix, t2 <- ix, t1 <- ix
    , s3 <- ix, s2 <- ix, s1 <- ix
    ]
  where
    p = cdim @p
    ix = [0 .. p - 1]

-- | Apply an MPO to a flattened physical state by explicit summation.
mpoApplyFlat
  :: forall p w.
     ( KnownNat p, KnownNat w, KnownNat (p * p * p)
     , KnownNat (w * p), KnownNat (1 * p) )
  => MPO p w -> C (p * p * p) -> C (p * p * p)
mpoApplyFlat mpo v =
  fromList
    [ sum
        [ mpoElement mpo t1 t2 t3 s1 s2 s3
            * (unwrap v VS.! flatIndex3 p s1 s2 s3)
        | s1 <- ix, s2 <- ix, s3 <- ix ]
    | t3 <- ix, t2 <- ix, t1 <- ix ]
  where
    p = cdim @p
    ix = [0 .. p - 1]
