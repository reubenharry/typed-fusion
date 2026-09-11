{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Concrete leaf/Hom spines and term-level smokes for symbolic Hom (SU(2) Nat engine).
-- Spines are spelled as 'FuseFTrees' / ''IrrepTree' / ''Irrep' compositions (no alias layer).
module Hom.Smoke
  ( fmoveTrees111, fmoveInvTrees111
  , fmoveTrees000, fmoveInvTrees000
  , fmoveTrees110, fmoveInvTrees110
  , fmoveTrees112, fmoveInvTrees112
  , idRightFinv111
  , fillFTreeVScaled
  , approxHomTrees
  , approxHom11
  , checkFmoveTrees111
  , checkFmoveTrees110
  , checkFmoveTrees112
  , checkFmoveTreesLeaves
  , checkUnitorI1
  , checkUnitorHom11
  , checkCupIHom
  , checkComposeHomTrees111
  , checkComposeHomTrees000
  , checkComposeHomTrees222
  , checkComposeHomTrees333
  , checkComposeHomTrees121
  , checkFmoveTreesLeaves121
  , checkFmoveHomLeft111
  , checkHomFusedCategory222
  , checkHomFusedCategory333
  , checkHomInterCategory111
  , checkForgetHomFusedId111
  , checkForgetHomInterCompose111
  , checkI2FmoveSmoke
  , checkFmoveOuter111
  , checkIdLeftId111
  ) where

import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..), (.), id)
import Data.Complex (Complex ((:+)), conjugate, magnitude, realPart)
import Data.VectorSpace (InnerSpace ((<.>)), (*^), (^-^))
import qualified Data.Vector.Storable as VS
import Categorical.Linear ((⊗^))
import Fusion.Obj (Obj (Irrep))
import Symmetry.Group (Group (SU2))
import Hom.Core
import Hom.Expr
import Hom.FMove
import Hom.FTreeV
import Hom.Singletons
import Hom.TypeLevel
import GHC.TypeLits (KnownNat)
import Math.LinearMap.Category
  ( pattern LinearFunction
  , type (+>)
  )
import Math.LinearMap.Category.Class (asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, konst)

import Prelude hiding (id, (.), ($))

-- | Triple-leaf F-move via 'fmoveTrees' (@½⊗½⊗½@).
fmoveTrees111
  :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])
  -> FTreeV (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
fmoveTrees111 = fmoveTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1])

fmoveInvTrees111
  :: FTreeV (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
  -> FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])
fmoveInvTrees111 = fmoveInvTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1])

fmoveTrees000
  :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 0] '[ 'IrrepTree 0]) '[ 'IrrepTree 0])
  -> FTreeV (FuseFTrees '[ 'IrrepTree 0] (FuseFTrees '[ 'IrrepTree 0] '[ 'IrrepTree 0]))
fmoveTrees000 = fmoveTrees @('[ 'IrrepTree 0]) @('[ 'IrrepTree 0]) @('[ 'IrrepTree 0])

fmoveInvTrees000
  :: FTreeV (FuseFTrees '[ 'IrrepTree 0] (FuseFTrees '[ 'IrrepTree 0] '[ 'IrrepTree 0]))
  -> FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 0] '[ 'IrrepTree 0]) '[ 'IrrepTree 0])
fmoveInvTrees000 = fmoveInvTrees @('[ 'IrrepTree 0]) @('[ 'IrrepTree 0]) @('[ 'IrrepTree 0])

fmoveTrees110
  :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 0])
  -> FTreeV (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 0]))
fmoveTrees110 = fmoveTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 0])

fmoveInvTrees110
  :: FTreeV (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 0]))
  -> FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 0])
fmoveInvTrees110 = fmoveInvTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 0])

fmoveTrees112
  :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
  -> FTreeV (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 2]))
fmoveTrees112 = fmoveTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 2])

fmoveInvTrees112
  :: FTreeV (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 2]))
  -> FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
fmoveInvTrees112 = fmoveInvTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 2])

-- | @Fuse(id, F-inv)@ on Mid — instance of 'idRight'.
idRightFinv111
  :: FTreeV (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])))
  -> FTreeV (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1]))
idRightFinv111 =
  idRight
    @('[ 'IrrepTree 1])
    @(FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
    @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])
    fmoveInvTrees111

-- | Fill a spine with scaled ones (deterministic nested-F sample).
fillFTreeVScaled
  :: forall ts
   . KnownFTrees ts
  => FTreeV ts
fillFTreeVScaled = go 0 (fTreesSing @_ @ts)
  where
    go :: Int -> SFTrees ts' -> FTreeV ts'
    go _ SFTreesNil = FNil
    go i (SFTreesCons t rest) =
      case t of
        SIrrepTree {} ->
          FCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)
        SFrom {} ->
          FCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)

-- | Approx equality on Hom / association spines (expanded spine-order flat).
approxHomTrees
  :: forall ts
   . KnownFTrees ts
  => FTreeV ts
  -> FTreeV ts
  -> Bool
approxHomTrees u v =
  let bu = fTreeVToExpandedFlat @ts u
      bv = fTreeVToExpandedFlat @ts v
      err =
        VS.sum $
          VS.zipWith
            (\x y -> let d = x - y in realPart (d * conjugate d))
            bu
            bv
   in err < 1e-10

approxHom11
  :: FTreeV (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
  -> FTreeV (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
  -> Bool
approxHom11 = approxHomTrees @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])

-- | Tree F round-trip on @½⊗½⊗½@ (@F⁻¹ ∘ F ≈ id@).
checkFmoveTrees111
  :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1]) -> Bool
checkFmoveTrees111 tv =
  approxFTreeV
    @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])
    tv
    (fmoveInvTrees111 (fmoveTrees111 tv))

-- | Tree F round-trip on @½⊗½⊗0@.
checkFmoveTrees110
  :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 0]) -> Bool
checkFmoveTrees110 tv =
  approxFTreeV
    @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 0])
    tv
    (fmoveInvTrees110 (fmoveTrees110 tv))

-- | Tree F round-trip on @½⊗½⊗1@.
checkFmoveTrees112
  :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2]) -> Bool
checkFmoveTrees112 tv =
  approxFTreeV
    @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
    tv
    (fmoveInvTrees112 (fmoveTrees112 tv))

-- | Round-trip only: works for any irrep-leaf triple.
checkFmoveTreesLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownFTrees ( FuseFTrees (FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree jb]) '[ 'IrrepTree jc] )
     , KnownFTrees ( FuseFTrees '[ 'IrrepTree ja] (FuseFTrees '[ 'IrrepTree jb] '[ 'IrrepTree jc]) )
     )
  => FTreeV ( FuseFTrees (FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree jb]) '[ 'IrrepTree jc] )
  -> Bool
checkFmoveTreesLeaves tv =
  let rt =
        fmoveInvTrees @('[ 'IrrepTree ja]) @('[ 'IrrepTree jb]) @('[ 'IrrepTree jc])
          (fmoveTrees @('[ 'IrrepTree ja]) @('[ 'IrrepTree jb]) @('[ 'IrrepTree jc]) tv)
   in approxFTreeV
        @( FuseFTrees (FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree jb]) '[ 'IrrepTree jc] )
        tv
        rt

-- | 'unitor' on @Unit ⊗ I½@: payload round-trip.
checkUnitorI1 :: Bool
checkUnitorI1 =
  let u =
        FCons @('From 1 '( 'IrrepTree 0, 'IrrepTree 1)) (konst 0.42) FNil
          :: FTreeV (FuseFTrees Unit '[ 'IrrepTree 1])
      v = unitor @('[ 'IrrepTree 1]) u
   in case fTreeVToV @('[ 'IrrepTree 1]) v of
        x ->
          let d = x ^-^ konst 0.42
           in magnitude (d <.> d) < 1e-18

-- | 'unitorHom' = 'idRight' 'unitor' on after-cup leaf-½ spine.
checkUnitorHom11 :: Bool
checkUnitorHom11 =
  let mid =
        FCons @('From 0 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 0, 'IrrepTree 1))) (konst 0.3) $
          FCons @('From 2 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 0, 'IrrepTree 1))) (konst 0.7) FNil
      out = unitorHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) mid
   in approxHom11 out $
        FCons @('From 0 '( 'IrrepTree 1, 'IrrepTree 1)) (konst 0.3) $
          FCons @('From 2 '( 'IrrepTree 1, 'IrrepTree 1)) (konst 0.7) FNil

-- | Mac Lane 'cup' on leaf Hom: singlet × FS·dim (@0 → 1@, @½ → −2@, @1 → 3@).
checkCupIHom :: Bool
checkCupIHom =
  let s0 =
        case cup @('[ 'IrrepTree 0]) (idHomFTrees @('[ 'IrrepTree 0])) of
          FCons v FNil -> konst 1 <.> v
          _ -> 0
      s1 =
        case cup @('[ 'IrrepTree 1]) (idHomFTrees @('[ 'IrrepTree 1])) of
          FCons v FNil -> konst 1 <.> v
          _ -> 0
      s2 =
        case cup @('[ 'IrrepTree 2]) (idHomFTrees @('[ 'IrrepTree 2])) of
          FCons v FNil -> konst 1 <.> v
          _ -> 0
   in magnitude (s0 - 1) < 1e-12
        && magnitude (s1 - (-2)) < 1e-12
        && magnitude (s2 - 3) < 1e-12

-- | Five-morphism 'composeHomTrees' unit laws on leaf-½.
checkComposeHomTrees111 :: Bool
checkComposeHomTrees111 =
  let f =
        FCons @('From 0 '( 'IrrepTree 1, 'IrrepTree 1)) (konst 0.3) $
          FCons @('From 2 '( 'IrrepTree 1, 'IrrepTree 1)) (konst 0.7) FNil
      idH = idHomFTrees @('[ 'IrrepTree 1])
      idid = composeHomTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) idH idH
      fid = composeHomTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) f idH
      idf = composeHomTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) idH f
   in approxHomTrees @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) idid idH
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) fid f
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) idf f

-- | Five-morphism compose unit laws on trivial Hom.
checkComposeHomTrees000 :: Bool
checkComposeHomTrees000 =
  let f = FCons @('From 0 '( 'IrrepTree 0, 'IrrepTree 0)) (konst 0.4) FNil
      idH = idHomFTrees @('[ 'IrrepTree 0])
   in approxHomTrees @(FuseFTrees '[ 'IrrepTree 0] '[ 'IrrepTree 0])
        (composeHomTrees @('[ 'IrrepTree 0]) @('[ 'IrrepTree 0]) @('[ 'IrrepTree 0]) idH idH)
        idH
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 0] '[ 'IrrepTree 0])
          (composeHomTrees @('[ 'IrrepTree 0]) @('[ 'IrrepTree 0]) @('[ 'IrrepTree 0]) f idH)
          f
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 0] '[ 'IrrepTree 0])
          (composeHomTrees @('[ 'IrrepTree 0]) @('[ 'IrrepTree 0]) @('[ 'IrrepTree 0]) idH f)
          f

-- | I spin-1 Hom compose: @id∘id ≈ id@ and left/right units on multi-channel Hom.
checkComposeHomTrees222 :: Bool
checkComposeHomTrees222 =
  let f =
        FCons @('From 0 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.2) $
          FCons @('From 2 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.3) $
            FCons @('From 4 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.5) FNil
      idH = idHomFTrees @('[ 'IrrepTree 2])
      idid = composeHomTrees @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) idH idH
      fid = composeHomTrees @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) f idH
      idf = composeHomTrees @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) idH f
   in approxHomTrees @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) idid idH
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) fid f
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) idf f

-- | Polymorphic leaf F + outer Hom: unit laws on @tj = 3@.
checkComposeHomTrees333 :: Bool
checkComposeHomTrees333 =
  let f =
        FCons @('From 0 '( 'IrrepTree 3, 'IrrepTree 3)) (konst 0.1) $
          FCons @('From 2 '( 'IrrepTree 3, 'IrrepTree 3)) (konst 0.2) $
            FCons @('From 4 '( 'IrrepTree 3, 'IrrepTree 3)) (konst 0.3) $
              FCons @('From 6 '( 'IrrepTree 3, 'IrrepTree 3)) (konst 0.4) FNil
      idH = idHomFTrees @('[ 'IrrepTree 3])
      idid = composeHomTrees @('[ 'IrrepTree 3]) @('[ 'IrrepTree 3]) @('[ 'IrrepTree 3]) idH idH
      fid = composeHomTrees @('[ 'IrrepTree 3]) @('[ 'IrrepTree 3]) @('[ 'IrrepTree 3]) f idH
      idf = composeHomTrees @('[ 'IrrepTree 3]) @('[ 'IrrepTree 3]) @('[ 'IrrepTree 3]) idH f
   in approxHomTrees @(FuseFTrees '[ 'IrrepTree 3] '[ 'IrrepTree 3]) idid idH
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 3] '[ 'IrrepTree 3]) fid f
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 3] '[ 'IrrepTree 3]) idf f

-- | Unequal-leaf compose @½ → 1 → ½@: left/right units on @FuseFTrees ½ 1@.
checkComposeHomTrees121 :: Bool
checkComposeHomTrees121 =
  let f :: FTreeV (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 2])
      f =
        FCons @('From 1 '( 'IrrepTree 1, 'IrrepTree 2)) (konst 0.3) $
          FCons @('From 3 '( 'IrrepTree 1, 'IrrepTree 2)) (konst 0.7) FNil
      id1 = idHomFTrees @('[ 'IrrepTree 1])
      id2 = idHomFTrees @('[ 'IrrepTree 2])
      -- f ∘ id₁  and  id₂ ∘ f
      idf = composeHomTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 2]) id1 f
      fid = composeHomTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) f id2
   in approxHomTrees @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 2]) idf f
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 2]) fid f

-- | Irrep-leaf F round-trip for @½⊗1⊗½@ via 'fmoveTrees'.
checkFmoveTreesLeaves121 :: Bool
checkFmoveTreesLeaves121 =
  let assocL = fillFTreeVScaled @( FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 2]) '[ 'IrrepTree 1] )
      rt =
        fmoveInvTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 1])
          (fmoveTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 1]) assocL)
   in approxHomTrees @( FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 2]) '[ 'IrrepTree 1] ) assocL rt

-- | Nested F: Hom⊗leaf⊗leaf (@(½*⊗½) ⊗ ½ ⊗ ½@) round-trip via channel-keyed F.
checkFmoveHomLeft111 :: Bool
checkFmoveHomLeft111 =
  let assocL =
        fillFTreeVScaled
          @( FuseFTrees (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1]) '[ 'IrrepTree 1] )
      rt =
        fmoveInvTreesHomLeft @1 @1 @1
          (fmoveTreesHomLeft @1 @1 @1 assocL)
   in approxHomTrees
        @( FuseFTrees (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1]) '[ 'IrrepTree 1] )
        assocL
        rt

-- | 'HomFused' packaging unit laws on spin-1 via 'composeHomFused'.
checkHomFusedCategory222 :: Bool
checkHomFusedCategory222 =
  let f :: HomFused SU2 ('Irrep 2) ('Irrep 2)
      f =
        HomFused $
          FCons @('From 0 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.2) $
            FCons @('From 2 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.3) $
              FCons @('From 4 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.5) FNil
      idT = HomFused (idHomFTrees @('[ 'IrrepTree 2]))
      HomFused idid =
        composeHomFused @('Irrep 2) @('Irrep 2) @('Irrep 2) idT idT
      HomFused fid =
        composeHomFused @('Irrep 2) @('Irrep 2) @('Irrep 2) idT f
      HomFused idf =
        composeHomFused @('Irrep 2) @('Irrep 2) @('Irrep 2) f idT
   in approxHomTrees @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) idid (idHomFTrees @('[ 'IrrepTree 2]))
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) fid (unHomFused f)
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) idf (unHomFused f)

-- | 'HomFused' unit laws on @tj = 3@ via 'idHomFTrees'.
checkHomFusedCategory333 :: Bool
checkHomFusedCategory333 =
  let f :: HomFused SU2 ('Irrep 3) ('Irrep 3)
      f =
        HomFused $
          FCons @('From 0 '( 'IrrepTree 3, 'IrrepTree 3)) (konst 0.1) $
            FCons @('From 2 '( 'IrrepTree 3, 'IrrepTree 3)) (konst 0.2) $
              FCons @('From 4 '( 'IrrepTree 3, 'IrrepTree 3)) (konst 0.3) $
                FCons @('From 6 '( 'IrrepTree 3, 'IrrepTree 3)) (konst 0.4) FNil
      idT = HomFused (idHomFTrees @('[ 'IrrepTree 3]))
      HomFused idid =
        composeHomFused @('Irrep 3) @('Irrep 3) @('Irrep 3) idT idT
      HomFused fid =
        composeHomFused @('Irrep 3) @('Irrep 3) @('Irrep 3) idT f
      HomFused idf =
        composeHomFused @('Irrep 3) @('Irrep 3) @('Irrep 3) f idT
   in approxHomTrees @(FuseFTrees '[ 'IrrepTree 3] '[ 'IrrepTree 3]) idid (idHomFTrees @('[ 'IrrepTree 3]))
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 3] '[ 'IrrepTree 3]) fid (unHomFused f)
        && approxHomTrees @(FuseFTrees '[ 'IrrepTree 3] '[ 'IrrepTree 3]) idf (unHomFused f)

-- | 'HomInter' unit laws on spin-½ via embed → 'composeHomTrees' → filter.
checkHomInterCategory111 :: Bool
checkHomInterCategory111 =
  let f :: HomInter SU2 ('Irrep 1) ('Irrep 1)
      f =
        HomInter $
          scaleFTreeV
            @(FilterTrivial (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
            (0.3 :+ 0)
            (idHomInterVal @('Irrep 1))
      idT = HomInter (idHomInterVal @('Irrep 1))
      HomInter idid =
        composeHomInter @('Irrep 1) @('Irrep 1) @('Irrep 1) idT idT
      HomInter fid =
        composeHomInter @('Irrep 1) @('Irrep 1) @('Irrep 1) idT f
      HomInter idf =
        composeHomInter @('Irrep 1) @('Irrep 1) @('Irrep 1) f idT
   in approxHomTrees
        @(FilterTrivial (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
        idid
        (idHomInterVal @('Irrep 1))
        && approxHomTrees
          @(FilterTrivial (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
          fid
          (unHomInter f)
        && approxHomTrees
          @(FilterTrivial (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
          idf
          (unHomInter f)

-- | Forgetful densify @HomFused SU2 ⇒ HomUnfused@ on spin-½ (smoke-only adapter).
-- CG-unfuse, FS dual iso on the left leg, scale by @√2@.
forgetHomFusedHalf
  :: HomFused SU2 ('Irrep 1) ('Irrep 1)
  -> HomUnfused SU2 ('Irrep 1) ('Irrep 1)
forgetHomFusedHalf (HomFused r) =
  let u = unfuseTrees @('IrrepTree 1) @('IrrepTree 1) r
      dualIso :: C 2 +> C 2
      dualIso =
        arr . LinearFunction $ \v ->
          let [a, b] = VS.toList (toArray v)
           in unsafeFromArray (VS.fromList [-b, a])
      mid = (dualIso ⊗^ (id :: C 2 +> C 2)) $ u
      packed = (sqrt 2 :+ 0) *^ mid
      m = fromTensor -+$=> packed :: C 2 +> C 2
   in HomUnfused (asTensor -+$=> m)

-- | Forgetful densify of fused id matches unfused id on spin-½.
checkForgetHomFusedId111 :: Bool
checkForgetHomFusedId111 =
  let fusedId = id :: HomFused SU2 ('Irrep 1) ('Irrep 1)
      unfusedId = id :: HomUnfused SU2 ('Irrep 1) ('Irrep 1)
      forgotten = forgetHomFusedHalf fusedId
   in approxHomUnfused forgotten unfusedId

-- | Forgetful densify is a functor on the intertwiner (singlet) sector:
-- @forget(g ∘_Inter f) = forget(g) ∘_Unfused forget(f)@ for scaled ids.
checkForgetHomInterCompose111 :: Bool
checkForgetHomInterCompose111 =
  let f :: HomInter SU2 ('Irrep 1) ('Irrep 1)
      f =
        HomInter $
          scaleFTreeV
            @(FilterTrivial (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
            (0.4 :+ 0)
            (idHomInterVal @('Irrep 1))
      g :: HomInter SU2 ('Irrep 1) ('Irrep 1)
      g =
        HomInter $
          scaleFTreeV
            @(FilterTrivial (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
            ((-0.5) :+ 0)
            (idHomInterVal @('Irrep 1))
      -- Embed intertwiners to HomFused, densify, compare compose both ways.
      emb
        :: HomInter SU2 ('Irrep 1) ('Irrep 1)
        -> HomFused SU2 ('Irrep 1) ('Irrep 1)
      emb (HomInter t) =
        HomFused (embedTrivialFTreeV @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) t)
      lhs =
        forgetHomFusedHalf
          (composeHomFused
             @('Irrep 1)
             @('Irrep 1)
             @('Irrep 1)
             (emb g)
             (emb f))
      rhs = forgetHomFusedHalf (emb g) . forgetHomFusedHalf (emb f)
   in approxHomUnfused lhs rhs

approxHomUnfused
  :: HomUnfused SU2 ('Irrep 1) ('Irrep 1)
  -> HomUnfused SU2 ('Irrep 1) ('Irrep 1)
  -> Bool
approxHomUnfused (HomUnfused u) (HomUnfused v) =
  let du = toArray u
      dv = toArray v
   in VS.length du == VS.length dv
        && VS.and (VS.zipWith (\x y -> magnitude (x - y) < 1e-9) du dv)

-- | Spin-1 leaf smoke: irrep F + outer Hom F round-trips.
checkI2FmoveSmoke :: Bool
checkI2FmoveSmoke =
  let assocL = fillFTreeVScaled @( FuseFTrees (FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) '[ 'IrrepTree 2] )
      assocOk =
        approxHomTrees @( FuseFTrees (FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) '[ 'IrrepTree 2] ) assocL $
          fmoveInvTrees @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2])
            (fmoveTrees @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) assocL)
      idH = idHomFTrees @('[ 'IrrepTree 2])
      dom =
        fuseFTreesTerm
          @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2])
          @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2])
          idH
          idH
      mid = fmoveOuterHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) dom
      back = fmoveInvOuterHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) mid
   in assocOk
        && approxHomTrees
          @( FuseFTrees (FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) (FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) )
          dom
          back

-- | Outer F round-trip on Dom = Fuse(id,id): @F⁻¹ ∘ F ≈ id@.
checkFmoveOuter111 :: Bool
checkFmoveOuter111 =
  let dom =
        fuseFTreesTerm
          @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
          @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
          (idHomFTrees @('[ 'IrrepTree 1]))
          (idHomFTrees @('[ 'IrrepTree 1]))
      mid = fmoveOuterHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) dom
      back = fmoveInvOuterHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) mid
   in approxHomTrees
        @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
        dom
        back

-- | 'idLeft id' is the identity on Mid.
checkIdLeftId111 :: Bool
checkIdLeftId111 =
  let mid =
        fmoveOuterHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) $
          fuseFTreesTerm
            @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
            @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
            (idHomFTrees @('[ 'IrrepTree 1]))
            (idHomFTrees @('[ 'IrrepTree 1]))
      mid' =
        idLeft
          @('[ 'IrrepTree 1])
          @('[ 'IrrepTree 1])
          @(FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
          id
          mid
   in approxHomTrees
        @(FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])))
        mid
        mid'
