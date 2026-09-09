{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Concrete leaf/Hom spines and term-level smokes for symbolic SU(2).
-- Spines are spelled as 'FuseRep' / ''I' / ''Atom' compositions (no alias layer).
module Hom.Smoke
  ( fmoveTrees111, fmoveInvTrees111
  , fmoveTrees000, fmoveInvTrees000
  , fmoveTrees110, fmoveInvTrees110
  , fmoveTrees112, fmoveInvTrees112
  , fuseMapRightFinv111
  , fillRepVScaled
  , cupTensorIdHomI1
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
  , checkFuseMapLeftId111
  ) where

import Control.Category.Constrained.Prelude (Category (..), (.), id)
import Data.Complex (Complex ((:+)), conjugate, magnitude, realPart)
import Data.VectorSpace (InnerSpace ((<.>)), (^-^))
import qualified Data.Vector.Storable as VS
import qualified Fusion.Obj as FObj
import Hom.Core
import Hom.Expr
import Hom.FMove
import Hom.RepV
import Hom.Singletons
import Hom.TypeLevel
import GHC.TypeLits (KnownNat)
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static (konst)

import Prelude hiding (id, (.))

-- | Triple-leaf F-move via 'CanFmoveTrees' (@½⊗½⊗½@).
fmoveTrees111
  :: RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1])
  -> RepV (FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 1]))
fmoveTrees111 = fmoveTrees @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1])

fmoveInvTrees111
  :: RepV (FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 1]))
  -> RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1])
fmoveInvTrees111 = fmoveInvTrees @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1])

fmoveTrees000
  :: RepV (FuseRep (FuseRep '[ 'I 0] '[ 'I 0]) '[ 'I 0])
  -> RepV (FuseRep '[ 'I 0] (FuseRep '[ 'I 0] '[ 'I 0]))
fmoveTrees000 = fmoveTrees @('[ 'I 0]) @('[ 'I 0]) @('[ 'I 0])

fmoveInvTrees000
  :: RepV (FuseRep '[ 'I 0] (FuseRep '[ 'I 0] '[ 'I 0]))
  -> RepV (FuseRep (FuseRep '[ 'I 0] '[ 'I 0]) '[ 'I 0])
fmoveInvTrees000 = fmoveInvTrees @('[ 'I 0]) @('[ 'I 0]) @('[ 'I 0])

fmoveTrees110
  :: RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 0])
  -> RepV (FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 0]))
fmoveTrees110 = fmoveTrees @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 0])

fmoveInvTrees110
  :: RepV (FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 0]))
  -> RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 0])
fmoveInvTrees110 = fmoveInvTrees @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 0])

fmoveTrees112
  :: RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2])
  -> RepV (FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 2]))
fmoveTrees112 = fmoveTrees @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 2])

fmoveInvTrees112
  :: RepV (FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 2]))
  -> RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2])
fmoveInvTrees112 = fmoveInvTrees @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 2])

-- | @Fuse(id, F-inv)@ on Mid — instance of 'fuseMapRight'.
fuseMapRightFinv111
  :: RepV (FuseRep '[ 'I 1] (FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 1])))
  -> RepV (FuseRep '[ 'I 1] (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1]))
fuseMapRightFinv111 =
  fuseMapRight
    @('[ 'I 1])
    @(FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 1]))
    @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1])
    fmoveInvTrees111

-- | Fill a spine with scaled ones (deterministic nested-F sample).
fillRepVScaled
  :: forall ts
   . KnownFTrees ts
  => RepV ts
fillRepVScaled = go 0 (fTreesSing @ts)
  where
    go :: Int -> SFTrees ts' -> RepV ts'
    go _ SFTreesNil = RNil
    go i (SFTreesCons t rest) =
      case t of
        SI {} ->
          RCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)
        SFrom {} ->
          RCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)

cupTensorIdHomI1
  :: RepV
       ( FuseRep
           '[ 'I 1]
           (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1])
       )
  -> RepV (FuseRep '[ 'I 1] (FuseRep Unit '[ 'I 1]))
cupTensorIdHomI1 = cupTensorIdHom @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1])

-- | Approx equality on Hom / association spines (expanded spine-order flat).
approxHomTrees
  :: forall ts
   . KnownFTrees ts
  => RepV ts
  -> RepV ts
  -> Bool
approxHomTrees u v =
  let bu = repVToExpandedFlat @ts u
      bv = repVToExpandedFlat @ts v
      err =
        VS.sum $
          VS.zipWith
            (\x y -> let d = x - y in realPart (d * conjugate d))
            bu
            bv
   in err < 1e-10

approxHom11
  :: RepV (FuseRep '[ 'I 1] '[ 'I 1])
  -> RepV (FuseRep '[ 'I 1] '[ 'I 1])
  -> Bool
approxHom11 = approxHomTrees @(FuseRep '[ 'I 1] '[ 'I 1])

-- | Tree F round-trip on @½⊗½⊗½@ (@F⁻¹ ∘ F ≈ id@).
checkFmoveTrees111
  :: RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1]) -> Bool
checkFmoveTrees111 tv =
  approxRepV
    @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1])
    tv
    (fmoveInvTrees111 (fmoveTrees111 tv))

-- | Tree F round-trip on @½⊗½⊗0@.
checkFmoveTrees110
  :: RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 0]) -> Bool
checkFmoveTrees110 tv =
  approxRepV
    @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 0])
    tv
    (fmoveInvTrees110 (fmoveTrees110 tv))

-- | Tree F round-trip on @½⊗½⊗1@.
checkFmoveTrees112
  :: RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2]) -> Bool
checkFmoveTrees112 tv =
  approxRepV
    @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2])
    tv
    (fmoveInvTrees112 (fmoveTrees112 tv))

-- | Round-trip only: works for any atom-leaf triple.
checkFmoveTreesLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownFTrees ( FuseRep (FuseRep '[ 'I ja] '[ 'I jb]) '[ 'I jc] )
     , KnownFTrees ( FuseRep '[ 'I ja] (FuseRep '[ 'I jb] '[ 'I jc]) )
     )
  => RepV ( FuseRep (FuseRep '[ 'I ja] '[ 'I jb]) '[ 'I jc] )
  -> Bool
checkFmoveTreesLeaves tv =
  let rt =
        fmoveInvTrees @('[ 'I ja]) @('[ 'I jb]) @('[ 'I jc])
          (fmoveTrees @('[ 'I ja]) @('[ 'I jb]) @('[ 'I jc]) tv)
   in approxRepV
        @( FuseRep (FuseRep '[ 'I ja] '[ 'I jb]) '[ 'I jc] )
        tv
        rt

-- | 'unitor' on @Unit ⊗ I½@: payload round-trip.
checkUnitorI1 :: Bool
checkUnitorI1 =
  let u =
        RCons @('From 1 '( 'I 0, 'I 1)) (konst 0.42) RNil
          :: RepV (FuseRep Unit '[ 'I 1])
      v = unitor @('[ 'I 1]) u
   in case repVToV @('[ 'I 1]) v of
        x ->
          let d = x ^-^ konst 0.42
           in magnitude (d <.> d) < 1e-18

-- | 'unitorHom' = 'fuseMapRight' 'unitor' on after-cup leaf-½ spine.
checkUnitorHom11 :: Bool
checkUnitorHom11 =
  let mid =
        RCons @('From 0 '( 'I 1, 'From 1 '( 'I 0, 'I 1))) (konst 0.3) $
          RCons @('From 2 '( 'I 1, 'From 1 '( 'I 0, 'I 1))) (konst 0.7) RNil
      out = unitorHom @('[ 'I 1]) @('[ 'I 1]) mid
   in approxHom11 out $
        RCons @('From 0 '( 'I 1, 'I 1)) (konst 0.3) $
          RCons @('From 2 '( 'I 1, 'I 1)) (konst 0.7) RNil

-- | Mac Lane 'cup' on leaf Hom: singlet × FS·dim (@0 → 1@, @½ → −2@, @1 → 3@).
checkCupIHom :: Bool
checkCupIHom =
  let s0 =
        case cup @('[ 'I 0]) (idHomI @0) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
      s1 =
        case cup @('[ 'I 1]) (idHomI @1) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
      s2 =
        case cup @('[ 'I 2]) (idHomI @2) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
   in magnitude (s0 - 1) < 1e-12
        && magnitude (s1 - (-2)) < 1e-12
        && magnitude (s2 - 3) < 1e-12

-- | Five-morphism 'composeHomTrees' unit laws on leaf-½.
checkComposeHomTrees111 :: Bool
checkComposeHomTrees111 =
  let f =
        RCons @('From 0 '( 'I 1, 'I 1)) (konst 0.3) $
          RCons @('From 2 '( 'I 1, 'I 1)) (konst 0.7) RNil
      idH = idHomI @1
      idid = composeHomTrees @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) idH idH
      fid = composeHomTrees @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) f idH
      idf = composeHomTrees @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) idH f
   in approxHomTrees @(FuseRep '[ 'I 1] '[ 'I 1]) idid idH
        && approxHomTrees @(FuseRep '[ 'I 1] '[ 'I 1]) fid f
        && approxHomTrees @(FuseRep '[ 'I 1] '[ 'I 1]) idf f

-- | Five-morphism compose unit laws on trivial Hom.
checkComposeHomTrees000 :: Bool
checkComposeHomTrees000 =
  let f = RCons @('From 0 '( 'I 0, 'I 0)) (konst 0.4) RNil
      idH = idHomI @0
   in approxHomTrees @(FuseRep '[ 'I 0] '[ 'I 0])
        (composeHomTrees @('[ 'I 0]) @('[ 'I 0]) @('[ 'I 0]) idH idH)
        idH
        && approxHomTrees @(FuseRep '[ 'I 0] '[ 'I 0])
          (composeHomTrees @('[ 'I 0]) @('[ 'I 0]) @('[ 'I 0]) f idH)
          f
        && approxHomTrees @(FuseRep '[ 'I 0] '[ 'I 0])
          (composeHomTrees @('[ 'I 0]) @('[ 'I 0]) @('[ 'I 0]) idH f)
          f

-- | I spin-1 Hom compose: @id∘id ≈ id@ and left/right units on multi-channel Hom.
checkComposeHomTrees222 :: Bool
checkComposeHomTrees222 =
  let f =
        RCons @('From 0 '( 'I 2, 'I 2)) (konst 0.2) $
          RCons @('From 2 '( 'I 2, 'I 2)) (konst 0.3) $
            RCons @('From 4 '( 'I 2, 'I 2)) (konst 0.5) RNil
      idH = idHomI @2
      idid = composeHomTrees @('[ 'I 2]) @('[ 'I 2]) @('[ 'I 2]) idH idH
      fid = composeHomTrees @('[ 'I 2]) @('[ 'I 2]) @('[ 'I 2]) f idH
      idf = composeHomTrees @('[ 'I 2]) @('[ 'I 2]) @('[ 'I 2]) idH f
   in approxHomTrees @(FuseRep '[ 'I 2] '[ 'I 2]) idid idH
        && approxHomTrees @(FuseRep '[ 'I 2] '[ 'I 2]) fid f
        && approxHomTrees @(FuseRep '[ 'I 2] '[ 'I 2]) idf f

-- | Polymorphic leaf F + outer Hom: unit laws on @tj = 3@.
checkComposeHomTrees333 :: Bool
checkComposeHomTrees333 =
  let f =
        RCons @('From 0 '( 'I 3, 'I 3)) (konst 0.1) $
          RCons @('From 2 '( 'I 3, 'I 3)) (konst 0.2) $
            RCons @('From 4 '( 'I 3, 'I 3)) (konst 0.3) $
              RCons @('From 6 '( 'I 3, 'I 3)) (konst 0.4) RNil
      idH = idHomI @3
      idid = composeHomTrees @('[ 'I 3]) @('[ 'I 3]) @('[ 'I 3]) idH idH
      fid = composeHomTrees @('[ 'I 3]) @('[ 'I 3]) @('[ 'I 3]) f idH
      idf = composeHomTrees @('[ 'I 3]) @('[ 'I 3]) @('[ 'I 3]) idH f
   in approxHomTrees @(FuseRep '[ 'I 3] '[ 'I 3]) idid idH
        && approxHomTrees @(FuseRep '[ 'I 3] '[ 'I 3]) fid f
        && approxHomTrees @(FuseRep '[ 'I 3] '[ 'I 3]) idf f

-- | Unequal-leaf compose @½ → 1 → ½@: left/right units on @FuseRep ½ 1@.
checkComposeHomTrees121 :: Bool
checkComposeHomTrees121 =
  let f :: RepV (FuseRep '[ 'I 1] '[ 'I 2])
      f =
        RCons @('From 1 '( 'I 1, 'I 2)) (konst 0.3) $
          RCons @('From 3 '( 'I 1, 'I 2)) (konst 0.7) RNil
      id1 = idHomI @1
      id2 = idHomI @2
      -- f ∘ id₁  and  id₂ ∘ f
      idf = composeHomTrees @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 2]) id1 f
      fid = composeHomTrees @('[ 'I 1]) @('[ 'I 2]) @('[ 'I 2]) f id2
   in approxHomTrees @(FuseRep '[ 'I 1] '[ 'I 2]) idf f
        && approxHomTrees @(FuseRep '[ 'I 1] '[ 'I 2]) fid f

-- | Atom-leaf F round-trip for @½⊗1⊗½@ via polymorphic 'CanFmoveTrees'.
checkFmoveTreesLeaves121 :: Bool
checkFmoveTreesLeaves121 =
  let assocL = fillRepVScaled @( FuseRep (FuseRep '[ 'I 1] '[ 'I 2]) '[ 'I 1] )
      rt =
        fmoveInvTrees @('[ 'I 1]) @('[ 'I 2]) @('[ 'I 1])
          (fmoveTrees @('[ 'I 1]) @('[ 'I 2]) @('[ 'I 1]) assocL)
   in approxHomTrees @( FuseRep (FuseRep '[ 'I 1] '[ 'I 2]) '[ 'I 1] ) assocL rt

-- | Nested F: Hom⊗leaf⊗leaf (@(½*⊗½) ⊗ ½ ⊗ ½@) round-trip via channel-keyed F.
checkFmoveHomLeft111 :: Bool
checkFmoveHomLeft111 =
  let assocL =
        fillRepVScaled
          @( FuseRep (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1]) '[ 'I 1] )
      rt =
        fmoveInvTreesHomLeft @1 @1 @1
          (fmoveTreesHomLeft @1 @1 @1 assocL)
   in approxHomTrees
        @( FuseRep (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1]) '[ 'I 1] )
        assocL
        rt

-- | 'HomFused' packaging unit laws on spin-1 via 'composeHomFused'.
checkHomFusedCategory222 :: Bool
checkHomFusedCategory222 =
  let f :: HomFused ('FObj.Atom 2) ('FObj.Atom 2)
      f =
        HomFused $
          RCons @('From 0 '( 'I 2, 'I 2)) (konst 0.2) $
            RCons @('From 2 '( 'I 2, 'I 2)) (konst 0.3) $
              RCons @('From 4 '( 'I 2, 'I 2)) (konst 0.5) RNil
      idT = HomFused (idHomFusedVal @('FObj.Atom 2))
      HomFused idid =
        composeHomFused @('FObj.Atom 2) @('FObj.Atom 2) @('FObj.Atom 2) idT idT
      HomFused fid =
        composeHomFused @('FObj.Atom 2) @('FObj.Atom 2) @('FObj.Atom 2) idT f
      HomFused idf =
        composeHomFused @('FObj.Atom 2) @('FObj.Atom 2) @('FObj.Atom 2) f idT
   in approxHomTrees @(FuseRep '[ 'I 2] '[ 'I 2]) idid (idHomI @2)
        && approxHomTrees @(FuseRep '[ 'I 2] '[ 'I 2]) fid (unHomFused f)
        && approxHomTrees @(FuseRep '[ 'I 2] '[ 'I 2]) idf (unHomFused f)

-- | 'HomFused' unit laws on @tj = 3@ via polymorphic 'KnownHomFused' / 'idHomI'.
checkHomFusedCategory333 :: Bool
checkHomFusedCategory333 =
  let f :: HomFused ('FObj.Atom 3) ('FObj.Atom 3)
      f =
        HomFused $
          RCons @('From 0 '( 'I 3, 'I 3)) (konst 0.1) $
            RCons @('From 2 '( 'I 3, 'I 3)) (konst 0.2) $
              RCons @('From 4 '( 'I 3, 'I 3)) (konst 0.3) $
                RCons @('From 6 '( 'I 3, 'I 3)) (konst 0.4) RNil
      idT = HomFused (idHomFusedVal @('FObj.Atom 3))
      HomFused idid =
        composeHomFused @('FObj.Atom 3) @('FObj.Atom 3) @('FObj.Atom 3) idT idT
      HomFused fid =
        composeHomFused @('FObj.Atom 3) @('FObj.Atom 3) @('FObj.Atom 3) idT f
      HomFused idf =
        composeHomFused @('FObj.Atom 3) @('FObj.Atom 3) @('FObj.Atom 3) f idT
   in approxHomTrees @(FuseRep '[ 'I 3] '[ 'I 3]) idid (idHomFusedVal @('FObj.Atom 3))
        && approxHomTrees @(FuseRep '[ 'I 3] '[ 'I 3]) fid (unHomFused f)
        && approxHomTrees @(FuseRep '[ 'I 3] '[ 'I 3]) idf (unHomFused f)

-- | 'HomInter' unit laws on spin-½ via embed → 'composeHomTrees' → filter.
checkHomInterCategory111 :: Bool
checkHomInterCategory111 =
  let f :: HomInter ('FObj.Atom 1) ('FObj.Atom 1)
      f =
        HomInter $
          scaleRepV
            @(FilterTrivial (FuseRep '[ 'I 1] '[ 'I 1]))
            (0.3 :+ 0)
            (idHomInterVal @('FObj.Atom 1))
      idT = HomInter (idHomInterVal @('FObj.Atom 1))
      HomInter idid =
        composeHomInter @('FObj.Atom 1) @('FObj.Atom 1) @('FObj.Atom 1) idT idT
      HomInter fid =
        composeHomInter @('FObj.Atom 1) @('FObj.Atom 1) @('FObj.Atom 1) idT f
      HomInter idf =
        composeHomInter @('FObj.Atom 1) @('FObj.Atom 1) @('FObj.Atom 1) f idT
   in approxHomTrees
        @(FilterTrivial (FuseRep '[ 'I 1] '[ 'I 1]))
        idid
        (idHomInterVal @('FObj.Atom 1))
        && approxHomTrees
          @(FilterTrivial (FuseRep '[ 'I 1] '[ 'I 1]))
          fid
          (unHomInter f)
        && approxHomTrees
          @(FilterTrivial (FuseRep '[ 'I 1] '[ 'I 1]))
          idf
          (unHomInter f)

-- | Forgetful densify of fused id matches unfused id on spin-½.
checkForgetHomFusedId111 :: Bool
checkForgetHomFusedId111 =
  let fusedId = id :: HomFused ('FObj.Atom 1) ('FObj.Atom 1)
      unfusedId = id :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
      forgotten = forgetHomFusedHalf fusedId
   in approxHomUnfused forgotten unfusedId

-- | Forgetful densify is a functor on the intertwiner (singlet) sector:
-- @forget(g ∘_Inter f) = forget(g) ∘_Unfused forget(f)@ for scaled ids.
checkForgetHomInterCompose111 :: Bool
checkForgetHomInterCompose111 =
  let f :: HomInter ('FObj.Atom 1) ('FObj.Atom 1)
      f =
        HomInter $
          scaleRepV
            @(FilterTrivial (FuseRep '[ 'I 1] '[ 'I 1]))
            (0.4 :+ 0)
            (idHomInterVal @('FObj.Atom 1))
      g :: HomInter ('FObj.Atom 1) ('FObj.Atom 1)
      g =
        HomInter $
          scaleRepV
            @(FilterTrivial (FuseRep '[ 'I 1] '[ 'I 1]))
            ((-0.5) :+ 0)
            (idHomInterVal @('FObj.Atom 1))
      -- Embed intertwiners to HomFused, densify, compare compose both ways.
      emb (HomInter t) =
        HomFused (embedTrivialRepV @(FuseRep '[ 'I 1] '[ 'I 1]) t)
      lhs =
        forgetHomFusedHalf
          (composeHomFused
             @('FObj.Atom 1)
             @('FObj.Atom 1)
             @('FObj.Atom 1)
             (emb g)
             (emb f))
      rhs = forgetHomFusedHalf (emb g) . forgetHomFusedHalf (emb f)
   in approxHomUnfused lhs rhs

approxHomUnfused
  :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
  -> HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
  -> Bool
approxHomUnfused (HomUnfused u) (HomUnfused v) =
  let du = toArray u
      dv = toArray v
   in VS.length du == VS.length dv
        && VS.and (VS.zipWith (\x y -> magnitude (x - y) < 1e-9) du dv)

-- | Spin-1 leaf smoke: atom F + outer Hom F round-trips.
checkI2FmoveSmoke :: Bool
checkI2FmoveSmoke =
  let assocL = fillRepVScaled @( FuseRep (FuseRep '[ 'I 2] '[ 'I 2]) '[ 'I 2] )
      assocOk =
        approxHomTrees @( FuseRep (FuseRep '[ 'I 2] '[ 'I 2]) '[ 'I 2] ) assocL $
          fmoveInvTrees @('[ 'I 2]) @('[ 'I 2]) @('[ 'I 2])
            (fmoveTrees @('[ 'I 2]) @('[ 'I 2]) @('[ 'I 2]) assocL)
      idH = idHomI @2
      dom =
        fuseRepTerm
          @(FuseRep '[ 'I 2] '[ 'I 2])
          @(FuseRep '[ 'I 2] '[ 'I 2])
          idH
          idH
      mid = fmoveOuterHom @('[ 'I 2]) @('[ 'I 2]) @('[ 'I 2]) dom
      back = fmoveInvOuterHom @('[ 'I 2]) @('[ 'I 2]) @('[ 'I 2]) mid
   in assocOk
        && approxHomTrees
          @( FuseRep (FuseRep '[ 'I 2] '[ 'I 2]) (FuseRep '[ 'I 2] '[ 'I 2]) )
          dom
          back

-- | Outer F round-trip on Dom = Fuse(id,id): @F⁻¹ ∘ F ≈ id@.
checkFmoveOuter111 :: Bool
checkFmoveOuter111 =
  let dom =
        fuseRepTerm
          @(FuseRep '[ 'I 1] '[ 'I 1])
          @(FuseRep '[ 'I 1] '[ 'I 1])
          (idHomI @1)
          (idHomI @1)
      mid = fmoveOuterHom @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) dom
      back = fmoveInvOuterHom @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) mid
   in approxHomTrees
        @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) (FuseRep '[ 'I 1] '[ 'I 1]))
        dom
        back

-- | 'fuseMapLeft id' is the identity on Mid.
checkFuseMapLeftId111 :: Bool
checkFuseMapLeftId111 =
  let mid =
        fmoveOuterHom @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) $
          fuseRepTerm
            @(FuseRep '[ 'I 1] '[ 'I 1])
            @(FuseRep '[ 'I 1] '[ 'I 1])
            (idHomI @1)
            (idHomI @1)
      mid' =
        fuseMapLeft
          @('[ 'I 1])
          @('[ 'I 1])
          @(FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 1]))
          id
          mid
   in approxHomTrees
        @(FuseRep '[ 'I 1] (FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 1])))
        mid
        mid'
