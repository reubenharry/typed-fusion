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
module Experiments.Symbolic.Smoke
  ( module Experiments.Symbolic.Aliases
  , fmoveTrees111, fmoveInvTrees111
  , fmoveTrees000, fmoveInvTrees000
  , fmoveTrees110, fmoveInvTrees110
  , fmoveTrees112, fmoveInvTrees112
  , fuseMapRightFinv111
  , fillRepVScaled
  , cupTensorIdHomBare1
  , approxHomTrees
  , approxHom11
  , checkFmoveTrees111
  , checkFmoveTrees110
  , checkFmoveTrees112
  , checkFmoveTreesLeaves
  , checkUnitorBare1
  , checkUnitorHom11
  , checkCupBareHom
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
  , checkBare2FmoveSmoke
  , checkFmoveOuter111
  , checkFuseMapLeftId111
  ) where

import Control.Category.Constrained.Prelude (Category (..), (.), id)
import Data.Complex (Complex ((:+)), conjugate, magnitude, realPart)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (InnerSpace ((<.>)), (^-^))
import qualified Data.Vector.Storable as VS
import Experiments.Symbolic.Aliases
import Experiments.Symbolic.Core
import Experiments.Symbolic.Expr
import Experiments.Symbolic.FMove
import Experiments.Symbolic.RepV
import Experiments.Symbolic.Singletons
import Experiments.Symbolic.TypeLevel
import GHC.TypeLits (KnownNat)
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static (konst)

import Prelude hiding (id, (.))

-- | Triple-leaf F-move via 'CanFmoveTrees'.
fmoveTrees111 :: RepV AssocL111 -> RepV AssocR111
fmoveTrees111 = fmoveTrees @Bare1 @Bare1 @Bare1

fmoveInvTrees111 :: RepV AssocR111 -> RepV AssocL111
fmoveInvTrees111 = fmoveInvTrees @Bare1 @Bare1 @Bare1

fmoveTrees000 :: RepV AssocL000 -> RepV AssocR000
fmoveTrees000 = fmoveTrees @Bare0 @Bare0 @Bare0

fmoveInvTrees000 :: RepV AssocR000 -> RepV AssocL000
fmoveInvTrees000 = fmoveInvTrees @Bare0 @Bare0 @Bare0

fmoveTrees110 :: RepV AssocL110 -> RepV AssocR110
fmoveTrees110 = fmoveTrees @Bare1 @Bare1 @Bare0

fmoveInvTrees110 :: RepV AssocR110 -> RepV AssocL110
fmoveInvTrees110 = fmoveInvTrees @Bare1 @Bare1 @Bare0

fmoveTrees112 :: RepV AssocL112 -> RepV AssocR112
fmoveTrees112 = fmoveTrees @Bare1 @Bare1 @Bare2

fmoveInvTrees112 :: RepV AssocR112 -> RepV AssocL112
fmoveInvTrees112 = fmoveInvTrees @Bare1 @Bare1 @Bare2

-- | @Fuse(id, F-inv)@ on Mid — instance of 'fuseMapRight'.
fuseMapRightFinv111 :: RepV Mid111 -> RepV CupR111
fuseMapRightFinv111 =
  fuseMapRight @Bare1 @AssocR111 @AssocL111 fmoveInvTrees111

-- | Fill a spine with scaled ones (deterministic nested-F sample).
fillRepVScaled
  :: forall ts
   . KnownRep ts
  => RepV ts
fillRepVScaled = go 0 (repSing @ts)
  where
    go :: Int -> SRep ts' -> RepV ts'
    go _ SRepNil = RNil
    go i (SRepCons t rest) =
      case t of
        SBare {} ->
          RCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)
        SFrom {} ->
          RCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)

cupTensorIdHomBare1
  :: RepV (FuseRep Bare1 (FuseRep Hom11 Bare1))
  -> RepV (FuseRep Bare1 (FuseRep Unit Bare1))
cupTensorIdHomBare1 = cupTensorIdHom @Bare1 @Bare1 @Bare1

-- | Approx equality on Hom / association spines (expanded spine-order flat).
approxHomTrees
  :: forall ts
   . KnownRep ts
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

approxHom11 :: RepV Hom11 -> RepV Hom11 -> Bool
approxHom11 = approxHomTrees @Hom11

-- | Tree F round-trip on @½⊗½⊗½@ (@F⁻¹ ∘ F ≈ id@).
checkFmoveTrees111 :: RepV AssocL111 -> Bool
checkFmoveTrees111 tv =
  approxRepV @AssocL111 tv (fmoveInvTrees111 (fmoveTrees111 tv))

-- | Tree F round-trip on @½⊗½⊗0@.
checkFmoveTrees110 :: RepV AssocL110 -> Bool
checkFmoveTrees110 tv =
  approxRepV @AssocL110 tv (fmoveInvTrees110 (fmoveTrees110 tv))

-- | Tree F round-trip on @½⊗½⊗1@.
checkFmoveTrees112 :: RepV AssocL112 -> Bool
checkFmoveTrees112 tv =
  approxRepV @AssocL112 tv (fmoveInvTrees112 (fmoveTrees112 tv))

-- | Round-trip only: works for any atom-leaf triple.
checkFmoveTreesLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) '[ 'Bare jc] )
     , KnownRep ( FuseRep '[ 'Bare ja] (FuseRep '[ 'Bare jb] '[ 'Bare jc]) )
     )
  => RepV ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) '[ 'Bare jc] )
  -> Bool
checkFmoveTreesLeaves tv =
  let rt =
        fmoveInvTrees @('[ 'Bare ja]) @('[ 'Bare jb]) @('[ 'Bare jc])
          (fmoveTrees @('[ 'Bare ja]) @('[ 'Bare jb]) @('[ 'Bare jc]) tv)
   in approxRepV
        @( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) '[ 'Bare jc] )
        tv
        rt

-- | 'unitor' on @Unit ⊗ Bare½@: payload round-trip.
checkUnitorBare1 :: Bool
checkUnitorBare1 =
  let u =
        RCons @('From 1 '( 'Bare 0, 'Bare 1)) (konst 0.42) RNil
          :: RepV (FuseRep Unit Bare1)
      v = unitor @Bare1 u
   in case repVToV @Bare1 v of
        x ->
          let d = x ^-^ konst 0.42
           in magnitude (d <.> d) < 1e-18

-- | 'unitorHom' = 'fuseMapRight' 'unitor' on after-cup leaf-½ spine.
checkUnitorHom11 :: Bool
checkUnitorHom11 =
  let mid =
        RCons @('From 0 '( 'Bare 1, 'From 1 '( 'Bare 0, 'Bare 1))) (konst 0.3) $
          RCons @('From 2 '( 'Bare 1, 'From 1 '( 'Bare 0, 'Bare 1))) (konst 0.7) RNil
      out = unitorHom @Bare1 @Bare1 mid
   in approxHom11 out $
        RCons @('From 0 '( 'Bare 1, 'Bare 1)) (konst 0.3) $
          RCons @('From 2 '( 'Bare 1, 'Bare 1)) (konst 0.7) RNil

-- | Mac Lane 'cup' on leaf Hom: singlet × FS·dim (@0 → 1@, @½ → −2@, @1 → 3@).
checkCupBareHom :: Bool
checkCupBareHom =
  let s0 =
        case cup @Bare0 (idHomBare @0) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
      s1 =
        case cup @Bare1 (idHomBare @1) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
      s2 =
        case cup @Bare2 (idHomBare @2) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
   in magnitude (s0 - 1) < 1e-12
        && magnitude (s1 - (-2)) < 1e-12
        && magnitude (s2 - 3) < 1e-12

-- | Five-morphism 'composeHomTrees' unit laws on leaf-½.
checkComposeHomTrees111 :: Bool
checkComposeHomTrees111 =
  let f =
        RCons @('From 0 '( 'Bare 1, 'Bare 1)) (konst 0.3) $
          RCons @('From 2 '( 'Bare 1, 'Bare 1)) (konst 0.7) RNil
      idH = idHomBare @1
      idid = composeHomTrees @Bare1 @Bare1 @Bare1 idH idH
      fid = composeHomTrees @Bare1 @Bare1 @Bare1 f idH
      idf = composeHomTrees @Bare1 @Bare1 @Bare1 idH f
   in approxHomTrees @Hom11 idid idH
        && approxHomTrees @Hom11 fid f
        && approxHomTrees @Hom11 idf f

-- | Five-morphism compose unit laws on trivial Hom.
checkComposeHomTrees000 :: Bool
checkComposeHomTrees000 =
  let f = RCons @('From 0 '( 'Bare 0, 'Bare 0)) (konst 0.4) RNil
      idH = idHomBare @0
   in approxHomTrees @Hom00
        (composeHomTrees @Bare0 @Bare0 @Bare0 idH idH)
        idH
        && approxHomTrees @Hom00
          (composeHomTrees @Bare0 @Bare0 @Bare0 f idH)
          f
        && approxHomTrees @Hom00
          (composeHomTrees @Bare0 @Bare0 @Bare0 idH f)
          f

-- | Bare spin-1 Hom compose: @id∘id ≈ id@ and left/right units on multi-channel Hom.
checkComposeHomTrees222 :: Bool
checkComposeHomTrees222 =
  let f =
        RCons @('From 0 '( 'Bare 2, 'Bare 2)) (konst 0.2) $
          RCons @('From 2 '( 'Bare 2, 'Bare 2)) (konst 0.3) $
            RCons @('From 4 '( 'Bare 2, 'Bare 2)) (konst 0.5) RNil
      idH = idHomBare @2
      idid = composeHomTrees @Bare2 @Bare2 @Bare2 idH idH
      fid = composeHomTrees @Bare2 @Bare2 @Bare2 f idH
      idf = composeHomTrees @Bare2 @Bare2 @Bare2 idH f
   in approxHomTrees @Hom22 idid idH
        && approxHomTrees @Hom22 fid f
        && approxHomTrees @Hom22 idf f

-- | Polymorphic leaf F + outer Hom: unit laws on @tj = 3@.
checkComposeHomTrees333 :: Bool
checkComposeHomTrees333 =
  let f =
        RCons @('From 0 '( 'Bare 3, 'Bare 3)) (konst 0.1) $
          RCons @('From 2 '( 'Bare 3, 'Bare 3)) (konst 0.2) $
            RCons @('From 4 '( 'Bare 3, 'Bare 3)) (konst 0.3) $
              RCons @('From 6 '( 'Bare 3, 'Bare 3)) (konst 0.4) RNil
      idH = idHomBare @3
      idid = composeHomTrees @Bare3 @Bare3 @Bare3 idH idH
      fid = composeHomTrees @Bare3 @Bare3 @Bare3 f idH
      idf = composeHomTrees @Bare3 @Bare3 @Bare3 idH f
   in approxHomTrees @Hom33 idid idH
        && approxHomTrees @Hom33 fid f
        && approxHomTrees @Hom33 idf f

-- | Unequal-leaf compose @½ → 1 → ½@: left/right units on 'Hom12'.
checkComposeHomTrees121 :: Bool
checkComposeHomTrees121 =
  let f :: RepV Hom12
      f =
        RCons @('From 1 '( 'Bare 1, 'Bare 2)) (konst 0.3) $
          RCons @('From 3 '( 'Bare 1, 'Bare 2)) (konst 0.7) RNil
      id1 = idHomBare @1
      id2 = idHomBare @2
      -- f ∘ id₁  and  id₂ ∘ f
      idf = composeHomTrees @Bare1 @Bare1 @Bare2 id1 f
      fid = composeHomTrees @Bare1 @Bare2 @Bare2 f id2
   in approxHomTrees @Hom12 idf f && approxHomTrees @Hom12 fid f

-- | Atom-leaf F round-trip for @½⊗1⊗½@ via polymorphic 'CanFmoveTrees'.
checkFmoveTreesLeaves121 :: Bool
checkFmoveTreesLeaves121 =
  let assocL = fillRepVScaled @( FuseRep (FuseRep Bare1 Bare2) Bare1 )
      rt =
        fmoveInvTrees @Bare1 @Bare2 @Bare1
          (fmoveTrees @Bare1 @Bare2 @Bare1 assocL)
   in approxHomTrees @( FuseRep (FuseRep Bare1 Bare2) Bare1 ) assocL rt

-- | Nested F: Hom⊗leaf⊗leaf (@Hom11 ⊗ ½ ⊗ ½@) round-trip via channel-keyed F.
checkFmoveHomLeft111 :: Bool
checkFmoveHomLeft111 =
  let assocL = fillRepVScaled @( FuseRep (FuseRep Hom11 Bare1) Bare1 )
      rt =
        fmoveInvTreesHomLeft @1 @1 @1
          (fmoveTreesHomLeft @1 @1 @1 assocL)
   in approxHomTrees @( FuseRep (FuseRep Hom11 Bare1) Bare1 ) assocL rt

-- | 'HomFused' packaging unit laws on spin-1 via 'composeHomFused'.
checkHomFusedCategory222 :: Bool
checkHomFusedCategory222 =
  let f :: HomFused Atom2 Atom2
      f =
        HomFused $
          RCons @('From 0 '( 'Bare 2, 'Bare 2)) (konst 0.2) $
            RCons @('From 2 '( 'Bare 2, 'Bare 2)) (konst 0.3) $
              RCons @('From 4 '( 'Bare 2, 'Bare 2)) (konst 0.5) RNil
      idT = HomFused (idHomFusedVal @Atom2)
      HomFused idid = composeHomFused @Atom2 @Atom2 @Atom2 idT idT
      HomFused fid = composeHomFused @Atom2 @Atom2 @Atom2 idT f
      HomFused idf = composeHomFused @Atom2 @Atom2 @Atom2 f idT
   in approxHomTrees @Hom22 idid (idHomBare @2)
        && approxHomTrees @Hom22 fid (unHomFused f)
        && approxHomTrees @Hom22 idf (unHomFused f)

-- | 'HomFused' unit laws on @tj = 3@ via polymorphic 'KnownHomFused' / 'idHomBare'.
checkHomFusedCategory333 :: Bool
checkHomFusedCategory333 =
  let f :: HomFused Atom3 Atom3
      f =
        HomFused $
          RCons @('From 0 '( 'Bare 3, 'Bare 3)) (konst 0.1) $
            RCons @('From 2 '( 'Bare 3, 'Bare 3)) (konst 0.2) $
              RCons @('From 4 '( 'Bare 3, 'Bare 3)) (konst 0.3) $
                RCons @('From 6 '( 'Bare 3, 'Bare 3)) (konst 0.4) RNil
      idT = HomFused (idHomFusedVal @Atom3)
      HomFused idid = composeHomFused @Atom3 @Atom3 @Atom3 idT idT
      HomFused fid = composeHomFused @Atom3 @Atom3 @Atom3 idT f
      HomFused idf = composeHomFused @Atom3 @Atom3 @Atom3 f idT
   in approxHomTrees @Hom33 idid (idHomFusedVal @Atom3)
        && approxHomTrees @Hom33 fid (unHomFused f)
        && approxHomTrees @Hom33 idf (unHomFused f)

-- | 'HomInter' unit laws on spin-½ via embed → 'composeHomTrees' → filter.
checkHomInterCategory111 :: Bool
checkHomInterCategory111 =
  let f :: HomInter Atom1 Atom1
      f =
        HomInter $
          scaleRepV @Inter11 (0.3 :+ 0) (idHomInterVal @Atom1)
      idT = HomInter (idHomInterVal @Atom1)
      HomInter idid = composeHomInter @Atom1 @Atom1 @Atom1 idT idT
      HomInter fid = composeHomInter @Atom1 @Atom1 @Atom1 idT f
      HomInter idf = composeHomInter @Atom1 @Atom1 @Atom1 f idT
   in approxHomTrees @Inter11 idid (idHomInterVal @Atom1)
        && approxHomTrees @Inter11 fid (unHomInter f)
        && approxHomTrees @Inter11 idf (unHomInter f)

-- | Forgetful densify of fused id matches unfused id on spin-½.
checkForgetHomFusedId111 :: Bool
checkForgetHomFusedId111 =
  let fusedId = id :: HomFused Atom1 Atom1
      unfusedId = id :: HomUnfused Atom1 Atom1
      forgotten = forgetHomFusedHalf fusedId
   in approxHomUnfused forgotten unfusedId

-- | Forgetful densify is a functor on the intertwiner (singlet) sector:
-- @forget(g ∘_Inter f) = forget(g) ∘_Unfused forget(f)@ for scaled ids.
checkForgetHomInterCompose111 :: Bool
checkForgetHomInterCompose111 =
  let f :: HomInter Atom1 Atom1
      f = HomInter $ scaleRepV @Inter11 (0.4 :+ 0) (idHomInterVal @Atom1)
      g :: HomInter Atom1 Atom1
      g = HomInter $ scaleRepV @Inter11 ((-0.5) :+ 0) (idHomInterVal @Atom1)
      -- Embed intertwiners to HomFused, densify, compare compose both ways.
      emb (HomInter t) =
        HomFused (embedTrivialRepV @(FuseRep Bare1 Bare1) t)
      lhs =
        forgetHomFusedHalf
          (composeHomFused @Atom1 @Atom1 @Atom1 (emb g) (emb f))
      rhs = forgetHomFusedHalf (emb g) . forgetHomFusedHalf (emb f)
   in approxHomUnfused lhs rhs

approxHomUnfused
  :: HomUnfused Atom1 Atom1
  -> HomUnfused Atom1 Atom1
  -> Bool
approxHomUnfused (HomUnfused u) (HomUnfused v) =
  let du = toArray u
      dv = toArray v
   in VS.length du == VS.length dv
        && VS.and (VS.zipWith (\x y -> magnitude (x - y) < 1e-9) du dv)

-- | Spin-1 leaf smoke: atom F + outer Hom F round-trips.
checkBare2FmoveSmoke :: Bool
checkBare2FmoveSmoke =
  let assocL = fillRepVScaled @( FuseRep (FuseRep Bare2 Bare2) Bare2 )
      assocOk =
        approxHomTrees @( FuseRep (FuseRep Bare2 Bare2) Bare2 ) assocL $
          fmoveInvTrees @Bare2 @Bare2 @Bare2 (fmoveTrees @Bare2 @Bare2 @Bare2 assocL)
      idH = idHomBare @2
      dom = fuseRepTerm @Hom22 @Hom22 idH idH
      mid = fmoveOuterHom @Bare2 @Bare2 @Bare2 dom
      back = fmoveInvOuterHom @Bare2 @Bare2 @Bare2 mid
   in assocOk && approxHomTrees @( FuseRep (FuseRep Bare2 Bare2) Hom22 ) dom back

-- | Outer F round-trip on Dom = Fuse(id,id): @F⁻¹ ∘ F ≈ id@.
checkFmoveOuter111 :: Bool
checkFmoveOuter111 =
  let dom = fuseRepTerm @Hom11 @Hom11 (idHomBare @1) (idHomBare @1)
      mid = fmoveOuterHom @Bare1 @Bare1 @Bare1 dom
      back = fmoveInvOuterHom @Bare1 @Bare1 @Bare1 mid
   in approxHomTrees @Dom111 dom back

-- | 'fuseMapLeft id' is the identity on Mid.
checkFuseMapLeftId111 :: Bool
checkFuseMapLeftId111 =
  let mid =
        fmoveOuterHom @Bare1 @Bare1 @Bare1 $
          fuseRepTerm @Hom11 @Hom11 (idHomBare @1) (idHomBare @1)
      mid' = fuseMapLeft @Bare1 @Bare1 @AssocR111 id mid
   in approxHomTrees @Mid111 mid mid'

