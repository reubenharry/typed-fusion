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
fmoveTrees111 = fmoveTrees @I1 @I1 @I1

fmoveInvTrees111 :: RepV AssocR111 -> RepV AssocL111
fmoveInvTrees111 = fmoveInvTrees @I1 @I1 @I1

fmoveTrees000 :: RepV AssocL000 -> RepV AssocR000
fmoveTrees000 = fmoveTrees @I0 @I0 @I0

fmoveInvTrees000 :: RepV AssocR000 -> RepV AssocL000
fmoveInvTrees000 = fmoveInvTrees @I0 @I0 @I0

fmoveTrees110 :: RepV AssocL110 -> RepV AssocR110
fmoveTrees110 = fmoveTrees @I1 @I1 @I0

fmoveInvTrees110 :: RepV AssocR110 -> RepV AssocL110
fmoveInvTrees110 = fmoveInvTrees @I1 @I1 @I0

fmoveTrees112 :: RepV AssocL112 -> RepV AssocR112
fmoveTrees112 = fmoveTrees @I1 @I1 @I2

fmoveInvTrees112 :: RepV AssocR112 -> RepV AssocL112
fmoveInvTrees112 = fmoveInvTrees @I1 @I1 @I2

-- | @Fuse(id, F-inv)@ on Mid — instance of 'fuseMapRight'.
fuseMapRightFinv111 :: RepV Mid111 -> RepV CupR111
fuseMapRightFinv111 =
  fuseMapRight @I1 @AssocR111 @AssocL111 fmoveInvTrees111

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
        SI {} ->
          RCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)
        SFrom {} ->
          RCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)

cupTensorIdHomI1
  :: RepV (FuseRep I1 (FuseRep Hom11 I1))
  -> RepV (FuseRep I1 (FuseRep Unit I1))
cupTensorIdHomI1 = cupTensorIdHom @I1 @I1 @I1

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
     , KnownRep ( FuseRep (FuseRep '[ 'I ja] '[ 'I jb]) '[ 'I jc] )
     , KnownRep ( FuseRep '[ 'I ja] (FuseRep '[ 'I jb] '[ 'I jc]) )
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
          :: RepV (FuseRep Unit I1)
      v = unitor @I1 u
   in case repVToV @I1 v of
        x ->
          let d = x ^-^ konst 0.42
           in magnitude (d <.> d) < 1e-18

-- | 'unitorHom' = 'fuseMapRight' 'unitor' on after-cup leaf-½ spine.
checkUnitorHom11 :: Bool
checkUnitorHom11 =
  let mid =
        RCons @('From 0 '( 'I 1, 'From 1 '( 'I 0, 'I 1))) (konst 0.3) $
          RCons @('From 2 '( 'I 1, 'From 1 '( 'I 0, 'I 1))) (konst 0.7) RNil
      out = unitorHom @I1 @I1 mid
   in approxHom11 out $
        RCons @('From 0 '( 'I 1, 'I 1)) (konst 0.3) $
          RCons @('From 2 '( 'I 1, 'I 1)) (konst 0.7) RNil

-- | Mac Lane 'cup' on leaf Hom: singlet × FS·dim (@0 → 1@, @½ → −2@, @1 → 3@).
checkCupIHom :: Bool
checkCupIHom =
  let s0 =
        case cup @I0 (idHomI @0) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
      s1 =
        case cup @I1 (idHomI @1) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
      s2 =
        case cup @I2 (idHomI @2) of
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
      idid = composeHomTrees @I1 @I1 @I1 idH idH
      fid = composeHomTrees @I1 @I1 @I1 f idH
      idf = composeHomTrees @I1 @I1 @I1 idH f
   in approxHomTrees @Hom11 idid idH
        && approxHomTrees @Hom11 fid f
        && approxHomTrees @Hom11 idf f

-- | Five-morphism compose unit laws on trivial Hom.
checkComposeHomTrees000 :: Bool
checkComposeHomTrees000 =
  let f = RCons @('From 0 '( 'I 0, 'I 0)) (konst 0.4) RNil
      idH = idHomI @0
   in approxHomTrees @Hom00
        (composeHomTrees @I0 @I0 @I0 idH idH)
        idH
        && approxHomTrees @Hom00
          (composeHomTrees @I0 @I0 @I0 f idH)
          f
        && approxHomTrees @Hom00
          (composeHomTrees @I0 @I0 @I0 idH f)
          f

-- | I spin-1 Hom compose: @id∘id ≈ id@ and left/right units on multi-channel Hom.
checkComposeHomTrees222 :: Bool
checkComposeHomTrees222 =
  let f =
        RCons @('From 0 '( 'I 2, 'I 2)) (konst 0.2) $
          RCons @('From 2 '( 'I 2, 'I 2)) (konst 0.3) $
            RCons @('From 4 '( 'I 2, 'I 2)) (konst 0.5) RNil
      idH = idHomI @2
      idid = composeHomTrees @I2 @I2 @I2 idH idH
      fid = composeHomTrees @I2 @I2 @I2 f idH
      idf = composeHomTrees @I2 @I2 @I2 idH f
   in approxHomTrees @Hom22 idid idH
        && approxHomTrees @Hom22 fid f
        && approxHomTrees @Hom22 idf f

-- | Polymorphic leaf F + outer Hom: unit laws on @tj = 3@.
checkComposeHomTrees333 :: Bool
checkComposeHomTrees333 =
  let f =
        RCons @('From 0 '( 'I 3, 'I 3)) (konst 0.1) $
          RCons @('From 2 '( 'I 3, 'I 3)) (konst 0.2) $
            RCons @('From 4 '( 'I 3, 'I 3)) (konst 0.3) $
              RCons @('From 6 '( 'I 3, 'I 3)) (konst 0.4) RNil
      idH = idHomI @3
      idid = composeHomTrees @I3 @I3 @I3 idH idH
      fid = composeHomTrees @I3 @I3 @I3 f idH
      idf = composeHomTrees @I3 @I3 @I3 idH f
   in approxHomTrees @Hom33 idid idH
        && approxHomTrees @Hom33 fid f
        && approxHomTrees @Hom33 idf f

-- | Unequal-leaf compose @½ → 1 → ½@: left/right units on 'Hom12'.
checkComposeHomTrees121 :: Bool
checkComposeHomTrees121 =
  let f :: RepV Hom12
      f =
        RCons @('From 1 '( 'I 1, 'I 2)) (konst 0.3) $
          RCons @('From 3 '( 'I 1, 'I 2)) (konst 0.7) RNil
      id1 = idHomI @1
      id2 = idHomI @2
      -- f ∘ id₁  and  id₂ ∘ f
      idf = composeHomTrees @I1 @I1 @I2 id1 f
      fid = composeHomTrees @I1 @I2 @I2 f id2
   in approxHomTrees @Hom12 idf f && approxHomTrees @Hom12 fid f

-- | Atom-leaf F round-trip for @½⊗1⊗½@ via polymorphic 'CanFmoveTrees'.
checkFmoveTreesLeaves121 :: Bool
checkFmoveTreesLeaves121 =
  let assocL = fillRepVScaled @( FuseRep (FuseRep I1 I2) I1 )
      rt =
        fmoveInvTrees @I1 @I2 @I1
          (fmoveTrees @I1 @I2 @I1 assocL)
   in approxHomTrees @( FuseRep (FuseRep I1 I2) I1 ) assocL rt

-- | Nested F: Hom⊗leaf⊗leaf (@Hom11 ⊗ ½ ⊗ ½@) round-trip via channel-keyed F.
checkFmoveHomLeft111 :: Bool
checkFmoveHomLeft111 =
  let assocL = fillRepVScaled @( FuseRep (FuseRep Hom11 I1) I1 )
      rt =
        fmoveInvTreesHomLeft @1 @1 @1
          (fmoveTreesHomLeft @1 @1 @1 assocL)
   in approxHomTrees @( FuseRep (FuseRep Hom11 I1) I1 ) assocL rt

-- | 'HomFused' packaging unit laws on spin-1 via 'composeHomFused'.
checkHomFusedCategory222 :: Bool
checkHomFusedCategory222 =
  let f :: HomFused Atom2 Atom2
      f =
        HomFused $
          RCons @('From 0 '( 'I 2, 'I 2)) (konst 0.2) $
            RCons @('From 2 '( 'I 2, 'I 2)) (konst 0.3) $
              RCons @('From 4 '( 'I 2, 'I 2)) (konst 0.5) RNil
      idT = HomFused (idHomFusedVal @Atom2)
      HomFused idid = composeHomFused @Atom2 @Atom2 @Atom2 idT idT
      HomFused fid = composeHomFused @Atom2 @Atom2 @Atom2 idT f
      HomFused idf = composeHomFused @Atom2 @Atom2 @Atom2 f idT
   in approxHomTrees @Hom22 idid (idHomI @2)
        && approxHomTrees @Hom22 fid (unHomFused f)
        && approxHomTrees @Hom22 idf (unHomFused f)

-- | 'HomFused' unit laws on @tj = 3@ via polymorphic 'KnownHomFused' / 'idHomI'.
checkHomFusedCategory333 :: Bool
checkHomFusedCategory333 =
  let f :: HomFused Atom3 Atom3
      f =
        HomFused $
          RCons @('From 0 '( 'I 3, 'I 3)) (konst 0.1) $
            RCons @('From 2 '( 'I 3, 'I 3)) (konst 0.2) $
              RCons @('From 4 '( 'I 3, 'I 3)) (konst 0.3) $
                RCons @('From 6 '( 'I 3, 'I 3)) (konst 0.4) RNil
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
        HomFused (embedTrivialRepV @(FuseRep I1 I1) t)
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
checkI2FmoveSmoke :: Bool
checkI2FmoveSmoke =
  let assocL = fillRepVScaled @( FuseRep (FuseRep I2 I2) I2 )
      assocOk =
        approxHomTrees @( FuseRep (FuseRep I2 I2) I2 ) assocL $
          fmoveInvTrees @I2 @I2 @I2 (fmoveTrees @I2 @I2 @I2 assocL)
      idH = idHomI @2
      dom = fuseRepTerm @Hom22 @Hom22 idH idH
      mid = fmoveOuterHom @I2 @I2 @I2 dom
      back = fmoveInvOuterHom @I2 @I2 @I2 mid
   in assocOk && approxHomTrees @( FuseRep (FuseRep I2 I2) Hom22 ) dom back

-- | Outer F round-trip on Dom = Fuse(id,id): @F⁻¹ ∘ F ≈ id@.
checkFmoveOuter111 :: Bool
checkFmoveOuter111 =
  let dom = fuseRepTerm @Hom11 @Hom11 (idHomI @1) (idHomI @1)
      mid = fmoveOuterHom @I1 @I1 @I1 dom
      back = fmoveInvOuterHom @I1 @I1 @I1 mid
   in approxHomTrees @Dom111 dom back

-- | 'fuseMapLeft id' is the identity on Mid.
checkFuseMapLeftId111 :: Bool
checkFuseMapLeftId111 =
  let mid =
        fmoveOuterHom @I1 @I1 @I1 $
          fuseRepTerm @Hom11 @Hom11 (idHomI @1) (idHomI @1)
      mid' = fuseMapLeft @I1 @I1 @AssocR111 id mid
   in approxHomTrees @Mid111 mid mid'

