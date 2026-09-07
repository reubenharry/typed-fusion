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
  , cupTensorIdHomLeaf1
  , approxHomTrees
  , approxHom11
  , checkFmoveTrees111
  , checkFmoveTrees110
  , checkFmoveTrees112
  , checkFmoveTreesLeaves
  , checkUnitorLeaf1
  , checkUnitorHom11
  , checkCupLeafHom
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
  , checkLeaf2FmoveSmoke
  , checkFmoveOuter111
  , checkFuseMapLeftId111
  ) where

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


-- | Triple-leaf F-move via label-driven 'fmoveTreesLeaves'.
fmoveTrees111 :: RepV AssocL111 -> RepV AssocR111
fmoveTrees111 = fmoveTreesLeaves @1 @1 @1

fmoveInvTrees111 :: RepV AssocR111 -> RepV AssocL111
fmoveInvTrees111 = fmoveInvTreesLeaves @1 @1 @1

fmoveTrees000 :: RepV AssocL000 -> RepV AssocR000
fmoveTrees000 = fmoveTreesLeaves @0 @0 @0

fmoveInvTrees000 :: RepV AssocR000 -> RepV AssocL000
fmoveInvTrees000 = fmoveInvTreesLeaves @0 @0 @0

fmoveTrees110 :: RepV AssocL110 -> RepV AssocR110
fmoveTrees110 = fmoveTreesLeaves @1 @1 @0

fmoveInvTrees110 :: RepV AssocR110 -> RepV AssocL110
fmoveInvTrees110 = fmoveInvTreesLeaves @1 @1 @0

fmoveTrees112 :: RepV AssocL112 -> RepV AssocR112
fmoveTrees112 = fmoveTreesLeaves @1 @1 @2

fmoveInvTrees112 :: RepV AssocR112 -> RepV AssocL112
fmoveInvTrees112 = fmoveInvTreesLeaves @1 @1 @2

-- | @Fuse(id, F-inv)@ on Mid — instance of 'fuseMapRight'.
fuseMapRightFinv111 :: RepV Mid111 -> RepV CupR111
fuseMapRightFinv111 =
  fuseMapRight @Leaf1 @AssocR111 @AssocL111 fmoveInvTrees111

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
        SLeaf {} ->
          RCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)
        SNode {} ->
          RCons (konst (0.1 * fromIntegral (i + 1) :+ 0)) (go (i + 1) rest)

cupTensorIdHomLeaf1
  :: RepV (FuseRep Leaf1 (FuseRep Hom11 Leaf1))
  -> RepV (FuseRep Leaf1 (FuseRep Unit Leaf1))
cupTensorIdHomLeaf1 = cupTensorIdHom @Leaf1 @Leaf1 @Leaf1

-- | Approx equality on Hom / association spines (forgetful flat).
approxHomTrees
  :: forall ts
   . KnownRep ts
  => RepV ts
  -> RepV ts
  -> Bool
approxHomTrees u v =
  let bu = repVToForgetFlat @ts u
      bv = repVToForgetFlat @ts v
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
     , KnownRep ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
     , KnownRep ( FuseRep '[ 'Leaf ja] (FuseRep '[ 'Leaf jb] '[ 'Leaf jc]) )
     )
  => RepV ( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
  -> Bool
checkFmoveTreesLeaves tv =
  let rt = fmoveInvTreesLeaves @ja @jb @jc (fmoveTreesLeaves @ja @jb @jc tv)
   in approxRepV
        @( FuseRep (FuseRep '[ 'Leaf ja] '[ 'Leaf jb]) '[ 'Leaf jc] )
        tv
        rt

-- | 'unitor' on @Unit ⊗ Leaf½@: payload round-trip.
checkUnitorLeaf1 :: Bool
checkUnitorLeaf1 =
  let u =
        RCons @('Node 1 ('Leaf 0) ('Leaf 1)) (konst 0.42) RNil
          :: RepV (FuseRep Unit Leaf1)
      v = unitor @Leaf1 u
   in case repVToV @Leaf1 v of
        x ->
          let d = x ^-^ konst 0.42
           in magnitude (d <.> d) < 1e-18

-- | 'unitorHom' = 'fuseMapRight' 'unitor' on after-cup leaf-½ spine.
checkUnitorHom11 :: Bool
checkUnitorHom11 =
  let mid =
        RCons @('Node 0 ('Leaf 1) ('Node 1 ('Leaf 0) ('Leaf 1))) (konst 0.3) $
          RCons @('Node 2 ('Leaf 1) ('Node 1 ('Leaf 0) ('Leaf 1))) (konst 0.7) RNil
      out = unitorHom @Leaf1 @Leaf1 mid
   in approxHom11 out $
        RCons @('Node 0 ('Leaf 1) ('Leaf 1)) (konst 0.3) $
          RCons @('Node 2 ('Leaf 1) ('Leaf 1)) (konst 0.7) RNil

-- | Mac Lane 'cup' on leaf Hom: singlet × FS·dim (@0 → 1@, @½ → −2@, @1 → 3@).
checkCupLeafHom :: Bool
checkCupLeafHom =
  let s0 =
        case cup @Leaf0 (idHomLeaf @0) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
      s1 =
        case cup @Leaf1 (idHomLeaf @1) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
      s2 =
        case cup @Leaf2 (idHomLeaf @2) of
          RCons v RNil -> konst 1 <.> v
          _ -> 0
   in magnitude (s0 - 1) < 1e-12
        && magnitude (s1 - (-2)) < 1e-12
        && magnitude (s2 - 3) < 1e-12

-- | Five-morphism 'composeHomTrees' unit laws on leaf-½.
checkComposeHomTrees111 :: Bool
checkComposeHomTrees111 =
  let f =
        RCons @('Node 0 ('Leaf 1) ('Leaf 1)) (konst 0.3) $
          RCons @('Node 2 ('Leaf 1) ('Leaf 1)) (konst 0.7) RNil
      idH = idHomLeaf @1
      idid = composeHomTrees @Leaf1 @Leaf1 @Leaf1 idH idH
      fid = composeHomTrees @Leaf1 @Leaf1 @Leaf1 f idH
      idf = composeHomTrees @Leaf1 @Leaf1 @Leaf1 idH f
   in approxHomTrees @Hom11 idid idH
        && approxHomTrees @Hom11 fid f
        && approxHomTrees @Hom11 idf f

-- | Five-morphism compose unit laws on trivial Hom.
checkComposeHomTrees000 :: Bool
checkComposeHomTrees000 =
  let f = RCons @('Node 0 ('Leaf 0) ('Leaf 0)) (konst 0.4) RNil
      idH = idHomLeaf @0
   in approxHomTrees @Hom00
        (composeHomTrees @Leaf0 @Leaf0 @Leaf0 idH idH)
        idH
        && approxHomTrees @Hom00
          (composeHomTrees @Leaf0 @Leaf0 @Leaf0 f idH)
          f
        && approxHomTrees @Hom00
          (composeHomTrees @Leaf0 @Leaf0 @Leaf0 idH f)
          f

-- | Leaf spin-1 Hom compose: @id∘id ≈ id@ and left/right units on multi-channel Hom.
checkComposeHomTrees222 :: Bool
checkComposeHomTrees222 =
  let f =
        RCons @('Node 0 ('Leaf 2) ('Leaf 2)) (konst 0.2) $
          RCons @('Node 2 ('Leaf 2) ('Leaf 2)) (konst 0.3) $
            RCons @('Node 4 ('Leaf 2) ('Leaf 2)) (konst 0.5) RNil
      idH = idHomLeaf @2
      idid = composeHomTrees @Leaf2 @Leaf2 @Leaf2 idH idH
      fid = composeHomTrees @Leaf2 @Leaf2 @Leaf2 f idH
      idf = composeHomTrees @Leaf2 @Leaf2 @Leaf2 idH f
   in approxHomTrees @Hom22 idid idH
        && approxHomTrees @Hom22 fid f
        && approxHomTrees @Hom22 idf f

-- | Polymorphic leaf F + outer Hom: unit laws on @tj = 3@.
checkComposeHomTrees333 :: Bool
checkComposeHomTrees333 =
  let f =
        RCons @('Node 0 ('Leaf 3) ('Leaf 3)) (konst 0.1) $
          RCons @('Node 2 ('Leaf 3) ('Leaf 3)) (konst 0.2) $
            RCons @('Node 4 ('Leaf 3) ('Leaf 3)) (konst 0.3) $
              RCons @('Node 6 ('Leaf 3) ('Leaf 3)) (konst 0.4) RNil
      idH = idHomLeaf @3
      idid = composeHomTrees @Leaf3 @Leaf3 @Leaf3 idH idH
      fid = composeHomTrees @Leaf3 @Leaf3 @Leaf3 f idH
      idf = composeHomTrees @Leaf3 @Leaf3 @Leaf3 idH f
   in approxHomTrees @Hom33 idid idH
        && approxHomTrees @Hom33 fid f
        && approxHomTrees @Hom33 idf f

-- | Unequal-leaf compose @½ → 1 → ½@: left/right units on 'Hom12'.
checkComposeHomTrees121 :: Bool
checkComposeHomTrees121 =
  let f :: RepV Hom12
      f =
        RCons @('Node 1 ('Leaf 1) ('Leaf 2)) (konst 0.3) $
          RCons @('Node 3 ('Leaf 1) ('Leaf 2)) (konst 0.7) RNil
      id1 = idHomLeaf @1
      id2 = idHomLeaf @2
      -- f ∘ id₁  and  id₂ ∘ f
      idf = composeHomTrees @Leaf1 @Leaf1 @Leaf2 id1 f
      fid = composeHomTrees @Leaf1 @Leaf2 @Leaf2 f id2
   in approxHomTrees @Hom12 idf f && approxHomTrees @Hom12 fid f

-- | Atom-leaf F round-trip for @½⊗1⊗½@ via polymorphic 'CanFmoveTrees'.
checkFmoveTreesLeaves121 :: Bool
checkFmoveTreesLeaves121 =
  let assocL = sampleAssocLLeaves @1 @2 @1
      rt =
        fmoveInvTrees @Leaf1 @Leaf2 @Leaf1
          (fmoveTrees @Leaf1 @Leaf2 @Leaf1 assocL)
   in approxHomTrees @( FuseRep (FuseRep Leaf1 Leaf2) Leaf1 ) assocL rt

-- | Nested F: Hom⊗leaf⊗leaf (@Hom11 ⊗ ½ ⊗ ½@) round-trip via channel-keyed F.
checkFmoveHomLeft111 :: Bool
checkFmoveHomLeft111 =
  let assocL = fillRepVScaled @( FuseRep (FuseRep Hom11 Leaf1) Leaf1 )
      rt =
        fmoveInvTreesHomLeft @1 @1 @1
          (fmoveTreesHomLeft @1 @1 @1 assocL)
   in approxHomTrees @( FuseRep (FuseRep Hom11 Leaf1) Leaf1 ) assocL rt

-- | 'HomFused' packaging unit laws on spin-1 via 'composeHomFused'.
checkHomFusedCategory222 :: Bool
checkHomFusedCategory222 =
  let f :: HomFused Spine2 Spine2
      f =
        HomFused $
          RCons @('Node 0 ('Leaf 2) ('Leaf 2)) (konst 0.2) $
            RCons @('Node 2 ('Leaf 2) ('Leaf 2)) (konst 0.3) $
              RCons @('Node 4 ('Leaf 2) ('Leaf 2)) (konst 0.5) RNil
      idT = HomFused (idHomFusedVal @Spine2)
      HomFused idid = composeHomFused @Spine2 @Spine2 @Spine2 idT idT
      HomFused fid = composeHomFused @Spine2 @Spine2 @Spine2 idT f
      HomFused idf = composeHomFused @Spine2 @Spine2 @Spine2 f idT
   in approxHomTrees @Hom22 idid (idHomLeaf @2)
        && approxHomTrees @Hom22 fid (unHomFused f)
        && approxHomTrees @Hom22 idf (unHomFused f)

-- | 'HomFused' unit laws on @tj = 3@ via polymorphic 'KnownHomFused' / 'idHomLeaf'.
checkHomFusedCategory333 :: Bool
checkHomFusedCategory333 =
  let f :: HomFused Spine3 Spine3
      f =
        HomFused $
          RCons @('Node 0 ('Leaf 3) ('Leaf 3)) (konst 0.1) $
            RCons @('Node 2 ('Leaf 3) ('Leaf 3)) (konst 0.2) $
              RCons @('Node 4 ('Leaf 3) ('Leaf 3)) (konst 0.3) $
                RCons @('Node 6 ('Leaf 3) ('Leaf 3)) (konst 0.4) RNil
      idT = HomFused (idHomFusedVal @Spine3)
      HomFused idid = composeHomFused @Spine3 @Spine3 @Spine3 idT idT
      HomFused fid = composeHomFused @Spine3 @Spine3 @Spine3 idT f
      HomFused idf = composeHomFused @Spine3 @Spine3 @Spine3 f idT
   in approxHomTrees @Hom33 idid (idHomFusedVal @Spine3)
        && approxHomTrees @Hom33 fid (unHomFused f)
        && approxHomTrees @Hom33 idf (unHomFused f)

-- | 'HomInter' unit laws on spin-½ via embed → 'composeHomTrees' → filter.
checkHomInterCategory111 :: Bool
checkHomInterCategory111 =
  let f :: HomInter Spine1 Spine1
      f =
        HomInter $
          scaleRepV @Inter11 (0.3 :+ 0) (idHomInterVal @Spine1)
      idT = HomInter (idHomInterVal @Spine1)
      HomInter idid = composeHomInter @Spine1 @Spine1 @Spine1 idT idT
      HomInter fid = composeHomInter @Spine1 @Spine1 @Spine1 idT f
      HomInter idf = composeHomInter @Spine1 @Spine1 @Spine1 f idT
   in approxHomTrees @Inter11 idid (idHomInterVal @Spine1)
        && approxHomTrees @Inter11 fid (unHomInter f)
        && approxHomTrees @Inter11 idf (unHomInter f)

-- | Spin-1 leaf smoke: atom F + outer Hom F round-trips.
checkLeaf2FmoveSmoke :: Bool
checkLeaf2FmoveSmoke =
  let assocL = sampleAssocLLeaves @2 @2 @2
      assocOk =
        approxHomTrees @( FuseRep (FuseRep Leaf2 Leaf2) Leaf2 ) assocL $
          fmoveInvTreesLeaves @2 @2 @2 (fmoveTreesLeaves @2 @2 @2 assocL)
      idH = idHomLeaf @2
      dom = fuseRepTerm @Hom22 @Hom22 idH idH
      mid = fmoveOuterHom @Leaf2 @Leaf2 @Leaf2 dom
      back = fmoveInvOuterHom @Leaf2 @Leaf2 @Leaf2 mid
   in assocOk && approxHomTrees @( FuseRep (FuseRep Leaf2 Leaf2) Hom22 ) dom back

-- | Outer F round-trip on Dom = Fuse(id,id): @F⁻¹ ∘ F ≈ id@.
checkFmoveOuter111 :: Bool
checkFmoveOuter111 =
  let dom = fuseRepTerm @Hom11 @Hom11 (idHomLeaf @1) (idHomLeaf @1)
      mid = fmoveOuterHom @Leaf1 @Leaf1 @Leaf1 dom
      back = fmoveInvOuterHom @Leaf1 @Leaf1 @Leaf1 mid
   in approxHomTrees @Dom111 dom back

-- | 'fuseMapLeft id' is the identity on Mid.
checkFuseMapLeftId111 :: Bool
checkFuseMapLeftId111 =
  let mid =
        fmoveOuterHom @Leaf1 @Leaf1 @Leaf1 $
          fuseRepTerm @Hom11 @Hom11 (idHomLeaf @1) (idHomLeaf @1)
      mid' = fuseMapLeft @Leaf1 @Leaf1 @AssocR111 id mid
   in approxHomTrees @Mid111 mid mid'

