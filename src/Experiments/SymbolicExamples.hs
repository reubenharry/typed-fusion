{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Smokes for 'Experiments.Symbolic': term-level checks and compile-time type equalities.
-- Covers Dual-left 'HomUnfused' and genealogy 'HomFused' / 'composeHomTrees'.
-- Unit laws: 'composeHomTreesSelfTest'.
-- Fused cups: 'cupFused' / 'capFused' on singlet trees.
-- Phase-1 fusion trees: 'FuseTrees' / 'ToVTree' / 'Root'.
module Experiments.SymbolicExamples where

import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..), id)
import Data.Complex (Complex ((:+)), magnitude)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (InnerSpace ((<.>)), (*^), (^-^))
import Experiments.Categorical.Associative (Associative (..))
import Experiments.Categorical.Bifunctor (Bifunctor (..))
import Experiments.Fusion.Obj as FObj
import Experiments.Symbolic
import GHC.TypeLits (Nat)
import Math.LinearMap.Category
  ( DualVector
  , pattern LinearFunction
  , type (+>)
  , type (⊗)
  , (⊗)
  )
import Math.LinearMap.Category.Class (asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, konst)
import TensorNetwork.Categorical ((⊗^))
import qualified Data.Vector.Storable as VS

import Prelude hiding (id, (.), ($))

-- | Right unitor absorbs @Unit@ on Dual-left HomUnfused (@m ⊗ 1 ≅ m@).
unitRunitMorTrivialOk :: Bool
unitRunitMorTrivialOk =
  let m = (5 :+ 0) *^ idMorObj @('FObj.Atom 0)
      u = unitToVFromScalar 1
   in toVApproxEq
        (toArray
           ( unitRunit
               @( DualVector (ToVObj ('FObj.Atom 0))
                    ⊗ ToVObj ('FObj.Atom 0)
                )
               $ (m ⊗ u)
           ))
        (toArray m)

-- | @(cup ⊗ id)@ then unitor on a packed assoc-shape state: @cup(η_b) = dim b@.
cupTensorIdUnitorOk :: Bool
cupTensorIdUnitorOk =
  let packed =
        dualAtomAtomM @0 @1 (unitToVFromScalar 1)
          ⊗ ( capUnfusedObj @('FObj.Atom 1) (unitToVFromScalar 1)
                ⊗ unitToVFromScalar 1
            )
      out =
        unitorComposeObj
          @('FObj.Atom 0)
          @('FObj.Atom 0)
          ( cupTensorIdComposeObj
              @('FObj.Atom 0)
              @('FObj.Atom 1)
              @('FObj.Atom 0)
              packed
          )
      -- @cup ∘ cap = 2@ on spin-½; result is scale on Dual-left @η@.
      expected = 2 *^ idMorObj @('FObj.Atom 0)
   in all (\(x, y) -> magnitude (x - y) < 1e-9)
        (zip (VS.toList (toArray out)) (VS.toList (toArray expected)))

toVApproxEq :: VS.Vector (Complex Double) -> VS.Vector (Complex Double) -> Bool
toVApproxEq u v =
  VS.length u == VS.length v
    && VS.and (VS.zipWith (\x y -> magnitude (x - y) < 1e-9) u v)

-- | @composeMorObj id id ≅ id@ on @j = 0@.
composeMorObjIdIdTrivialOk :: Bool
composeMorObjIdIdTrivialOk =
  let i = id :: HomUnfused ('FObj.Atom 0) ('FObj.Atom 0)
   in toVApproxEq
        (toArray (unHomUnfused (i . i)))
        (toArray (unHomUnfused i))

-- | Left unit law: @id ∘ f ≅ f@ on spin-½ ('HomUnfused').
composeMorObjLeftUnitOk :: Bool
composeMorObjLeftUnitOk =
  let i = id :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
      f =
        HomUnfused ((3 :+ 0) *^ unHomUnfused i)
          :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
   in toVApproxEq
        (toArray (unHomUnfused (i . f)))
        (toArray (unHomUnfused f))

-- | Right unit law: @f ∘ id ≅ f@ on spin-½ ('HomUnfused').
composeMorObjRightUnitOk :: Bool
composeMorObjRightUnitOk =
  let i = id :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
      f =
        HomUnfused ((3 :+ 0) *^ unHomUnfused i)
          :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
   in toVApproxEq
        (toArray (unHomUnfused (f . i)))
        (toArray (unHomUnfused f))

-- | Unfused 'HomUnfused' composition matches ordinary map composition.
--
-- Objects: spin-½ (@C 1 ⊗ C 2@) → spin-½ → spin-1 (@C 1 ⊗ C 3@), with @id@ on
-- the trivial copy leg. Hom elements are @asTensor@ of the linear maps;
-- @g . f@ is compared to @g ∘ f@ on the standard basis.
composeMorObjMatchesMatMulOk :: Bool
composeMorObjMatchesMatMulOk =
  let -- Irrep-leg maps (column action on coordinate lists).
      fLeg :: C 2 +> C 2
      fLeg =
        arr . LinearFunction $ \v ->
          let [a, b] = VS.toList (toArray v)
           in unsafeFromArray (VS.fromList [a + 2 * b, 3 * a + 4 * b])
      gLeg :: C 2 +> C 3
      gLeg =
        arr . LinearFunction $ \v ->
          let [a, b] = VS.toList (toArray v)
           in unsafeFromArray (VS.fromList [a, b, a + b])
      uf :: (C 1 ⊗ C 2) +> (C 1 ⊗ C 2)
      uf = id ⊗^ fLeg
      ug :: (C 1 ⊗ C 2) +> (C 1 ⊗ C 3)
      ug = id ⊗^ gLeg
      fHom =
        HomUnfused (asTensor -+$=> uf)
          :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
      gHom =
        HomUnfused (asTensor -+$=> ug)
          :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 2)
      hHom = gHom . fHom
      h = fromTensor -+$=> unHomUnfused hHom :: (C 1 ⊗ C 2) +> (C 1 ⊗ C 3)
      e0 = unsafeFromArray (VS.fromList [1, 0]) :: C 2
      e1 = unsafeFromArray (VS.fromList [0, 1]) :: C 2
      xs = [(konst 1 ⊗ e0), (konst 1 ⊗ e1)]
      agree x =
        toVApproxEq (toArray (h $ x)) (toArray (ug $ (uf $ x)))
   in all agree xs

-- | @composeMorObj id id ≅ id@ on spin-½ (true unfused Hom).
composeMorObjIdIdOk :: Bool
composeMorObjIdIdOk =
  let i = id :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
   in toVApproxEq
        (toArray (unHomUnfused (i . i)))
        (toArray (unHomUnfused i))

-- | @bimap id id ≅ id@ on @½ ⊗ ½@ (true unfused Hom).
bimapHomUnfusedIdIdOk :: Bool
bimapHomUnfusedIdIdOk =
  let iHalf = id :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
      iTen =
        id
          :: HomUnfused
               (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
               (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
      bi =
        bimap iHalf iHalf
          :: HomUnfused
               (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
               (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
   in toVApproxEq (toArray (unHomUnfused bi)) (toArray (unHomUnfused iTen))
-- | @disassociate ∘ associate ≅ id@ as linear maps on @(½ ⊗ ½) ⊗ ½@
-- (Hom packing of linearmap α / α⁻¹; avoids Hom-compose cost on the smoke).
associateHomUnfusedRoundtripOk :: Bool
associateHomUnfusedRoundtripOk =
  let α =
        unHomUnfused
          ( associate
              :: HomUnfused
                   ( FObj.Tensor
                       (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
                       ('FObj.Atom 1)
                   )
                   ( FObj.Tensor
                       ('FObj.Atom 1)
                       (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
                   )
          )
      αinv =
        unHomUnfused
          ( disassociate
              :: HomUnfused
                   ( FObj.Tensor
                       ('FObj.Atom 1)
                       (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
                   )
                   ( FObj.Tensor
                       (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
                       ('FObj.Atom 1)
                   )
          )
      roundTrip =
        (fromTensor -+$=> αinv)
          . (fromTensor -+$=> α)
            :: ToVObj
                 ( FObj.Tensor
                     (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
                     ('FObj.Atom 1)
                 )
               +> ToVObj
                    ( FObj.Tensor
                        (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
                        ('FObj.Atom 1)
                    )
      iHom =
        unHomUnfused
          ( id
              :: HomUnfused
                   ( FObj.Tensor
                       (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
                       ('FObj.Atom 1)
                   )
                   ( FObj.Tensor
                       (FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
                       ('FObj.Atom 1)
                   )
          )
   in toVApproxEq
        (toArray (asTensor -+$=> roundTrip))
        (toArray iHom)

-- | 'undualAtomAtomM' ∘ 'dualAtomAtomM' ≈ @√(j+1) · CS²@ (pivotal undual).
-- For spin-½, @CS² = −id@, so the round-trip is @−√2 · v@.
undualDualRoundtripOk :: Bool
undualDualRoundtripOk =
  let v :: C 1 ⊗ C 2
      v = unsafeFromArray (VS.fromList [0.6, 0.8])
      expected =
        unsafeFromArray (VS.fromList [-(sqrt 2 * 0.6), -(sqrt 2 * 0.8)])
          :: C 1 ⊗ C 2
      v' = undualAtomAtomM @1 @1 (dualAtomAtomM @1 @1 v)
   in VS.and $
        VS.zipWith
          (\a b -> magnitude (a - b) < 1e-9)
          (toArray expected)
          (toArray v')

-- | 'capFused' then 'cupTrivial' recovers the unit scalar.
cupCapFusedRoundtripSpinHalfOk :: Bool
cupCapFusedRoundtripSpinHalfOk =
  let u = 0.7 :+ 0
   in magnitude (cupTrivial (capFused @Leaf1 u) - 0.7) < 1e-9

-- | All symbolic smokes in one place (for REPL / probes).
symbolicExamplesOk :: Bool
symbolicExamplesOk =
  and
    [ unitRunitMorTrivialOk
    , cupTensorIdUnitorOk
    , composeMorObjIdIdTrivialOk
    , composeMorObjLeftUnitOk
    , composeMorObjRightUnitOk
    , composeMorObjMatchesMatMulOk
    , composeMorObjIdIdOk
    , bimapHomUnfusedIdIdOk
    , associateHomUnfusedRoundtripOk
    , undualDualRoundtripOk
    , cupCapFusedRoundtripSpinHalfOk
    , composeHomTreesSelfTest
    , composeHomTreesLeaf1TypedOk
    ]


--------------------------------------------------------------------------------
-- Compile-time smokes (type equalities)
--------------------------------------------------------------------------------

type family AssertEqNat (a :: Nat) (b :: Nat) :: Bool where
  AssertEqNat a a = 'True

type family AssertEqRep (a :: Rep) (b :: Rep) :: Bool where
  AssertEqRep a a = 'True

type family AssertEqType (a :: Type) (b :: Type) :: Bool where
  AssertEqType a a = 'True

type family AssertEqIrrep (a :: Irrep) (b :: Irrep) :: Bool where
  AssertEqIrrep a a = 'True

-- | Fused Hom is 'RepV' of 'FuseRep' (genealogy-preserving).
type SmokeHomFused =
  AssertEqType
    (ToVRep (FuseRep '[ 'Leaf 1] '[ 'Leaf 1]))
    (ToVRep Hom11)

-- | @½ ⊗ ½@ fusion trees: singlet and triplet channels (no coalesce).
type SmokeFuseTrees =
  AssertEqRep
    (FuseTrees ('Leaf 1) ('Leaf 1))
    '[ 'Node 0 ('Leaf 1) ('Leaf 1)
     , 'Node 2 ('Leaf 1) ('Leaf 1)
     ]

-- | Root of a fusion tree is the channel label.
type SmokeRootNode =
  AssertEqNat
    (Root ('Node 0 ('Leaf 1) ('Leaf 1)))
    0

-- | 'ToVTree' is the root irrep space only (@j=1 ⇒ C 2@; @j=2 ⇒ C 3@).
type SmokeToVTree =
  AssertEqType
    (ToVTree ('Node 2 ('Leaf 1) ('Leaf 1)))
    (C 3)

-- | 'ToVRep' nests root spaces.
type SmokeToVRep =
  AssertEqType
    (ToVRep (FuseTrees ('Leaf 1) ('Leaf 1)))
    (C 1, C 3)

-- | List fuse distributes over tree pairs.
type SmokeFuseRep =
  AssertEqRep
    (FuseRep '[ 'Leaf 1] '[ 'Leaf 1])
    (FuseTrees ('Leaf 1) ('Leaf 1))

-- | Left-assoc @½⊗½⊗½@ equals the concrete 'AssocL111' spine used by 'fmoveTrees111'.
type SmokeAssocL111 =
  AssertEqRep
    ( FuseRep (FuseRep '[ 'Leaf 1] '[ 'Leaf 1]) '[ 'Leaf 1] )
    AssocL111

type SmokeAssocR111 =
  AssertEqRep
    ( FuseRep '[ 'Leaf 1] (FuseRep '[ 'Leaf 1] '[ 'Leaf 1]) )
    AssocR111

type SmokeAssocL110 =
  AssertEqRep
    ( FuseRep (FuseRep '[ 'Leaf 1] '[ 'Leaf 1]) '[ 'Leaf 0] )
    AssocL110

type SmokeAssocR110 =
  AssertEqRep
    ( FuseRep '[ 'Leaf 1] (FuseRep '[ 'Leaf 1] '[ 'Leaf 0]) )
    AssocR110

type SmokeAssocL112 =
  AssertEqRep
    ( FuseRep (FuseRep '[ 'Leaf 1] '[ 'Leaf 1]) '[ 'Leaf 2] )
    AssocL112

type SmokeAssocR112 =
  AssertEqRep
    ( FuseRep '[ 'Leaf 1] (FuseRep '[ 'Leaf 1] '[ 'Leaf 2]) )
    AssocR112

-- | Concrete Leaf-½ Hom-compose spines match 'FuseRep' expansions.
type SmokeHom11 =
  AssertEqRep
    (FuseRep '[ 'Leaf 1] '[ 'Leaf 1])
    Hom11

type SmokeDom111 =
  AssertEqRep
    (FuseRep Hom11 Hom11)
    Dom111

type SmokeMid111 =
  AssertEqRep
    (FuseRep '[ 'Leaf 1] AssocR111)
    Mid111

type SmokeCupR111 =
  AssertEqRep
    (FuseRep '[ 'Leaf 1] AssocL111)
    CupR111

-- | Nested outer-F codomain (Mac Lane step 2) equals 'Mid111'.
type SmokeAfterOuterF111 =
  AssertEqRep
    ( FuseRep
        '[ 'Leaf 1]
        (FuseRep '[ 'Leaf 1] (FuseRep '[ 'Leaf 1] '[ 'Leaf 1]))
    )
    Mid111

-- | Nested cup-ready spine (Mac Lane step 3) equals 'CupR111'.
type SmokeCupReady111 =
  AssertEqRep
    ( FuseRep
        '[ 'Leaf 1]
        (FuseRep (FuseRep '[ 'Leaf 1] '[ 'Leaf 1]) '[ 'Leaf 1])
    )
    CupR111

-- | After @id ⊗ (cup ⊗ id)@: Unit remains as 'Unit' in the middle.
type SmokeAfterCup111 =
  AssertEqRep
    (FuseRep '[ 'Leaf 1] (FuseRep Unit '[ 'Leaf 1]))
    '[ 'Node 0 ('Leaf 1) ('Node 1 ('Leaf 0) ('Leaf 1))
     , 'Node 2 ('Leaf 1) ('Node 1 ('Leaf 0) ('Leaf 1))
     ]

type SmokeHom00 =
  AssertEqRep
    (FuseRep '[ 'Leaf 0] '[ 'Leaf 0])
    Hom00

type SmokeDom000 =
  AssertEqRep
    (FuseRep Hom00 Hom00)
    Dom000

type SmokeCupR000 =
  AssertEqRep
    (FuseRep '[ 'Leaf 0] (FuseRep Hom00 '[ 'Leaf 0]))
    CupR000

-- | Flat layout equals reduced HMatrix packing for @½⊗½⊗½@ (both associations).
smokeHomFused :: Proxy SmokeHomFused
smokeHomFused = Proxy

smokeFuseTrees :: Proxy SmokeFuseTrees
smokeFuseTrees = Proxy

smokeRootNode :: Proxy SmokeRootNode
smokeRootNode = Proxy

smokeToVTree :: Proxy SmokeToVTree
smokeToVTree = Proxy

smokeToVRep :: Proxy SmokeToVRep
smokeToVRep = Proxy

smokeFuseRep :: Proxy SmokeFuseRep
smokeFuseRep = Proxy

smokeAssocL111 :: Proxy SmokeAssocL111
smokeAssocL111 = Proxy

smokeAssocR111 :: Proxy SmokeAssocR111
smokeAssocR111 = Proxy

smokeAssocL110 :: Proxy SmokeAssocL110
smokeAssocL110 = Proxy

smokeAssocR110 :: Proxy SmokeAssocR110
smokeAssocR110 = Proxy

smokeAssocL112 :: Proxy SmokeAssocL112
smokeAssocL112 = Proxy

smokeAssocR112 :: Proxy SmokeAssocR112
smokeAssocR112 = Proxy

-- | Sample left-assoc @½⊗½⊗½@ state for F-move self-tests.
sampleAssocL111 :: RepV AssocL111
sampleAssocL111 =
  vToRepV @AssocL111 (konst 1, (konst 0.5, konst 0.25))

sampleAssocL110 :: RepV AssocL110
sampleAssocL110 =
  vToRepV @AssocL110 (konst 1, konst 0.5)

sampleAssocL112 :: RepV AssocL112
sampleAssocL112 =
  vToRepV @AssocL112 (konst 1, (konst 0.5, (konst 0.25, konst 0.125)))

-- | Tree F-move round-trips (@F⁻¹ ∘ F ≈ id@) on concrete triples + @½⊗1⊗½@.
fmoveTreesSelfTest :: Bool
fmoveTreesSelfTest =
  checkFmoveTrees111 sampleAssocL111
    && checkFmoveTrees110 sampleAssocL110
    && checkFmoveTrees112 sampleAssocL112
    && checkFmoveTreesLeaves @1 @2 @1 (sampleAssocLLeaves @1 @2 @1)

-- | Force the F-move self-test at module load (fails loud if broken).
fmoveTreesSelfTestOk :: ()
fmoveTreesSelfTestOk =
  if fmoveTreesSelfTest
    then ()
    else error "fmoveTreesSelfTest failed: tree F round-trip"

-- | Pure Mid from 'TensorTrees': 'fuseMapRightFinv111' matches F-inv on the assoc factor.
fuseMapRightFinvSelfTest :: Bool
fuseMapRightFinvSelfTest =
  let leaf = RCons (konst 1) RNil
      assocR = vToRepV @AssocR111 (konst 0.5, (konst 0.25, konst 0.125))
      mid = fuseTensorTrees @Leaf1 @AssocR111 (TensorTrees leaf assocR)
      cupGen = fuseMapRightFinv111 mid
      expected =
        fuseTensorTrees @Leaf1 @AssocL111 $
          TensorTrees leaf (fmoveInvTrees111 assocR)
      close a b =
        let d = a ^-^ b
         in magnitude (d <.> d) < 1e-12
      approxHom16
        (a0, (a2, (b0, (b2, (c2, c4)))))
        (a0', (a2', (b0', (b2', (c2', c4'))))) =
          and
            [ close a0 a0'
            , close a2 a2'
            , close b0 b0'
            , close b2 b2'
            , close c2 c2'
            , close c4 c4'
            ]
   in approxHom16 (repVToV @CupR111 cupGen) (repVToV @CupR111 expected)

-- | Full leaf Hom compose ladder via five Mac Lane morphisms.
composeHomTreesSelfTest :: Bool
composeHomTreesSelfTest =
  checkComposeHomTrees111
    && checkComposeHomTrees000
    && checkComposeHomTrees222
    && checkComposeHomTrees333
    && checkComposeHomTrees121
    && checkFmoveTreesLeaves121
    && checkFmoveHomLeft111
    && checkHomFusedCategory222
    && checkHomFusedCategory333
    && checkLeaf2FmoveSmoke
    && checkFmoveOuter111
    && checkFuseMapLeftId111
    && checkUnitorLeaf1
    && checkUnitorHom11
    && checkCupLeafHom

composeHomTreesSelfTestOk :: ()
composeHomTreesSelfTestOk =
  if composeHomTreesSelfTest
    then ()
    else error "composeHomTreesSelfTest failed: id/unit laws on leaf Hom"

-- | Typechecks five-morphism 'composeHomTrees' at leaf-½ (do not evaluate).
composeHomTreesLeaf1
  :: RepV Hom11 -> RepV Hom11 -> RepV Hom11
composeHomTreesLeaf1 = composeHomTrees @Leaf1 @Leaf1 @Leaf1

composeHomTreesLeaf1TypedOk :: Bool
composeHomTreesLeaf1TypedOk =
  let _ty = composeHomTreesLeaf1
      _cup = cupTensorIdHomLeaf1
   in True
