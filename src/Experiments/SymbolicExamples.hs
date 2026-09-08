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
-- Fused cup/cap: genealogy 'cup' / 'idHomFusedVal'.
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
import Experiments.Fusion.SU2 (SU2Th)
import Experiments.Symbolic
import GHC.TypeLits (Nat)
import Math.LinearMap.Category
  ( DualVector
  , fromLinearForm
  , pattern LinearFunction
  , type (+>)
  , type (⊗)
  , (⊗)
  )
import Math.LinearMap.Category.Class (asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, konst)
import qualified Data.Vector.Storable as VS

import Prelude hiding (id, (.), ($))

exampleRep :: RepV '[ 'Bare 1, 'Bare 3]
exampleRep =
  RCons @('Bare 1) (konst 1) $
    RCons @('Bare 3) (konst 1) RNil

exampleUnfused :: ToVObj (Tensor ('Atom 1) ('Atom 1))
exampleUnfused = konst 1 ⊗ konst 1

example :: RepV (FuseRep '[ 'Bare 1] '[ 'Bare 1])
example = undefined

type TW = Tensor ('Atom 1) ('Atom 1)

type Irr (a :: Nat) = 'Atom a
type (:**:) (a :: Nat) (b :: Nat) =  ToVRep (FuseRep (ObjRep (Irr a)) (ObjRep (Irr b)))
type Unfused obj =  ToVObj obj
type (:*:) (a :: Obj Nat) (b :: Obj Nat) =  'FObj.Tensor a b

-- Leaf: Irrep
-- Node: a `From` (b,c) 

type Fused obj = ToVRep (ObjTrees obj)

foo :: Unfused (TW)
foo = undefined

baz :: Fused ( (Irr 1 :*: Irr 1) :*: Irr 2)
baz = undefined

fuseExample
  :: ToVObj ('Tensor ('Atom 1) ('Atom 1))
  -> RepV '[ 'From 0 '( 'Bare 1, 'Bare 1), 'From 2 '( 'Bare 1, 'Bare 1)]
fuseExample = fuseTrees @('Bare 1) @('Bare 1)

-- | Genealogy @(½⊗½)⊗1@: fuse @exampleUnfused@ then a spin-1 leaf.
fuseExample2
  :: ToVRep (FuseRep (FuseRep '[ 'Bare 1] '[ 'Bare 1]) '[ 'Bare 2])
fuseExample2 =
  repVToV @(FuseRep (FuseRep '[ 'Bare 1] '[ 'Bare 1]) '[ 'Bare 2]) $
    fuseRepTerm
      (fuseExample exampleUnfused)
      (RCons @('Bare 2) (konst 1) RNil)

-- | Trivial (total-charge-0) sector of 'fuseExample2'.
fuseExample3
  :: ToVRep
       ( FilterTrivial
           (FuseRep (FuseRep '[ 'Bare 1] '[ 'Bare 1]) '[ 'Bare 2])
       )
fuseExample3 =
  repVToV
    @( FilterTrivial
         (FuseRep (FuseRep '[ 'Bare 1] '[ 'Bare 1]) '[ 'Bare 2])
     )
    $ filterTrivialRepV
        @(FuseRep (FuseRep '[ 'Bare 1] '[ 'Bare 1]) '[ 'Bare 2])
        ( fuseRepTerm
            (fuseExample exampleUnfused)
            (RCons @('Bare 2) (konst 1) RNil)
        )

-- | Unfused nested Kronecker @((½⊗½)⊗1)@.
fuseExample4
  :: ToVObj
       ('FObj.Tensor ('FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1)) ('FObj.Atom 2))
fuseExample4 = (konst 1 ⊗ konst 1) ⊗ konst 1

-- | Endomorphism on leaf-½ Hom (singlet / triplet channels).
f :: RepV (FuseRep (ObjRep ('FObj.Atom 1)) (ObjRep ('FObj.Atom 1)))
f =
  RCons @('From 0 '( 'Bare 1, 'Bare 1)) (konst 0.3) $
    RCons @('From 2 '( 'Bare 1, 'Bare 1)) (konst 0.7) RNil

g :: RepV (FuseRep (ObjRep ('FObj.Atom 1)) (ObjRep ('FObj.Atom 1)))
g =
  RCons @('From 0 '( 'Bare 1, 'Bare 1)) (konst 0.5) $
    RCons @('From 2 '( 'Bare 1, 'Bare 1)) (konst (-0.2)) RNil

-- | @g ∘ f@ spelled as the five Mac Lane morphisms in 'composeHomTrees'.
composeFGSteps :: RepV Hom11
composeFGSteps =
  let -- 1. @f ⊗ g@
      step1 = fuseRepTerm @Hom11 @Hom11 f g
      -- 2. outer F: @(a*⊗b) ⊗ (b*⊗c) → a* ⊗ (b ⊗ (b*⊗c))@
      step2 = fmoveOuterHom @Bare1 @Bare1 @Bare1 step1
      -- 3. @id ⊗ F@: @a* ⊗ (b ⊗ (b*⊗c)) → a* ⊗ ((b ⊗ b*) ⊗ c)@
      step3 = fmoveInnerHom @Bare1 @Bare1 @Bare1 step2
      -- 4. @id ⊗ (cup ⊗ id)@: contract the middle Hom to @Unit@
      step4 = cupTensorIdHom @Bare1 @Bare1 @Bare1 step3
      -- 5. @id ⊗ λ@: absorb @Unit@ on the left of @c@
      step5 = unitorHom @Bare1 @Bare1 step4
   in step5

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
  let u0 = unitToVFromScalar 1
      -- Dual-left wire on @Atom 0@: metric dual of the unit packing.
      packed =
        (fromLinearForm $ arr (LinearFunction (<.> u0)))
          ⊗ ( capUnfusedObj @('FObj.Atom 1) u0 ⊗ u0 )
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
-- Objects: spin-½ (@C 2@) → spin-½ → spin-1 (@C 3@). Hom elements are
-- @asTensor@ of the linear maps; @g . f@ is compared to @g ∘ f@ on the
-- standard basis.
composeMorObjMatchesMatMulOk :: Bool
composeMorObjMatchesMatMulOk =
  let -- Irrep maps (column action on coordinate lists).
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
      fHom =
        HomUnfused (asTensor -+$=> fLeg)
          :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
      gHom =
        HomUnfused (asTensor -+$=> gLeg)
          :: HomUnfused ('FObj.Atom 1) ('FObj.Atom 2)
      hHom = gHom . fHom
      h = fromTensor -+$=> unHomUnfused hHom :: C 2 +> C 3
      e0 = unsafeFromArray (VS.fromList [1, 0]) :: C 2
      e1 = unsafeFromArray (VS.fromList [0, 1]) :: C 2
      xs = [e0, e1]
      agree x =
        toVApproxEq (toArray (h $ x)) (toArray (gLeg $ (fLeg $ x)))
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

-- | @cup ∘ (s · id) = s · FS·dim@ on spin-½ (@FS(1)·2 = −2@).
cupCapRoundtripSpinHalfOk :: Bool
cupCapRoundtripSpinHalfOk =
  let u = 0.7 :+ 0
      capped = scaleRepV @Hom11 u (idHomFusedVal @Atom1)
      RCons v RNil = cup @Bare1 capped
   in magnitude ((konst 1 <.> v) - ((-2) * u)) < 1e-9

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
    , cupCapRoundtripSpinHalfOk
    , composeHomTreesSelfTest
    , composeHomTreesBare1TypedOk
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

type family AssertEqSpine (a :: Spine Nat) (b :: Spine Nat) :: Bool where
  AssertEqSpine a a = 'True

type family AssertEqObj (a :: FObj.Obj Nat) (b :: FObj.Obj Nat) :: Bool where
  AssertEqObj a a = 'True

-- | Atom → singleton spine.
type SmokeObjSpineAtom =
  AssertEqSpine (ObjSpineSU2 ('FObj.Atom 1)) '[ '(1, 1)]

-- | @½ ⊗ ½@ FuseNorm → singlet ⊕ triplet multiplicities.
type SmokeObjSpineHalfHalf =
  AssertEqSpine
    (ObjSpineSU2 ('FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1)))
    '[ '(0, 1), '(2, 1)]

-- | Direct sum coalesces and sorts by @2j@.
type SmokeObjSpineSum =
  AssertEqSpine
    (ObjSpineSU2 ('FObj.Sum ('FObj.Atom 2) ('FObj.Atom 0)))
    '[ '(0, 1), '(2, 1)]

-- | Duplicate atoms add multiplicities.
type SmokeObjSpineMult =
  AssertEqSpine
    (ObjSpineSU2 ('FObj.Sum ('FObj.Atom 1) ('FObj.Atom 1)))
    '[ '(1, 2)]

-- | Fused Hom is 'RepV' of 'FuseRep' (genealogy-preserving).
type SmokeHomFused =
  AssertEqType
    (ToVRep (FuseRep '[ 'Bare 1] '[ 'Bare 1]))
    (ToVRep Hom11)

-- | @½ ⊗ ½@ fusion trees: singlet and triplet channels (no coalesce).
type SmokeFuseTrees =
  AssertEqRep
    (FuseTrees ('Bare 1) ('Bare 1))
    '[ 'From 0 '( 'Bare 1, 'Bare 1)
     , 'From 2 '( 'Bare 1, 'Bare 1)
     ]

-- | 'ObjTrees' on an atom is a singleton leaf.
type SmokeObjTreesAtom =
  AssertEqRep (ObjTrees ('FObj.Atom 1)) '[ 'Bare 1]

-- | 'ObjTrees' of @½ ⊗ ½@ matches 'FuseTrees' / 'FuseRep' on leaves.
type SmokeObjTreesHalfHalf =
  AssertEqRep
    (ObjTrees ('FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1)))
    (FuseTrees ('Bare 1) ('Bare 1))

-- | 'ObjTrees' of a sum is flat 'Append' (no coalesce).
type SmokeObjTreesSum =
  AssertEqRep
    (ObjTrees ('FObj.Sum ('FObj.Atom 2) ('FObj.Atom 0)))
    '[ 'Bare 2, 'Bare 0]

-- | 'Norm' then fuse: @(0 ⊕ 1) ⊗ ½@ equals the distributed sum of tensors.
type SmokeObjTreesDist =
  AssertEqRep
    ( ObjTrees
        ('FObj.Tensor
           ('FObj.Sum ('FObj.Atom 0) ('FObj.Atom 2))
           ('FObj.Atom 1))
    )
    ( ObjTrees
        ('FObj.Sum
           ('FObj.Tensor ('FObj.Atom 0) ('FObj.Atom 1))
           ('FObj.Tensor ('FObj.Atom 2) ('FObj.Atom 1)))
    )

-- | Nested tensor keeps association (@ObjTrees@ = left-assoc 'FuseRep').
type SmokeObjTreesAssocL =
  AssertEqRep
    ( ObjTrees
        ('FObj.Tensor
           ('FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 1))
           ('FObj.Atom 1))
    )
    AssocL111

-- | SU(2) simples are self-dual.
type SmokeDualObjAtom =
  AssertEqObj (FObj.DualObj SU2Th ('FObj.Atom 1)) ('FObj.Atom 1)

-- | Dual reverses tensor order (labels unchanged for SU(2)).
type SmokeDualObjTensor =
  AssertEqObj
    ( FObj.DualObj SU2Th
        ('FObj.Tensor ('FObj.Atom 1) ('FObj.Atom 2))
    )
    ('FObj.Tensor ('FObj.Atom 2) ('FObj.Atom 1))

-- | Dual distributes over sums.
type SmokeDualObjSum =
  AssertEqObj
    ( FObj.DualObj SU2Th
        ('FObj.Sum ('FObj.Atom 0) ('FObj.Atom 2))
    )
    ('FObj.Sum ('FObj.Atom 0) ('FObj.Atom 2))

-- | Root of a fusion tree is the channel label.
type SmokeRootNode =
  AssertEqNat
    (Root ('From 0 '( 'Bare 1, 'Bare 1)))
    0

-- | 'ToVTree' is the root irrep space only (@j=1 ⇒ C 2@; @j=2 ⇒ C 3@).
type SmokeToVTree =
  AssertEqType
    (ToVTree ('From 2 '( 'Bare 1, 'Bare 1)))
    (C 3)

-- | 'ToVRep' nests root spaces.
type SmokeToVRep =
  AssertEqType
    (ToVRep (FuseTrees ('Bare 1) ('Bare 1)))
    (C 1, C 3)

-- | List fuse distributes over tree pairs.
type SmokeFuseRep =
  AssertEqRep
    (FuseRep '[ 'Bare 1] '[ 'Bare 1])
    (FuseTrees ('Bare 1) ('Bare 1))

-- | Left-assoc @½⊗½⊗½@ equals the concrete 'AssocL111' spine used by 'fmoveTrees111'.
type SmokeAssocL111 =
  AssertEqRep
    ( FuseRep (FuseRep '[ 'Bare 1] '[ 'Bare 1]) '[ 'Bare 1] )
    AssocL111

type SmokeAssocR111 =
  AssertEqRep
    ( FuseRep '[ 'Bare 1] (FuseRep '[ 'Bare 1] '[ 'Bare 1]) )
    AssocR111

type SmokeAssocL110 =
  AssertEqRep
    ( FuseRep (FuseRep '[ 'Bare 1] '[ 'Bare 1]) '[ 'Bare 0] )
    AssocL110

type SmokeAssocR110 =
  AssertEqRep
    ( FuseRep '[ 'Bare 1] (FuseRep '[ 'Bare 1] '[ 'Bare 0]) )
    AssocR110

type SmokeAssocL112 =
  AssertEqRep
    ( FuseRep (FuseRep '[ 'Bare 1] '[ 'Bare 1]) '[ 'Bare 2] )
    AssocL112

type SmokeAssocR112 =
  AssertEqRep
    ( FuseRep '[ 'Bare 1] (FuseRep '[ 'Bare 1] '[ 'Bare 2]) )
    AssocR112

-- | Concrete Leaf-½ Hom-compose spines match 'FuseRep' expansions.
type SmokeHom11 =
  AssertEqRep
    (FuseRep '[ 'Bare 1] '[ 'Bare 1])
    Hom11

type SmokeDom111 =
  AssertEqRep
    (FuseRep Hom11 Hom11)
    Dom111

type SmokeMid111 =
  AssertEqRep
    (FuseRep '[ 'Bare 1] AssocR111)
    Mid111

type SmokeCupR111 =
  AssertEqRep
    (FuseRep '[ 'Bare 1] AssocL111)
    CupR111

-- | Nested outer-F codomain (Mac Lane step 2) equals 'Mid111'.
type SmokeAfterOuterF111 =
  AssertEqRep
    ( FuseRep
        '[ 'Bare 1]
        (FuseRep '[ 'Bare 1] (FuseRep '[ 'Bare 1] '[ 'Bare 1]))
    )
    Mid111

-- | Nested cup-ready spine (Mac Lane step 3) equals 'CupR111'.
type SmokeCupReady111 =
  AssertEqRep
    ( FuseRep
        '[ 'Bare 1]
        (FuseRep (FuseRep '[ 'Bare 1] '[ 'Bare 1]) '[ 'Bare 1])
    )
    CupR111

-- | After @id ⊗ (cup ⊗ id)@: Unit remains as 'Unit' in the middle.
type SmokeAfterCup111 =
  AssertEqRep
    (FuseRep '[ 'Bare 1] (FuseRep Unit '[ 'Bare 1]))
    '[ 'From 0 '( 'Bare 1, 'From 1 '( 'Bare 0, 'Bare 1))
     , 'From 2 '( 'Bare 1, 'From 1 '( 'Bare 0, 'Bare 1))
     ]

type SmokeHom00 =
  AssertEqRep
    (FuseRep '[ 'Bare 0] '[ 'Bare 0])
    Hom00

type SmokeDom000 =
  AssertEqRep
    (FuseRep Hom00 Hom00)
    Dom000

type SmokeCupR000 =
  AssertEqRep
    (FuseRep '[ 'Bare 0] (FuseRep Hom00 '[ 'Bare 0]))
    CupR000

-- | Flat layout equals reduced HMatrix packing for @½⊗½⊗½@ (both associations).
smokeObjSpineAtom :: Proxy SmokeObjSpineAtom
smokeObjSpineAtom = Proxy

smokeObjSpineHalfHalf :: Proxy SmokeObjSpineHalfHalf
smokeObjSpineHalfHalf = Proxy

smokeObjSpineSum :: Proxy SmokeObjSpineSum
smokeObjSpineSum = Proxy

smokeObjSpineMult :: Proxy SmokeObjSpineMult
smokeObjSpineMult = Proxy

smokeHomFused :: Proxy SmokeHomFused
smokeHomFused = Proxy

smokeFuseTrees :: Proxy SmokeFuseTrees
smokeFuseTrees = Proxy

smokeObjTreesAtom :: Proxy SmokeObjTreesAtom
smokeObjTreesAtom = Proxy

smokeObjTreesHalfHalf :: Proxy SmokeObjTreesHalfHalf
smokeObjTreesHalfHalf = Proxy

smokeObjTreesSum :: Proxy SmokeObjTreesSum
smokeObjTreesSum = Proxy

smokeObjTreesDist :: Proxy SmokeObjTreesDist
smokeObjTreesDist = Proxy

smokeObjTreesAssocL :: Proxy SmokeObjTreesAssocL
smokeObjTreesAssocL = Proxy

smokeDualObjAtom :: Proxy SmokeDualObjAtom
smokeDualObjAtom = Proxy

smokeDualObjTensor :: Proxy SmokeDualObjTensor
smokeDualObjTensor = Proxy

smokeDualObjSum :: Proxy SmokeDualObjSum
smokeDualObjSum = Proxy

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
    && checkFmoveTreesLeaves @1 @2 @1 (fillRepVScaled @( FuseRep (FuseRep Bare1 Bare2) Bare1 ))

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
      mid = fuseTensorTrees @Bare1 @AssocR111 (TensorTrees leaf assocR)
      cupGen = fuseMapRightFinv111 mid
      expected =
        fuseTensorTrees @Bare1 @AssocL111 $
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
    && checkHomInterCategory111
    && checkForgetHomFusedId111
    && checkForgetHomInterCompose111
    && checkBare2FmoveSmoke
    && checkFmoveOuter111
    && checkFuseMapLeftId111
    && checkUnitorBare1
    && checkUnitorHom11
    && checkCupBareHom

composeHomTreesSelfTestOk :: ()
composeHomTreesSelfTestOk =
  if composeHomTreesSelfTest
    then ()
    else error "composeHomTreesSelfTest failed: id/unit laws on leaf Hom"

-- | Typechecks five-morphism 'composeHomTrees' at leaf-½ (do not evaluate).
composeHomTreesBare1
  :: RepV Hom11 -> RepV Hom11 -> RepV Hom11
composeHomTreesBare1 = composeHomTrees @Bare1 @Bare1 @Bare1

composeHomTreesBare1TypedOk :: Bool
composeHomTreesBare1TypedOk =
  let _ty = composeHomTreesBare1
      _cup = cupTensorIdHomBare1
   in True
