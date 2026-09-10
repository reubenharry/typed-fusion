{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Smokes for 'Hom': term-level checks and compile-time type equalities.
-- Covers Dual-left 'HomUnfused' and genealogy 'HomFused' / 'composeHomTrees'.
-- Unit laws: 'composeHomTreesSelfTest'.
-- Fused cup/cap: genealogy 'cup' / 'idHomFTrees'.
-- Phase-1 fusion trees: 'FuseTrees' / 'ToVTree' / 'Root'.
module Hom.Examples where

import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..), id)
import Data.Complex (Complex ((:+)), magnitude)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (InnerSpace ((<.>)), (*^), (^-^))
import Categorical.Associative (Associative (..))
import Categorical.Bifunctor (Bifunctor (..))
import Fusion.Obj (Obj (Atom, (:⊗:), (:⊕:)), DualObj)
import Fusion.SU2 (SU2Th, Spin (..), TJ, type (/))
import Hom
import GHC.TypeLits (Nat)
import Math.LinearMap.Category
  ( DualVector
  , fromLinearForm
  , pattern LinearFunction
  , type (+>)
  , type (⊗)
  , (⊗), AdditiveGroup ((^+^))
  )
import Math.LinearMap.Category.Class (asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, konst)
import qualified Data.Vector.Storable as VS

import Prelude hiding (id, (.), ($))
import Categorical.Linear (runit, swapMap)
import Hom.Vec (vec)
import Data.IndexedListLiterals (Only(..))

exampleRep :: RepV '[ Irr' (1 / 2), Irr' (3 / 2)]
exampleRep =
  RCons @(Irr' (1 / 2)) (konst 1) $
    RCons @(Irr' (3 / 2)) (konst 1) RNil

exampleUnfused :: ToVObj ((('Atom (TJ (1 / 2))) :⊗: ('Atom (TJ (1 / 2)))))
exampleUnfused = konst 1 ⊗ konst 1

example :: RepV (FuseRep '[ 'I (TJ (1 / 2))] '[ 'I (TJ (1 / 2))])
example = undefined

type TW = (('Atom (TJ (1 / 2))) :⊗: ('Atom (TJ (1 / 2))))

type Irr' (s :: Spin) = 'I (TJ s)
type Irr (s :: Spin) = 'Atom (TJ s)
type (:**:) (a :: Spin) (b :: Spin) = RepV (FuseRep (ObjRep (Irr a)) (ObjRep (Irr b)))
type Unfused obj =  ToVObj obj

-- Leaf: FTree
-- Node: a `From` (b,c) 

type Dual (a :: Obj Nat) = DualObj SU2Th a

type Fused obj = ToVRep (ObjTrees obj)
type Sym obj = ToVRep (FilterTrivial (ObjTrees obj))

foo :: Unfused (Dual (Irr (1/2) :⊗: Irr (1/2)) :⊗: Irr (2/2) )
foo =  ((vec (1,2) ⊗ vec (1,2)) ⊗ vec (1,2,3)) ^+^ (vec (4,2) ⊗ vec (1,2)) ⊗ vec (1,2,7)

bar :: Fused ( Dual ( Irr (1/2) :⊗: Irr (1/2)) :⊗: Irr (2/2))
bar = (vec (1,2,3), (konst 1, (vec ( 2,3,4), vec (5,6,7,8,9))))

baz :: Sym ( Dual ( Irr (1/2) :⊗: Irr (1/2)) :⊗: Irr (2/2))
baz = konst 1

fuseExample
  :: ToVObj ((('Atom (TJ (1 / 2))) :⊗: ('Atom (TJ (1 / 2)))))
  -> RepV '[ 'From 0 '( 'I (TJ (1 / 2)), 'I (TJ (1 / 2))), 'From 2 '( 'I (TJ (1 / 2)), 'I (TJ (1 / 2)))]
fuseExample = fuseTrees @('I (TJ (1 / 2))) @('I (TJ (1 / 2)))

-- | Genealogy @(½⊗½)⊗1@: fuse @exampleUnfused@ then a spin-1 leaf.
fuseExample2
  :: ToVRep (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2])
fuseExample2 =
  repVToV @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2]) $
    fuseRepTerm
      (fuseExample exampleUnfused)
      (RCons @('I 2) (konst 1) RNil)

-- | Trivial (total-charge-0) sector of 'fuseExample2'.
fuseExample3
  :: ToVRep
       ( FilterTrivial
           (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2])
       )
fuseExample3 =
  repVToV
    @( FilterTrivial
         (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2])
     )
    $ filterTrivialRepV
        @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2])
        ( fuseRepTerm
            (fuseExample exampleUnfused)
            (RCons @('I 2) (konst 1) RNil)
        )

-- | Unfused nested Kronecker @((½⊗½)⊗1)@.
fuseExample4
  :: ToVObj
       ((((('Atom 1) :⊗: ('Atom 1))) :⊗: ('Atom 2)))
fuseExample4 = (konst 1 ⊗ konst 1) ⊗ konst 1

-- | Endomorphism on leaf-½ Hom (singlet / triplet channels).
f :: RepV (FuseRep (ObjRep ('Atom 1)) (ObjRep ('Atom 1)))
f =
  RCons @('From 0 '( 'I 1, 'I 1)) (konst 0.3) $
    RCons @('From 2 '( 'I 1, 'I 1)) (konst 0.7) RNil

g :: RepV (FuseRep (ObjRep ('Atom 1)) (ObjRep ('Atom 1)))
g =
  RCons @('From 0 '( 'I 1, 'I 1)) (konst 0.5) $
    RCons @('From 2 '( 'I 1, 'I 1)) (konst (-0.2)) RNil

-- | @g ∘ f@ spelled as the five Mac Lane morphisms in 'composeHomTrees'.
composeFGSteps :: RepV (FuseRep '[ 'I 1] '[ 'I 1])
composeFGSteps =
  let -- 1. @f ⊗ g@
      step1 =
        fuseRepTerm
          @(FuseRep '[ 'I 1] '[ 'I 1])
          @(FuseRep '[ 'I 1] '[ 'I 1])
          f
          g
      -- 2. outer F: @(a*⊗b) ⊗ (b*⊗c) → a* ⊗ (b ⊗ (b*⊗c))@
      step2 = fmoveOuterHom @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) step1
      -- 3. @id ⊗ F@: @a* ⊗ (b ⊗ (b*⊗c)) → a* ⊗ ((b ⊗ b*) ⊗ c)@
      step3 = fmoveInnerHom @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) step2
      -- 4. @id ⊗ (cup ⊗ id)@: contract the middle Hom to @Unit@
      step4 = cupTensorIdHom @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) step3
      -- 5. @id ⊗ λ@: absorb @Unit@ on the left of @c@
      step5 = unitorHom @('[ 'I 1]) @('[ 'I 1]) step4
   in step5

-- | Right unitor absorbs @Unit@ on Dual-left HomUnfused (@m ⊗ 1 ≅ m@).
runitMorTrivialOk :: Bool
runitMorTrivialOk =
  let m = (5 :+ 0) *^ capUnfusedObj @('Atom 0) (konst 1)
      u = konst 1
   in toVApproxEq
        (toArray
           ( runit
               @( DualVector (ToVObj ('Atom 0))
                    ⊗ ToVObj ('Atom 0)
                )
               $ (m ⊗ u)
           ))
        (toArray m)

-- | @(cup ⊗ id)@ then unitor on a packed assoc-shape state: @cup(η_b) = dim b@.
cupTensorIdUnitorOk :: Bool
cupTensorIdUnitorOk =
  let u0 = konst 1
      -- Right-dual @η_b : I → b* ⊗ b@, braided to @b ⊗ b*@ for @ε@.
      packed =
        (fromLinearForm $ arr (LinearFunction (<.> u0)))
          ⊗ ( (swapMap $ capUnfusedObj @('Atom 1) u0) ⊗ u0 )
      out =
        unitorComposeObj
          @('Atom 0)
          @('Atom 0)
          ( cupTensorIdComposeObj
              @('Atom 0)
              @('Atom 1)
              @('Atom 0)
              packed
          )
      -- @ε ∘ σ ∘ η = dim b@ on spin-½; result is scale on Dual-left id.
      expected = 2 *^ capUnfusedObj @('Atom 0) (konst 1)
   in all (\(x, y) -> magnitude (x - y) < 1e-9)
        (zip (VS.toList (toArray out)) (VS.toList (toArray expected)))

toVApproxEq :: VS.Vector (Complex Double) -> VS.Vector (Complex Double) -> Bool
toVApproxEq u v =
  VS.length u == VS.length v
    && VS.and (VS.zipWith (\x y -> magnitude (x - y) < 1e-9) u v)

-- | @composeMorObj id id ≅ id@ on @j = 0@.
composeMorObjIdIdTrivialOk :: Bool
composeMorObjIdIdTrivialOk =
  let i = id :: HomUnfused ('Atom 0) ('Atom 0)
   in toVApproxEq
        (toArray (unHomUnfused (i . i)))
        (toArray (unHomUnfused i))

-- | Left unit law: @id ∘ f ≅ f@ on spin-½ ('HomUnfused').
composeMorObjLeftUnitOk :: Bool
composeMorObjLeftUnitOk =
  let i = id :: HomUnfused ('Atom 1) ('Atom 1)
      f =
        HomUnfused ((3 :+ 0) *^ unHomUnfused i)
          :: HomUnfused ('Atom 1) ('Atom 1)
   in toVApproxEq
        (toArray (unHomUnfused (i . f)))
        (toArray (unHomUnfused f))

-- | Right unit law: @f ∘ id ≅ f@ on spin-½ ('HomUnfused').
composeMorObjRightUnitOk :: Bool
composeMorObjRightUnitOk =
  let i = id :: HomUnfused ('Atom 1) ('Atom 1)
      f =
        HomUnfused ((3 :+ 0) *^ unHomUnfused i)
          :: HomUnfused ('Atom 1) ('Atom 1)
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
  let -- FTree maps (column action on coordinate lists).
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
          :: HomUnfused ('Atom 1) ('Atom 1)
      gHom =
        HomUnfused (asTensor -+$=> gLeg)
          :: HomUnfused ('Atom 1) ('Atom 2)
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
  let i = id :: HomUnfused ('Atom 1) ('Atom 1)
   in toVApproxEq
        (toArray (unHomUnfused (i . i)))
        (toArray (unHomUnfused i))

-- | @bimap id id ≅ id@ on @½ ⊗ ½@ (true unfused Hom).
bimapHomUnfusedIdIdOk :: Bool
bimapHomUnfusedIdIdOk =
  let iHalf = id :: HomUnfused ('Atom 1) ('Atom 1)
      iTen =
        id
          :: HomUnfused
               ((('Atom 1) :⊗: ('Atom 1)))
               ((('Atom 1) :⊗: ('Atom 1)))
      bi =
        bimap iHalf iHalf
          :: HomUnfused
               ((('Atom 1) :⊗: ('Atom 1)))
               ((('Atom 1) :⊗: ('Atom 1)))
   in toVApproxEq (toArray (unHomUnfused bi)) (toArray (unHomUnfused iTen))
-- | @disassociate ∘ associate ≅ id@ as linear maps on @(½ ⊗ ½) ⊗ ½@
-- (Hom packing of linearmap α / α⁻¹; avoids Hom-compose cost on the smoke).
associateHomUnfusedRoundtripOk :: Bool
associateHomUnfusedRoundtripOk =
  let α =
        unHomUnfused
          ( associate
              :: HomUnfused
                   ( (((('Atom 1) :⊗: ('Atom 1))) :⊗: ('Atom 1))
                   )
                   ( (('Atom 1) :⊗: ((('Atom 1) :⊗: ('Atom 1))))
                   )
          )
      αinv =
        unHomUnfused
          ( disassociate
              :: HomUnfused
                   ( (('Atom 1) :⊗: ((('Atom 1) :⊗: ('Atom 1))))
                   )
                   ( (((('Atom 1) :⊗: ('Atom 1))) :⊗: ('Atom 1))
                   )
          )
      roundTrip =
        (fromTensor -+$=> αinv)
          . (fromTensor -+$=> α)
            :: ToVObj
                 ( (((('Atom 1) :⊗: ('Atom 1))) :⊗: ('Atom 1))
                 )
               +> ToVObj
                    ( (((('Atom 1) :⊗: ('Atom 1))) :⊗: ('Atom 1))
                    )
      iHom =
        unHomUnfused
          ( id
              :: HomUnfused
                   ( (((('Atom 1) :⊗: ('Atom 1))) :⊗: ('Atom 1))
                   )
                   ( (((('Atom 1) :⊗: ('Atom 1))) :⊗: ('Atom 1))
                   )
          )
   in toVApproxEq
        (toArray (asTensor -+$=> roundTrip))
        (toArray iHom)

-- | @cup ∘ (s · id) = s · FS·dim@ on spin-½ (@FS(1)·2 = −2@).
cupCapRoundtripSpinHalfOk :: Bool
cupCapRoundtripSpinHalfOk =
  let u = 0.7 :+ 0
      capped =
        scaleRepV
          @(FuseRep '[ 'I 1] '[ 'I 1])
          u
          (idHomFTrees @('[ 'I 1]))
      RCons v RNil = cup @('[ 'I 1]) capped
   in magnitude ((konst 1 <.> v) - ((-2) * u)) < 1e-9

-- | All symbolic smokes in one place (for REPL / probes).
symbolicExamplesOk :: Bool
symbolicExamplesOk =
  and
    [ runitMorTrivialOk
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
    , composeHomTreesI1TypedOk
    ]


--------------------------------------------------------------------------------
-- Compile-time smokes (type equalities)
--------------------------------------------------------------------------------

type family AssertEqNat (a :: Nat) (b :: Nat) :: Bool where
  AssertEqNat a a = 'True

type family AssertEqFTrees (a :: FTrees) (b :: FTrees) :: Bool where
  AssertEqFTrees a a = 'True

type family AssertEqType (a :: Type) (b :: Type) :: Bool where
  AssertEqType a a = 'True

type family AssertEqFTree (a :: FTree) (b :: FTree) :: Bool where
  AssertEqFTree a a = 'True

type family AssertEqSpine (a :: Spine Nat) (b :: Spine Nat) :: Bool where
  AssertEqSpine a a = 'True

type family AssertEqObj (a :: Obj Nat) (b :: Obj Nat) :: Bool where
  AssertEqObj a a = 'True

-- | Atom → singleton spine.
type SmokeObjSpineAtom =
  AssertEqSpine (ObjSpineSU2 ('Atom 1)) '[ '(1, 1)]

-- | @½ ⊗ ½@ FuseNorm → singlet ⊕ triplet multiplicities.
type SmokeObjSpineHalfHalf =
  AssertEqSpine
    (ObjSpineSU2 ((('Atom 1) :⊗: ('Atom 1))))
    '[ '(0, 1), '(2, 1)]

-- | Direct sum coalesces and sorts by @2j@.
type SmokeObjSpineSum =
  AssertEqSpine
    (ObjSpineSU2 ((('Atom 2) :⊕: ('Atom 0))))
    '[ '(0, 1), '(2, 1)]

-- | Duplicate atoms add multiplicities.
type SmokeObjSpineMult =
  AssertEqSpine
    (ObjSpineSU2 ((('Atom 1) :⊕: ('Atom 1))))
    '[ '(1, 2)]

-- | Fused Hom is 'RepV' of 'FuseRep' (genealogy-preserving).
type SmokeHomFused =
  AssertEqType
    (ToVRep (FuseRep '[ 'I 1] '[ 'I 1]))
    (C 1, C 3)

-- | @½ ⊗ ½@ fusion trees: singlet and triplet channels (no coalesce).
type SmokeFuseTrees =
  AssertEqFTrees
    (FuseTrees ('I 1) ('I 1))
    '[ 'From 0 '( 'I 1, 'I 1)
     , 'From 2 '( 'I 1, 'I 1)
     ]

-- | 'ObjTrees' on an atom is a singleton leaf.
type SmokeObjTreesAtom =
  AssertEqFTrees (ObjTrees ('Atom 1)) '[ 'I 1]

-- | 'ObjTrees' of @½ ⊗ ½@ matches 'FuseTrees' / 'FuseRep' on leaves.
type SmokeObjTreesHalfHalf =
  AssertEqFTrees
    (ObjTrees ((('Atom 1) :⊗: ('Atom 1))))
    (FuseTrees ('I 1) ('I 1))

-- | 'ObjTrees' of a sum is flat 'Append' (no coalesce).
type SmokeObjTreesSum =
  AssertEqFTrees
    (ObjTrees ((('Atom 2) :⊕: ('Atom 0))))
    '[ 'I 2, 'I 0]

-- | 'Norm' then fuse: @(0 ⊕ 1) ⊗ ½@ equals the distributed sum of tensors.
type SmokeObjTreesDist =
  AssertEqFTrees
    ( ObjTrees
        ((((('Atom 0) :⊕: ('Atom 2))) :⊗: ('Atom 1)))
    )
    ( ObjTrees
        ((((('Atom 0) :⊗: ('Atom 1))) :⊕: ((('Atom 2) :⊗: ('Atom 1)))))
    )

-- | Nested tensor keeps association (@ObjTrees@ = left-assoc 'FuseRep').
type SmokeObjTreesAssocL =
  AssertEqFTrees
    ( ObjTrees
        ((((('Atom 1) :⊗: ('Atom 1))) :⊗: ('Atom 1)))
    )
    (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1])

-- | SU(2) simples are self-dual.
type SmokeDualObjAtom =
  AssertEqObj (DualObj SU2Th ('Atom 1)) ('Atom 1)

-- | Dual reverses tensor order (labels unchanged for SU(2)).
type SmokeDualObjTensor =
  AssertEqObj
    ( DualObj SU2Th
        ((('Atom 1) :⊗: ('Atom 2)))
    )
    ((('Atom 2) :⊗: ('Atom 1)))

-- | Dual distributes over sums.
type SmokeDualObjSum =
  AssertEqObj
    ( DualObj SU2Th
        ((('Atom 0) :⊕: ('Atom 2)))
    )
    ((('Atom 0) :⊕: ('Atom 2)))

-- | Root of a fusion tree is the channel label.
type SmokeRootNode =
  AssertEqNat
    (Root ('From 0 '( 'I 1, 'I 1)))
    0

-- | 'ToVTree' is the root irrep space only (@j=1 ⇒ C 2@; @j=2 ⇒ C 3@).
type SmokeToVTree =
  AssertEqType
    (ToVTree ('From 2 '( 'I 1, 'I 1)))
    (C 3)

-- | 'ToVRep' nests root spaces.
type SmokeToVRep =
  AssertEqType
    (ToVRep (FuseTrees ('I 1) ('I 1)))
    (C 1, C 3)

-- | List fuse distributes over tree pairs.
type SmokeFuseRep =
  AssertEqFTrees
    (FuseRep '[ 'I 1] '[ 'I 1])
    (FuseTrees ('I 1) ('I 1))

-- | Left-assoc @½⊗½⊗½@ expands to the concrete 'From' spine.
type SmokeAssocL111 =
  AssertEqFTrees
    ( FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1] )
    '[ 'From 1 '( 'From 0 '( 'I 1, 'I 1), 'I 1)
     , 'From 1 '( 'From 2 '( 'I 1, 'I 1), 'I 1)
     , 'From 3 '( 'From 2 '( 'I 1, 'I 1), 'I 1)
     ]

type SmokeAssocR111 =
  AssertEqFTrees
    ( FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 1]) )
    '[ 'From 1 '( 'I 1, 'From 0 '( 'I 1, 'I 1))
     , 'From 1 '( 'I 1, 'From 2 '( 'I 1, 'I 1))
     , 'From 3 '( 'I 1, 'From 2 '( 'I 1, 'I 1))
     ]

type SmokeAssocL110 =
  AssertEqFTrees
    ( FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 0] )
    '[ 'From 0 '( 'From 0 '( 'I 1, 'I 1), 'I 0)
     , 'From 2 '( 'From 2 '( 'I 1, 'I 1), 'I 0)
     ]

type SmokeAssocR110 =
  AssertEqFTrees
    ( FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 0]) )
    '[ 'From 0 '( 'I 1, 'From 1 '( 'I 1, 'I 0))
     , 'From 2 '( 'I 1, 'From 1 '( 'I 1, 'I 0))
     ]

type SmokeAssocL112 =
  AssertEqFTrees
    ( FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2] )
    '[ 'From 2 '( 'From 0 '( 'I 1, 'I 1), 'I 2)
     , 'From 0 '( 'From 2 '( 'I 1, 'I 1), 'I 2)
     , 'From 2 '( 'From 2 '( 'I 1, 'I 1), 'I 2)
     , 'From 4 '( 'From 2 '( 'I 1, 'I 1), 'I 2)
     ]

type SmokeAssocR112 =
  AssertEqFTrees
    ( FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 2]) )
    '[ 'From 0 '( 'I 1, 'From 1 '( 'I 1, 'I 2))
     , 'From 2 '( 'I 1, 'From 1 '( 'I 1, 'I 2))
     , 'From 2 '( 'I 1, 'From 3 '( 'I 1, 'I 2))
     , 'From 4 '( 'I 1, 'From 3 '( 'I 1, 'I 2))
     ]

-- | After @id ⊗ (cup ⊗ id)@: Unit remains as 'Unit' in the middle.
type SmokeAfterCup111 =
  AssertEqFTrees
    (FuseRep '[ 'I 1] (FuseRep Unit '[ 'I 1]))
    '[ 'From 0 '( 'I 1, 'From 1 '( 'I 0, 'I 1))
     , 'From 2 '( 'I 1, 'From 1 '( 'I 0, 'I 1))
     ]

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

smokeAfterCup111 :: Proxy SmokeAfterCup111
smokeAfterCup111 = Proxy

-- | Sample left-assoc @½⊗½⊗½@ state for F-move self-tests.
sampleAssocL111 :: RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1])
sampleAssocL111 =
  vToRepV @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1])
    (konst 1, (konst 0.5, konst 0.25))

sampleAssocL110 :: RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 0])
sampleAssocL110 =
  vToRepV @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 0])
    (konst 1, konst 0.5)

sampleAssocL112 :: RepV (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2])
sampleAssocL112 =
  vToRepV @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 2])
    (konst 1, (konst 0.5, (konst 0.25, konst 0.125)))

-- | Tree F-move round-trips (@F⁻¹ ∘ F ≈ id@) on concrete triples + @½⊗1⊗½@.
fmoveTreesSelfTest :: Bool
fmoveTreesSelfTest =
  checkFmoveTrees111 sampleAssocL111
    && checkFmoveTrees110 sampleAssocL110
    && checkFmoveTrees112 sampleAssocL112
    && checkFmoveTreesLeaves @1 @2 @1
         (fillRepVScaled @( FuseRep (FuseRep '[ 'I 1] '[ 'I 2]) '[ 'I 1] ))

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
      assocR =
        vToRepV @(FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 1]))
          (konst 0.5, (konst 0.25, konst 0.125))
      mid =
        fuseTensorTrees
          @('[ 'I 1])
          @(FuseRep '[ 'I 1] (FuseRep '[ 'I 1] '[ 'I 1]))
          (TensorTrees leaf assocR)
      cupGen = fuseMapRightFinv111 mid
      expected =
        fuseTensorTrees
          @('[ 'I 1])
          @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1])
          $ TensorTrees leaf (fmoveInvTrees111 assocR)
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
   in approxHom16
        (repVToV @(FuseRep '[ 'I 1] (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1])) cupGen)
        (repVToV @(FuseRep '[ 'I 1] (FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) '[ 'I 1])) expected)

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
    && checkI2FmoveSmoke
    && checkFmoveOuter111
    && checkFuseMapLeftId111
    && checkUnitorI1
    && checkUnitorHom11
    && checkCupIHom

composeHomTreesSelfTestOk :: ()
composeHomTreesSelfTestOk =
  if composeHomTreesSelfTest
    then ()
    else error "composeHomTreesSelfTest failed: id/unit laws on leaf Hom"

-- | Typechecks five-morphism 'composeHomTrees' at leaf-½ (do not evaluate).
composeHomTreesI1
  :: RepV (FuseRep '[ 'I 1] '[ 'I 1])
  -> RepV (FuseRep '[ 'I 1] '[ 'I 1])
  -> RepV (FuseRep '[ 'I 1] '[ 'I 1])
composeHomTreesI1 = composeHomTrees @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1])

composeHomTreesI1TypedOk :: Bool
composeHomTreesI1TypedOk =
  let _ty = composeHomTreesI1
      _cup = cupTensorIdHomI1
   in True
