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
module Examples.Symbolic where

import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..), id)
import Data.Complex (Complex ((:+)), magnitude)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (InnerSpace ((<.>)), (*^), (^-^))
import Categorical.Associative (Associative (..))
import Categorical.Bifunctor (Bifunctor (..))
import Fusion.Obj (Obj (Irrep, (:⊗:), (:⊕:)), DualObj)
import Fusion.SU2 (SU2Th, Spin, type (/))
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

-- exampleFTreeV :: FTreeV '[ 'IrrepTree (Spin (1 / 2)), 'IrrepTree (Spin (3 / 2))]
example1 :: Unfused ('Irrep (Spin (1 / 2)) :⊕: 'Irrep (Spin (3 / 2)))
example1 = (vec (1,2), vec (3,4,5,6))

example2 :: Unfused ('Irrep (Spin (1 / 2)) :⊗: 'Irrep (Spin (1 / 2)))
example2 = vec (1,2) ⊗ vec (3,4) ^+^ vec (5,6) ⊗ vec (7,8)

example3 :: Fused ('Irrep (Spin (1 / 2)) :⊗: 'Irrep (Spin (1 / 2)))
example3 = (konst 1, vec (4,5,6))

example4 :: Sym ('Irrep (Spin (1 / 2)) :⊗: 'Irrep (Spin (1 / 2)))
example4 = konst 2

example5 :: Unfused (Dual ('Irrep (Spin (1 / 2)) :⊗: 'Irrep (Spin (1 / 2))) :⊗: 'Irrep (Spin (2 / 2)))
example5 =  ((vec (1,2) ⊗ vec (1,2)) ⊗ vec (1,2,3)) ^+^ (vec (4,2) ⊗ vec (1,2)) ⊗ vec (1,2,7)

example6 :: Fused (Dual ('Irrep (Spin (1 / 2)) :⊗: 'Irrep (Spin (1 / 2))) :⊗: 'Irrep (Spin (2 / 2)))
example6 = (vec (1,2,3), (konst 1, (vec ( 2,3,4), vec (5,6,7,8,9))))

example7 :: Sym (Dual ('Irrep (Spin (1 / 2)) :⊗: 'Irrep (Spin (1 / 2))) :⊗: 'Irrep (Spin (2 / 2)))
example7 = konst 1



type Dual (a :: Obj Nat) = DualObj SU2Th a




fuseExample :: ToVFTrees '[  
    0 `From` '( 'IrrepTree (Spin (1 / 2)), 'IrrepTree (Spin (1 / 2))), 
    2 `From` '( 'IrrepTree (Spin (1 / 2)), 'IrrepTree (Spin (1 / 2)))]
fuseExample = fTreeVToV $ fuseTrees @('IrrepTree (Spin (1 / 2))) @('IrrepTree (Spin (1 / 2))) example2


-- | Trivial (total-charge-0) sector of 'fuseExample2'.
fuseExample3
  :: ToVFTrees
       ( FilterTrivial
           (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
       )
fuseExample3 =
  fTreeVToV
    @( FilterTrivial
         (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
     )
    $ filterTrivialFTreeV
        @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
        ( fuseFTreesTerm
            (fuseExample example2)
            (FCons @('IrrepTree 2) (konst 1) FNil)
        )

-- | Unfused nested Kronecker @((½⊗½)⊗1)@.
fuseExample4
  :: ToVObj
       ((((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 2)))
fuseExample4 = (konst 1 ⊗ konst 1) ⊗ konst 1

-- | Endomorphism on leaf-½ Hom (singlet / triplet channels).
f :: FTreeV (FuseFTrees (ObjFTrees ('Irrep 1)) (ObjFTrees ('Irrep 1)))
f =
  FCons @('From 0 '( 'IrrepTree 1, 'IrrepTree 1)) (konst 0.3) $
    FCons @('From 2 '( 'IrrepTree 1, 'IrrepTree 1)) (konst 0.7) FNil

g :: FTreeV (FuseFTrees (ObjFTrees ('Irrep 1)) (ObjFTrees ('Irrep 1)))
g =
  FCons @('From 0 '( 'IrrepTree 1, 'IrrepTree 1)) (konst 0.5) $
    FCons @('From 2 '( 'IrrepTree 1, 'IrrepTree 1)) (konst (-0.2)) FNil

-- | @g ∘ f@ spelled as the five Mac Lane morphisms in 'composeHomTrees'.
composeFGSteps :: FTreeV (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
composeFGSteps =
  let -- 1. @f ⊗ g@
      step1 =
        fuseFTreesTerm
          @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
          @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
          f
          g
      -- 2. outer F: @(a*⊗b) ⊗ (b*⊗c) → a* ⊗ (b ⊗ (b*⊗c))@
      step2 = fmoveOuterHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) step1
      -- 3. @id ⊗ F@: @a* ⊗ (b ⊗ (b*⊗c)) → a* ⊗ ((b ⊗ b*) ⊗ c)@
      step3 = fmoveInnerHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) step2
      -- 4. @id ⊗ (cup ⊗ id)@: contract the middle Hom to @Unit@
      step4 = cupTensorIdHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) step3
      -- 5. @id ⊗ λ@: absorb @Unit@ on the left of @c@
      step5 = unitorHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) step4
   in step5

-- | Right unitor absorbs @Unit@ on Dual-left HomUnfused (@m ⊗ 1 ≅ m@).
runitMorTrivialOk :: Bool
runitMorTrivialOk =
  let m = (5 :+ 0) *^ capUnfusedObj @('Irrep 0) (konst 1)
      u = konst 1
   in toVApproxEq
        (toArray
           ( runit
               @( DualVector (ToVObj ('Irrep 0))
                    ⊗ ToVObj ('Irrep 0)
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
          ⊗ ( (swapMap $ capUnfusedObj @('Irrep 1) u0) ⊗ u0 )
      out =
        unitorComposeObj
          @('Irrep 0)
          @('Irrep 0)
          ( cupTensorIdComposeObj
              @('Irrep 0)
              @('Irrep 1)
              @('Irrep 0)
              packed
          )
      -- @ε ∘ σ ∘ η = dim b@ on spin-½; result is scale on Dual-left id.
      expected = 2 *^ capUnfusedObj @('Irrep 0) (konst 1)
   in all (\(x, y) -> magnitude (x - y) < 1e-9)
        (zip (VS.toList (toArray out)) (VS.toList (toArray expected)))

toVApproxEq :: VS.Vector (Complex Double) -> VS.Vector (Complex Double) -> Bool
toVApproxEq u v =
  VS.length u == VS.length v
    && VS.and (VS.zipWith (\x y -> magnitude (x - y) < 1e-9) u v)

-- | @composeMorObj id id ≅ id@ on @j = 0@.
composeMorObjIdIdTrivialOk :: Bool
composeMorObjIdIdTrivialOk =
  let i = id :: HomUnfused ('Irrep 0) ('Irrep 0)
   in toVApproxEq
        (toArray (unHomUnfused (i . i)))
        (toArray (unHomUnfused i))

-- | Left unit law: @id ∘ f ≅ f@ on spin-½ ('HomUnfused').
composeMorObjLeftUnitOk :: Bool
composeMorObjLeftUnitOk =
  let i = id :: HomUnfused ('Irrep 1) ('Irrep 1)
      f =
        HomUnfused ((3 :+ 0) *^ unHomUnfused i)
          :: HomUnfused ('Irrep 1) ('Irrep 1)
   in toVApproxEq
        (toArray (unHomUnfused (i . f)))
        (toArray (unHomUnfused f))

-- | Right unit law: @f ∘ id ≅ f@ on spin-½ ('HomUnfused').
composeMorObjRightUnitOk :: Bool
composeMorObjRightUnitOk =
  let i = id :: HomUnfused ('Irrep 1) ('Irrep 1)
      f =
        HomUnfused ((3 :+ 0) *^ unHomUnfused i)
          :: HomUnfused ('Irrep 1) ('Irrep 1)
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
          :: HomUnfused ('Irrep 1) ('Irrep 1)
      gHom =
        HomUnfused (asTensor -+$=> gLeg)
          :: HomUnfused ('Irrep 1) ('Irrep 2)
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
  let i = id :: HomUnfused ('Irrep 1) ('Irrep 1)
   in toVApproxEq
        (toArray (unHomUnfused (i . i)))
        (toArray (unHomUnfused i))

-- | @bimap id id ≅ id@ on @½ ⊗ ½@ (true unfused Hom).
bimapHomUnfusedIdIdOk :: Bool
bimapHomUnfusedIdIdOk =
  let iHalf = id :: HomUnfused ('Irrep 1) ('Irrep 1)
      iTen =
        id
          :: HomUnfused
               ((('Irrep 1) :⊗: ('Irrep 1)))
               ((('Irrep 1) :⊗: ('Irrep 1)))
      bi =
        bimap iHalf iHalf
          :: HomUnfused
               ((('Irrep 1) :⊗: ('Irrep 1)))
               ((('Irrep 1) :⊗: ('Irrep 1)))
   in toVApproxEq (toArray (unHomUnfused bi)) (toArray (unHomUnfused iTen))
-- | @disassociate ∘ associate ≅ id@ as linear maps on @(½ ⊗ ½) ⊗ ½@
-- (Hom packing of linearmap α / α⁻¹; avoids Hom-compose cost on the smoke).
associateHomUnfusedRoundtripOk :: Bool
associateHomUnfusedRoundtripOk =
  let α =
        unHomUnfused
          ( associate
              :: HomUnfused
                   ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
                   )
                   ( (('Irrep 1) :⊗: ((('Irrep 1) :⊗: ('Irrep 1))))
                   )
          )
      αinv =
        unHomUnfused
          ( disassociate
              :: HomUnfused
                   ( (('Irrep 1) :⊗: ((('Irrep 1) :⊗: ('Irrep 1))))
                   )
                   ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
                   )
          )
      roundTrip =
        (fromTensor -+$=> αinv)
          . (fromTensor -+$=> α)
            :: ToVObj
                 ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
                 )
               +> ToVObj
                    ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
                    )
      iHom =
        unHomUnfused
          ( id
              :: HomUnfused
                   ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
                   )
                   ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
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
        scaleFTreeV
          @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
          u
          (idHomFTrees @('[ 'IrrepTree 1]))
      FCons v FNil = cup @('[ 'IrrepTree 1]) capped
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

-- | Irrep → singleton spine.
type SmokeObjSpineIrrep =
  AssertEqSpine (ObjSpineSU2 ('Irrep 1)) '[ '(1, 1)]

-- | @½ ⊗ ½@ FuseNorm → singlet ⊕ triplet multiplicities.
type SmokeObjSpineHalfHalf =
  AssertEqSpine
    (ObjSpineSU2 ((('Irrep 1) :⊗: ('Irrep 1))))
    '[ '(0, 1), '(2, 1)]

-- | Direct sum coalesces and sorts by @2j@.
type SmokeObjSpineSum =
  AssertEqSpine
    (ObjSpineSU2 ((('Irrep 2) :⊕: ('Irrep 0))))
    '[ '(0, 1), '(2, 1)]

-- | Duplicate irreps add multiplicities.
type SmokeObjSpineMult =
  AssertEqSpine
    (ObjSpineSU2 ((('Irrep 1) :⊕: ('Irrep 1))))
    '[ '(1, 2)]

-- | Fused Hom is 'FTreeV' of 'FuseFTrees' (genealogy-preserving).
type SmokeHomFused =
  AssertEqType
    (ToVFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
    (C 1, C 3)

-- | @½ ⊗ ½@ fusion trees: singlet and triplet channels (no coalesce).
type SmokeFuseTrees =
  AssertEqFTrees
    (FuseTrees ('IrrepTree 1) ('IrrepTree 1))
    '[ 'From 0 '( 'IrrepTree 1, 'IrrepTree 1)
     , 'From 2 '( 'IrrepTree 1, 'IrrepTree 1)
     ]

-- | 'ObjTrees' on an irrep is a singleton leaf.
type SmokeObjTreesIrrep =
  AssertEqFTrees (ObjTrees ('Irrep 1)) '[ 'IrrepTree 1]

-- | 'ObjTrees' of @½ ⊗ ½@ matches 'FuseTrees' / 'FuseFTrees' on leaves.
type SmokeObjTreesHalfHalf =
  AssertEqFTrees
    (ObjTrees ((('Irrep 1) :⊗: ('Irrep 1))))
    (FuseTrees ('IrrepTree 1) ('IrrepTree 1))

-- | 'ObjTrees' of a sum is flat 'Append' (no coalesce).
type SmokeObjTreesSum =
  AssertEqFTrees
    (ObjTrees ((('Irrep 2) :⊕: ('Irrep 0))))
    '[ 'IrrepTree 2, 'IrrepTree 0]

-- | 'Norm' then fuse: @(0 ⊕ 1) ⊗ ½@ equals the distributed sum of tensors.
type SmokeObjTreesDist =
  AssertEqFTrees
    ( ObjTrees
        ((((('Irrep 0) :⊕: ('Irrep 2))) :⊗: ('Irrep 1)))
    )
    ( ObjTrees
        ((((('Irrep 0) :⊗: ('Irrep 1))) :⊕: ((('Irrep 2) :⊗: ('Irrep 1)))))
    )

-- | Nested tensor keeps association (@ObjTrees@ = left-assoc 'FuseFTrees').
type SmokeObjTreesAssocL =
  AssertEqFTrees
    ( ObjTrees
        ((((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1)))
    )
    (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])

-- | SU(2) simples are self-dual.
type SmokeDualObjIrrep =
  AssertEqObj (DualObj SU2Th ('Irrep 1)) ('Irrep 1)

-- | Dual reverses tensor order (labels unchanged for SU(2)).
type SmokeDualObjTensor =
  AssertEqObj
    ( DualObj SU2Th
        ((('Irrep 1) :⊗: ('Irrep 2)))
    )
    ((('Irrep 2) :⊗: ('Irrep 1)))

-- | Dual distributes over sums.
type SmokeDualObjSum =
  AssertEqObj
    ( DualObj SU2Th
        ((('Irrep 0) :⊕: ('Irrep 2)))
    )
    ((('Irrep 0) :⊕: ('Irrep 2)))

-- | Root of a fusion tree is the channel label.
type SmokeRootNode =
  AssertEqNat
    (Root ('From 0 '( 'IrrepTree 1, 'IrrepTree 1)))
    0

-- | 'ToVTree' is the root irrep space only (@j=1 ⇒ C 2@; @j=2 ⇒ C 3@).
type SmokeToVTree =
  AssertEqType
    (ToVTree ('From 2 '( 'IrrepTree 1, 'IrrepTree 1)))
    (C 3)

-- | 'ToVFTrees' nests root spaces.
type SmokeToVFTrees =
  AssertEqType
    (ToVFTrees (FuseTrees ('IrrepTree 1) ('IrrepTree 1)))
    (C 1, C 3)

-- | List fuse distributes over tree pairs.
type SmokeFuseFTrees =
  AssertEqFTrees
    (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
    (FuseTrees ('IrrepTree 1) ('IrrepTree 1))

-- | Left-assoc @½⊗½⊗½@ expands to the concrete 'From' spine.
type SmokeAssocL111 =
  AssertEqFTrees
    ( FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1] )
    '[ 'From 1 '( 'From 0 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 1)
     , 'From 1 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 1)
     , 'From 3 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 1)
     ]

type SmokeAssocR111 =
  AssertEqFTrees
    ( FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) )
    '[ 'From 1 '( 'IrrepTree 1, 'From 0 '( 'IrrepTree 1, 'IrrepTree 1))
     , 'From 1 '( 'IrrepTree 1, 'From 2 '( 'IrrepTree 1, 'IrrepTree 1))
     , 'From 3 '( 'IrrepTree 1, 'From 2 '( 'IrrepTree 1, 'IrrepTree 1))
     ]

type SmokeAssocL110 =
  AssertEqFTrees
    ( FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 0] )
    '[ 'From 0 '( 'From 0 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 0)
     , 'From 2 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 0)
     ]

type SmokeAssocR110 =
  AssertEqFTrees
    ( FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 0]) )
    '[ 'From 0 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 1, 'IrrepTree 0))
     , 'From 2 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 1, 'IrrepTree 0))
     ]

type SmokeAssocL112 =
  AssertEqFTrees
    ( FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2] )
    '[ 'From 2 '( 'From 0 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 2)
     , 'From 0 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 2)
     , 'From 2 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 2)
     , 'From 4 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 2)
     ]

type SmokeAssocR112 =
  AssertEqFTrees
    ( FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 2]) )
    '[ 'From 0 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 1, 'IrrepTree 2))
     , 'From 2 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 1, 'IrrepTree 2))
     , 'From 2 '( 'IrrepTree 1, 'From 3 '( 'IrrepTree 1, 'IrrepTree 2))
     , 'From 4 '( 'IrrepTree 1, 'From 3 '( 'IrrepTree 1, 'IrrepTree 2))
     ]

-- | After @id ⊗ (cup ⊗ id)@: Unit remains as 'Unit' in the middle.
type SmokeAfterCup111 =
  AssertEqFTrees
    (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees Unit '[ 'IrrepTree 1]))
    '[ 'From 0 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 0, 'IrrepTree 1))
     , 'From 2 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 0, 'IrrepTree 1))
     ]

-- | Flat layout equals reduced HMatrix packing for @½⊗½⊗½@ (both associations).
smokeObjSpineIrrep :: Proxy SmokeObjSpineIrrep
smokeObjSpineIrrep = Proxy

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

smokeObjTreesIrrep :: Proxy SmokeObjTreesIrrep
smokeObjTreesIrrep = Proxy

smokeObjTreesHalfHalf :: Proxy SmokeObjTreesHalfHalf
smokeObjTreesHalfHalf = Proxy

smokeObjTreesSum :: Proxy SmokeObjTreesSum
smokeObjTreesSum = Proxy

smokeObjTreesDist :: Proxy SmokeObjTreesDist
smokeObjTreesDist = Proxy

smokeObjTreesAssocL :: Proxy SmokeObjTreesAssocL
smokeObjTreesAssocL = Proxy

smokeDualObjIrrep :: Proxy SmokeDualObjIrrep
smokeDualObjIrrep = Proxy

smokeDualObjTensor :: Proxy SmokeDualObjTensor
smokeDualObjTensor = Proxy

smokeDualObjSum :: Proxy SmokeDualObjSum
smokeDualObjSum = Proxy

smokeRootNode :: Proxy SmokeRootNode
smokeRootNode = Proxy

smokeToVTree :: Proxy SmokeToVTree
smokeToVTree = Proxy

smokeToVFTrees :: Proxy SmokeToVFTrees
smokeToVFTrees = Proxy

smokeFuseFTrees :: Proxy SmokeFuseFTrees
smokeFuseFTrees = Proxy

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
sampleAssocL111 :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])
sampleAssocL111 =
  makeFTrees @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])
    (konst 1, (konst 0.5, konst 0.25))

sampleAssocL110 :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 0])
sampleAssocL110 =
  makeFTrees @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 0])
    (konst 1, konst 0.5)

sampleAssocL112 :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
sampleAssocL112 =
  makeFTrees @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
    (konst 1, (konst 0.5, (konst 0.25, konst 0.125)))

-- | Tree F-move round-trips (@F⁻¹ ∘ F ≈ id@) on concrete triples + @½⊗1⊗½@.
fmoveTreesSelfTest :: Bool
fmoveTreesSelfTest =
  checkFmoveTrees111 sampleAssocL111
    && checkFmoveTrees110 sampleAssocL110
    && checkFmoveTrees112 sampleAssocL112
    && checkFmoveTreesLeaves @1 @2 @1
         (fillFTreeVScaled @( FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 2]) '[ 'IrrepTree 1] ))

-- | Force the F-move self-test at module load (fails loud if broken).
fmoveTreesSelfTestOk :: ()
fmoveTreesSelfTestOk =
  if fmoveTreesSelfTest
    then ()
    else error "fmoveTreesSelfTest failed: tree F round-trip"

-- | Pure Mid from 'TensorTrees': 'fuseMapRightFinv111' matches F-inv on the assoc factor.
fuseMapRightFinvSelfTest :: Bool
fuseMapRightFinvSelfTest =
  let leaf = FCons (konst 1) FNil
      assocR =
        makeFTrees @(FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
          (konst 0.5, (konst 0.25, konst 0.125))
      mid =
        fuseTensorTrees
          @('[ 'IrrepTree 1])
          @(FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
          (TensorTrees leaf assocR)
      cupGen = fuseMapRightFinv111 mid
      expected =
        fuseTensorTrees
          @('[ 'IrrepTree 1])
          @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])
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
        (fTreeVToV @(FuseFTrees '[ 'IrrepTree 1] (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])) cupGen)
        (fTreeVToV @(FuseFTrees '[ 'IrrepTree 1] (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])) expected)

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
  :: FTreeV (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
  -> FTreeV (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
  -> FTreeV (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
composeHomTreesI1 = composeHomTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1])

composeHomTreesI1TypedOk :: Bool
composeHomTreesI1TypedOk =
  let _ty = composeHomTreesI1
      _cup = cupTensorIdHomI1
   in True
