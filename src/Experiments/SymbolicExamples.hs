{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Smokes for 'Experiments.Symbolic': term-level checks and compile-time type equalities.
-- Covers 'ToVSpine' / 'rtensor' / 'cupRdual' / Dual-left 'HomUnfused';
-- tree fused Hom ('HomFused' / 'composeHomTrees').
-- Unit laws: 'composeHomTreesSelfTest'.
-- Fused cups: 'cupFused' / 'capFused' on singlet trees.
-- Phase-1 fusion trees: 'FuseTrees' / 'ToVTree' / 'Root'.
module Experiments.SymbolicExamples where

import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..), id)
import Data.Complex (Complex ((:+)), magnitude, realPart)
import Data.Kind (Type)
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (InnerSpace ((<.>)), (*^), (^-^))
import Experiments.Categorical.Associative (Associative (..))
import Experiments.Categorical.Bifunctor (Bifunctor (..))
import Experiments.Fusion.Obj as FObj
import Experiments.Symbolic
import Experiments.Symbolic.Reference
  ( exCoherenceRmove11
  , exCoherenceRmove12
  , repVApproxEq
  , sectorFlatDim
  )
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
import Symmetry.SU2
  ( SU2Element
  , su2FromQuaternion
  , su2Ident
  )
import TensorNetwork.Categorical ((⊗^))
import qualified Data.Vector.Storable as VS

import Prelude hiding (id, (.), ($))

-- | Hexagon coherence via Reference CG fuse (see 'Experiments.Symbolic.Reference').
coherenceRmoveLeafOk :: Bool
coherenceRmoveLeafOk = exCoherenceRmove12

coherenceRmoveLeaf11Ok :: Bool
coherenceRmoveLeaf11Ok = exCoherenceRmove11

--------------------------------------------------------------------------------
-- SU(2) action on irreps / tensors
--------------------------------------------------------------------------------

-- | Active rotation by @π@ about @z@: @α = -i@, @β = 0@.
exRzPi :: SU2Element
exRzPi = fromJust (su2FromQuaternion 0 0 0 1)

-- | Spin-½, @m = 1@: @|↑⟩@.
sSpinHalfUp :: ToVSector 1 ('AtomM 1)
sSpinHalfUp =
  unsafeFromArray $
    VS.fromList [1, 0]

-- | Identity acts as @id@ on a single irrep sector.
actRepIdentAtomOk :: Bool
actRepIdentAtomOk =
  let r = RConsAtomAtomM sSpinHalfUp RNil
            :: RepV '[ '(1, 'AtomM 1)]
      RConsAtomAtomM v RNil = actRep su2Ident r
   in toArray v == (toArray sSpinHalfUp :: VS.Vector (Complex Double))

-- | @R_z(π)@ on spin-½: @|↑⟩ ↦ (-i)|↑⟩@.
actRepRzPiSpinHalfOk :: Bool
actRepRzPiSpinHalfOk =
  let r = RConsAtomAtomM sSpinHalfUp RNil
            :: RepV '[ '(1, 'AtomM 1)]
      RConsAtomAtomM v RNil = actRep exRzPi r
      expected = VS.fromList [0 :+ (-1), 0]
   in all (\(a, b) -> magnitude (a - b) < 1e-9)
        (zip (VS.toList (toArray v)) (VS.toList expected))

-- | Kronecker action on unfused @½ ⊗ ½@ via 'rtensor'.
-- Each factor picks @(-i)@, so overall phase @(-i)² = -1@.
actRepRzPiTensorOk :: Bool
actRepRzPiTensorOk =
  let left = RConsAtomAtomM sSpinHalfUp RNil
                :: RepV '[ '(1, 'AtomM 1)]
      right = RConsAtomAtomM sSpinHalfUp RNil
      u = rtensor left right
      u' = rtensor (actRep exRzPi left) (actRep exRzPi right)
      expected = (-1) *^ u
   in all (\(a, b) -> magnitude (a - b) < 1e-9)
        (zip (VS.toList (toArray u')) (VS.toList (toArray expected)))
--------------------------------------------------------------------------------
-- Unfused tensor / fuse on atom spines
--------------------------------------------------------------------------------

-- | @j = 2@, @'AtomM 1@: one copy × @C 3@.
sTensorRight :: ToVSector 2 ('AtomM 1)
sTensorRight =
  unsafeFromArray $
    VS.fromList [1, 0, 0]

-- | @j = 0@, @'AtomM 1@: vacuum copy × @C 1@.
sUnitAtom :: ToVSector 0 ('AtomM 1)
sUnitAtom =
  unsafeFromArray $
    VS.fromList [1]

-- | 'rtensor' packages the full unfused product space (@(2·2)·(1·3)@ amplitudes).
rtensorFlatDimOk :: Bool
rtensorFlatDimOk =
  let left = RConsAtomAtomM sCoalesce1 RNil
                :: RepV '[ '(1, 'AtomM 2)]
      right = RConsAtomAtomM sTensorRight RNil
                :: RepV '[ '(2, 'AtomM 1)]
   in VS.length (toArray (rtensor left right)) == 12
--------------------------------------------------------------------------------
-- Dual + cup (InnerSpace Riesz DualVector; no euclideanNorm coerce)
--------------------------------------------------------------------------------

unitAmp :: ToVSector 0 ('AtomM 1) -> Double
unitAmp u = abs (realPart (VS.head (toArray u)))

-- | @cup(x ⊗ dual x) = ‖x‖²@ on spin-½ via 'cupRdual'.
dualAtomSpinHalfOk :: Bool
dualAtomSpinHalfOk =
  let v :: ToVSector 1 ('AtomM 1)
      v = unsafeFromArray (VS.fromList [1, 0])
      r = RConsAtomAtomM v RNil
      RConsAtomAtomM u RNil = cupRdual r
   in abs (unitAmp u - 1) < 1e-9

-- | @j = 0@: @cup(x ⊗ dual x) = |x|²@.
cupRdualTrivialOk :: Bool
cupRdualTrivialOk =
  let x :: ToVSector 0 ('AtomM 1)
      x = unsafeFromArray (VS.fromList [3 :+ 4])
      r = RConsAtomAtomM x RNil
      RConsAtomAtomM u RNil = cupRdual r
   in abs (unitAmp u - 25) < 1e-9

-- | Multiplicity @m = 2@, @j = 0@.
cupRdualMultOk :: Bool
cupRdualMultOk =
  let x :: ToVSector 0 ('AtomM 2)
      x = unsafeFromArray (VS.fromList [1, 2])
      r = RConsAtomAtomM x RNil
      RConsAtomAtomM u RNil = cupRdual r
   in abs (unitAmp u - 5) < 1e-9

-- | Two-sector spine: cup sums the sector pairings (@‖x‖² + ‖y‖²@).
cupRdualTwoSectorOk :: Bool
cupRdualTwoSectorOk =
  let x :: ToVSector 0 ('AtomM 1)
      x = unsafeFromArray (VS.fromList [3 :+ 4])
      y :: ToVSector 1 ('AtomM 1)
      y = unsafeFromArray (VS.fromList [1, 0])
      r =
        RConsAtomAtomM x (RConsAtomAtomM y RNil)
          :: RepV '[ '(0, 'AtomM 1), '(1, 'AtomM 1)]
      RConsAtomAtomM u RNil =
        cupRdual @'[ '(0, 'AtomM 1), '(1, 'AtomM 1)] r
   in abs (unitAmp u - 26) < 1e-9

-- | 'cupUnfused' on @x ⊗ dual x@ agrees with 'cupRdual'.
cupUnfusedMatchesCupRdualOk :: Bool
cupUnfusedMatchesCupRdualOk =
  let v :: ToVSector 1 ('AtomM 1)
      v = unsafeFromArray (VS.fromList [1, 0])
      r = RConsAtomAtomM v RNil :: RepV '[ '(1, 'AtomM 1)]
      RConsAtomAtomM u1 RNil = cupRdual r
      u2 =
        cupUnfused @'[ '(1, 'AtomM 1)] (repVToV r ⊗ rdual r)
   in abs (unitAmp u1 - unitAmp u2) < 1e-9

-- | Unfused snake: @cup ∘ cap = dim@ on @j = 0@ (@dim = 1@).
cupCapUnfusedSnakeTrivialOk :: Bool
cupCapUnfusedSnakeTrivialOk =
  let u =
        cupUnfused @'[ '(0, 'AtomM 1)]
          (capUnfused @'[ '(0, 'AtomM 1)] (unitToVFromScalar 1))
   in abs (unitAmp u - 1) < 1e-9

-- | Unfused snake on spin-½: @cup ∘ cap = 2@.
cupCapUnfusedSnakeSpinHalfOk :: Bool
cupCapUnfusedSnakeSpinHalfOk =
  let u =
        cupUnfused @'[ '(1, 'AtomM 1)]
          (capUnfused @'[ '(1, 'AtomM 1)] (unitToVFromScalar 1))
   in abs (unitAmp u - 2) < 1e-9

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

-- | 'undualAtomAtomM' ∘ 'dualAtomAtomM' ≈ @√(j+1) · CS@ (pivotal undual).
undualDualRoundtripOk :: Bool
undualDualRoundtripOk =
  let v :: ToVSector 1 ('AtomM 1)
      v = unsafeFromArray (VS.fromList [0.6, 0.8])
      -- CS on spin-½: |↑⟩↦|↓⟩, |↓⟩↦−|↑⟩; √2 scale.
      -- @CS (0.6, 0.8) = (−0.8, 0.6)@.
      expected =
        unsafeFromArray (VS.fromList [-(sqrt 2 * 0.8), sqrt 2 * 0.6])
          :: ToVSector 1 ('AtomM 1)
      v' = undualAtomAtomM @1 @1 (dualAtomAtomM @1 @1 v)
   in VS.and $
        VS.zipWith
          (\a b -> magnitude (a - b) < 1e-9)
          (toArray expected)
          (toArray v')

-- | 'repVToV' / 'vToRepV' round-trip on a two-sector atom spine.
repVToVRoundTripOk :: Bool
repVToVRoundTripOk =
  let s1 :: ToVSector 1 ('AtomM 2)
      s1 = unsafeFromArray (VS.fromList [1, 0, 0, 1])
      s0 :: ToVSector 0 ('AtomM 1)
      s0 = unsafeFromArray (VS.fromList [2 :+ 0])
      r =
        RConsAtomAtomM s1 (RConsAtomAtomM s0 RNil)
          :: RepV '[ '(1, 'AtomM 2), '(0, 'AtomM 1)]
   in repVApproxEq
        r
        ( vToRepV @'[ '(1, 'AtomM 2), '(0, 'AtomM 1)]
            (repVToV r)
        )
        1e-12

--------------------------------------------------------------------------------
-- Coalesce merge (direct-sum layout)
--------------------------------------------------------------------------------

-- | @j = 1@, @'AtomM 2@: two copy slots × @C 2@.
sCoalesce1 :: ToVSector 1 ('AtomM 2)
sCoalesce1 =
  unsafeFromArray $
    VS.fromList [1, 0, 0, 1]

-- | @j = 1@, @'AtomM 3@: three copy slots × @C 2@ (flat length @6@).
sCoalesce2 :: ToVSector 1 ('AtomM 3)
sCoalesce2 =
  unsafeFromArray $
    VS.fromList [2, 0, 0, 2, 3, 0]

exCoalesceMerge :: RepV '[ '(1, 'AtomM 5)]
exCoalesceMerge =
  coalesce @'[ '(1, 'AtomM 2), '(1, 'AtomM 3)] $
    RConsAtomAtomM sCoalesce1 (RConsAtomAtomM sCoalesce2 RNil)

-- | Merged sector flat length matches coalesced multiplicity × irrep dim.
coalesceMergeFlatDimOk :: Bool
coalesceMergeFlatDimOk =
  let RConsAtomAtomM v RNil = exCoalesceMerge
   in VS.length (toArray v)
        == sectorFlatDim (Proxy @'(1, 'AtomM 5))

-- | Merge stacks copy slots (via 'TensorNetwork.Categorical.mergeCopyAxis').
coalesceMergeDirectSumOk :: Bool
coalesceMergeDirectSumOk =
  let RConsAtomAtomM v RNil = exCoalesceMerge
   in toArray v
        == VS.fromList [1, 0, 0, 1, 2, 0, 0, 2, 3, 0]

-- | Total flat dim unchanged by 'coalesce' on this spine.
coalescePreservesFlatDimOk :: Bool
coalescePreservesFlatDimOk =
  let v1 = sCoalesce1
      v2 = sCoalesce2
      RConsAtomAtomM vMerged RNil =
        coalesce
          @'[ '(1, 'AtomM 2)
             , '(1, 'AtomM 3)
             ]
          (RConsAtomAtomM sCoalesce1 (RConsAtomAtomM sCoalesce2 RNil))
   in VS.length (toArray v1) + VS.length (toArray v2)
        == VS.length (toArray vMerged)

--------------------------------------------------------------------------------
-- Singlet projection
--------------------------------------------------------------------------------

-- | @j = 0@, @'AtomM 2@: two copy slots × @C 1@.
sTrivial :: ToVSector 0 ('AtomM 2)
sTrivial =
  unsafeFromArray $
    VS.fromList [4, 5]

-- | Keeps only @0@; drops @1@.
projectToSymmetricOk :: Bool
projectToSymmetricOk =
  let spine =
        RConsAtomAtomM sCoalesce1 (RConsAtomAtomM sTrivial RNil)
          :: RepV '[ '(1, 'AtomM 2), '(0, 'AtomM 2)]
      RConsAtomAtomM v RNil = projectToSymmetric spine
   in toArray v == VS.fromList [4, 5]

-- | 'cupFused' on identity Hom picks the singlet amplitude (@1@).
cupFusedIdSpinHalfOk :: Bool
cupFusedIdSpinHalfOk =
  magnitude (unitScalar (cupFused @Leaf1 idHom11) - 1) < 1e-9

-- | 'capFused' then 'cupTrivialTrees' recovers the unit scalar.
cupCapFusedRoundtripSpinHalfOk :: Bool
cupCapFusedRoundtripSpinHalfOk =
  let u = unitFromScalar (0.7 :+ 0)
   in magnitude (unitScalar (cupTrivialTrees (capFused @Leaf1 u)) - 0.7) < 1e-9

-- | All symbolic smokes in one place (for REPL / probes).
symbolicExamplesOk :: Bool
symbolicExamplesOk =
  and
    [ coherenceRmoveLeafOk
    , coherenceRmoveLeaf11Ok
    , actRepIdentAtomOk
    , actRepRzPiSpinHalfOk
    , actRepRzPiTensorOk
    , rtensorFlatDimOk
    , dualAtomSpinHalfOk
    , cupRdualTrivialOk
    , cupRdualMultOk
    , cupRdualTwoSectorOk
    , cupUnfusedMatchesCupRdualOk
    , cupCapUnfusedSnakeTrivialOk
    , cupCapUnfusedSnakeSpinHalfOk
    , unitRunitMorTrivialOk
    , cupTensorIdUnitorOk
    , composeMorObjIdIdTrivialOk
    , composeMorObjLeftUnitOk
    , composeMorObjRightUnitOk
    , composeMorObjMatchesMatMulOk
    , composeMorObjIdIdOk
    , bimapHomUnfusedIdIdOk
    , associateHomUnfusedRoundtripOk
    , undualDualRoundtripOk
    , repVToVRoundTripOk
    , coalesceMergeFlatDimOk
    , coalesceMergeDirectSumOk
    , coalescePreservesFlatDimOk
    , projectToSymmetricOk
    , cupFusedIdSpinHalfOk
    , cupCapFusedRoundtripSpinHalfOk
    , composeHomTreesSelfTest
    , composeHomTreesLeaf1TypedOk
    ]


--------------------------------------------------------------------------------
-- Compile-time smokes (type equalities)
--------------------------------------------------------------------------------

type family AssertEqNat (a :: Nat) (b :: Nat) :: Bool where
  AssertEqNat a a = 'True

type family AssertEqMult (a :: MultExpr) (b :: MultExpr) :: Bool where
  AssertEqMult a a = 'True

type family AssertEqSector (a :: Sector) (b :: Sector) :: Bool where
  AssertEqSector a a = 'True

type family AssertEqRep (a :: Rep) (b :: Rep) :: Bool where
  AssertEqRep a a = 'True

type family AssertEqType (a :: Type) (b :: Type) :: Bool where
  AssertEqType a a = 'True

type family AssertEqIrrep (a :: Irrep) (b :: Irrep) :: Bool where
  AssertEqIrrep a a = 'True

type family AssertEqTreeRep (a :: TreeRep) (b :: TreeRep) :: Bool where
  AssertEqTreeRep a a = 'True

type SmokeSector = '(1, 'Prod ('AtomM 3) ('AtomM 5))

type SmokeRep = '[SmokeSector]

-- | Braid swaps the copy factors and fixes the atom key.
type SmokeBraidSector =
  AssertEqSector
    (BraidSector SmokeSector)
    '(1, 'Prod ('AtomM 5) ('AtomM 3))

type SmokeBraid =
  AssertEqRep
    (Braid SmokeRep)
    '[ '(1, 'Prod ('AtomM 5) ('AtomM 3))]

-- | Dual-left Hom space: @Dual r ⊗ q@.
type SmokeMor =
  AssertEqType
    ( DualVector (ToVSpine '[ '(1, 'AtomM 2)])
        ⊗ ToVSpine '[ '(2, 'AtomM 3)]
    )
    ( DualVector (C 2 ⊗ C 2)
      ⊗ (C 3 ⊗ C 3)
    )

-- | Fused Hom is 'TreeV' of 'FuseTreeRep' (genealogy-preserving).
type SmokeHomFused =
  AssertEqType
    (ToVTreeRep (FuseTreeRep '[ 'Leaf 1] '[ 'Leaf 1]))
    (ToVTreeRep Hom11)

-- | Compose step-2 packing: @Dual a ⊗ ((b ⊗ Dual b) ⊗ c)@.
type SmokeComposeAssoc =
  AssertEqType
    ( DualVector (ToVSpine '[ '(0, 'AtomM 1)])
        ⊗ ( ( ToVSpine '[ '(1, 'AtomM 1)]
                ⊗ DualVector (ToVSpine '[ '(1, 'AtomM 1)])
            )
              ⊗ ToVSpine '[ '(0, 'AtomM 1)]
          )
    )
    ( DualVector (C 1 ⊗ C 1)
        ⊗ ( ((C 1 ⊗ C 2) ⊗ DualVector (C 1 ⊗ C 2))
              ⊗ (C 1 ⊗ C 1)
          )
    )

-- | Same @1@ sectors coalesce by adding multiplicities.
type SmokeCoalesceAtoms =
  AssertEqRep
    (Coalesce
      '[ '(1, 'AtomM 2)
       , '(1, 'AtomM 3)
       ])
    '[ '(1, 'AtomM 5)]

-- | @'Prod@ multiplicities on the same key collapse to @'AtomM@ of summed dims.
type SmokeCoalesceProds =
  AssertEqRep
    (Coalesce
      '[ '(1, 'Prod ('AtomM 2) ('AtomM 3))
       , '(1, 'Prod ('AtomM 1) ('AtomM 4))
       ])
    '[ '(1, 'AtomM 10)]

-- | Distinct keys stay sorted by irrep label.
type SmokeCoalesceSort =
  AssertEqRep
    (Coalesce
      '[ '(3, 'AtomM 1)
       , '(2, 'AtomM 1)
       ])
    '[ '(2, 'AtomM 1)
     , '(3, 'AtomM 1)
     ]

-- | Leaf sector @(1, 'AtomM 3)@ → @C 3 ⊗ C 2@.
type SmokeSectorAtom =
  AssertEqType
    (ToVSector 1 ('AtomM 3))
    (C 3 ⊗ C 2)

-- | @'Prod@ copy sector: @(C m ⊗ C n) ⊗ C (j+1)@.
type SmokeSectorProd =
  AssertEqType
    (ToVSector 1 ('Prod ('AtomM 2) ('AtomM 3)))
    ((C 2 ⊗ C 3) ⊗ C 2)

-- | Atom spine → right-nested sector tuples (no @()@ terminator).
type SmokeToVSpine =
  AssertEqType
    ( ToVSpine
        '[ '(1, 'AtomM 2)
         , '(0, 'AtomM 1)
         ]
    )
    ( C 2 ⊗ C 2
    , C 1 ⊗ C 1
    )

-- | Unfused atom-spine tensor: @ToVSpine r ⊗ ToVSpine q@.
type SmokeToVRtensor =
  AssertEqType
    (ToVSpine '[ '(1, 'AtomM 2)] ⊗ ToVSpine '[ '(2, 'AtomM 1)])
    ( (C 2 ⊗ C 2)
      ⊗ (C 1 ⊗ C 3)
    )

-- | @1 ⊗ 2@ (SU2) → @j = 1, 3@ channels.
type SmokeFuseAtoms =
  AssertEqRep
    (FuseAtoms 1 2 ('AtomM 1))
    '[ '(1, 'AtomM 1)
     , '(3, 'AtomM 1)
     ]

-- | 'FuseHom' on an unfused atom pair: CG channels tagged with the copy product.
type SmokeFuseTensor =
  AssertEqRep
    (FuseHom '[ '(1, 'AtomM 2)] '[ '(2, 'AtomM 3)])
    '[ '(1, 'Prod ('AtomM 2) ('AtomM 3))
     , '(3, 'Prod ('AtomM 2) ('AtomM 3))
     ]

-- | @FuseHom q r@ after braiding legs (swap copy factors on the product).
type SmokeFuseBraidTensor =
  AssertEqRep
    (FuseHom '[ '(2, 'AtomM 3)] '[ '(1, 'AtomM 2)])
    '[ '(1, 'Prod ('AtomM 3) ('AtomM 2))
     , '(3, 'Prod ('AtomM 3) ('AtomM 2))
     ]

-- | 'RmoveTarget' on fused 'FuseHom' matches braided 'FuseHom'.
type SmokeRmoveTarget =
  AssertEqRep
    (RmoveTarget 1 2 (FuseHom '[ '(1, 'AtomM 2)] '[ '(2, 'AtomM 3)]))
    (FuseHom '[ '(2, 'AtomM 3)] '[ '(1, 'AtomM 2)])

-- | Swapped tensor legs yield the same fused atom spine (@SU(2)@ CG symmetry).
type SmokeFusedLeafSym =
  AssertEqRep
    (Coalesce (FuseAtoms 2 1 ('AtomM 6)))
    (Coalesce (FuseAtoms 1 2 ('AtomM 6)))

-- | Reference flat fuse layout for @1 ⊗ 2@, @m = 2@, @n = 3@.
type SmokeFusedLeaf12 =
  AssertEqRep
    (Coalesce (FuseAtoms 1 2 ('AtomM 6)))
    '[ '(1, 'AtomM 6)
     , '(3, 'AtomM 6)
     ]

-- | 'FilterTrivial' keeps only @0@ sectors.
type SmokeFilterTrivial =
  AssertEqRep
    ( FilterTrivial
        '[ '(1, 'AtomM 2)
         , '(0, 'AtomM 3)
         , '(2, 'Prod ('AtomM 1) ('AtomM 1))
         , '(0, 'Prod ('AtomM 2) ('AtomM 2))
         ]
    )
    '[ '(0, 'AtomM 3)
     , '(0, 'Prod ('AtomM 2) ('AtomM 2))
     ]

-- | 'RepV' spine type is stable under its own index.
type SmokeRepVSpine =
  AssertEqType
    (RepV '[ '(1, 'AtomM 2), '(0, 'Prod ('AtomM 1) ('AtomM 1))])
    (RepV '[ '(1, 'AtomM 2), '(0, 'Prod ('AtomM 1) ('AtomM 1))])

-- | @½ ⊗ ½@ fusion trees: singlet and triplet channels (no coalesce).
type SmokeFuseTrees =
  AssertEqTreeRep
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

-- | 'ToVTreeRep' nests like 'ToVSpine'.
type SmokeToVTreeRep =
  AssertEqType
    (ToVTreeRep (FuseTrees ('Leaf 1) ('Leaf 1)))
    (C 1, C 3)

-- | List fuse distributes over tree pairs.
type SmokeFuseTreeRep =
  AssertEqTreeRep
    (FuseTreeRep '[ 'Leaf 1] '[ 'Leaf 1])
    (FuseTrees ('Leaf 1) ('Leaf 1))

-- | Left-assoc @½⊗½⊗½@: intermediate @0@ then @2@ channels.
type SmokeFuseAssocL =
  AssertEqTreeRep
    (FuseAssocL '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 1])
    '[ 'Node 1 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Leaf 1)
     , 'Node 1 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 1)
     , 'Node 3 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 1)
     ]

-- | Right-assoc @½⊗½⊗½@: same roots, different intermediate parenthesization.
type SmokeFuseAssocR =
  AssertEqTreeRep
    (FuseAssocR '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 1])
    '[ 'Node 1 ('Leaf 1) ('Node 0 ('Leaf 1) ('Leaf 1))
     , 'Node 1 ('Leaf 1) ('Node 2 ('Leaf 1) ('Leaf 1))
     , 'Node 3 ('Leaf 1) ('Node 2 ('Leaf 1) ('Leaf 1))
     ]

-- | Left and right associations forget to the same coalesced 'Rep'.
type SmokeForgetAssocLR =
  AssertEqRep
    (ForgetTreeRep (FuseAssocL '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 1]))
    (ForgetTreeRep (FuseAssocR '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 1]))

-- | Tree forget matches flat CG coalesce for the triple.
type SmokeForgetEqFuseFlat =
  AssertEqRep
    (ForgetTreeRep (FuseAssocL '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 1]))
    (FuseFlat (FuseFlat (Atom1 1) (Atom1 1)) (Atom1 1))

-- | 'FuseAssocL' equals the concrete 'AssocL111' spine used by 'fmoveTrees111'.
type SmokeAssocL111 =
  AssertEqTreeRep
    (FuseAssocL '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 1])
    AssocL111

type SmokeAssocR111 =
  AssertEqTreeRep
    (FuseAssocR '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 1])
    AssocR111

type SmokeAssocL110 =
  AssertEqTreeRep
    (FuseAssocL '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 0])
    AssocL110

type SmokeAssocR110 =
  AssertEqTreeRep
    (FuseAssocR '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 0])
    AssocR110

type SmokeAssocL112 =
  AssertEqTreeRep
    (FuseAssocL '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 2])
    AssocL112

type SmokeAssocR112 =
  AssertEqTreeRep
    (FuseAssocR '[ 'Leaf 1] '[ 'Leaf 1] '[ 'Leaf 2])
    AssocR112

-- | Concrete Leaf-½ Hom-compose spines match 'FuseTreeRep' expansions.
type SmokeHom11 =
  AssertEqTreeRep
    (FuseTreeRep '[ 'Leaf 1] '[ 'Leaf 1])
    Hom11

type SmokeDom111 =
  AssertEqTreeRep
    (FuseTreeRep Hom11 Hom11)
    Dom111

type SmokeMid111 =
  AssertEqTreeRep
    (FuseTreeRep '[ 'Leaf 1] AssocR111)
    Mid111

type SmokeCupR111 =
  AssertEqTreeRep
    (FuseTreeRep '[ 'Leaf 1] AssocL111)
    CupR111

-- | Nested outer-F codomain (Mac Lane step 2) equals 'Mid111'.
type SmokeAfterOuterF111 =
  AssertEqTreeRep
    ( FuseTreeRep
        '[ 'Leaf 1]
        (FuseTreeRep '[ 'Leaf 1] (FuseTreeRep '[ 'Leaf 1] '[ 'Leaf 1]))
    )
    Mid111

-- | Nested cup-ready spine (Mac Lane step 3) equals 'CupR111'.
type SmokeCupReady111 =
  AssertEqTreeRep
    ( FuseTreeRep
        '[ 'Leaf 1]
        (FuseTreeRep (FuseTreeRep '[ 'Leaf 1] '[ 'Leaf 1]) '[ 'Leaf 1])
    )
    CupR111

-- | After @id ⊗ (cup ⊗ id)@: Unit remains as 'TreeUnit' in the middle.
type SmokeAfterCup111 =
  AssertEqTreeRep
    (FuseTreeRep '[ 'Leaf 1] (FuseTreeRep TreeUnit '[ 'Leaf 1]))
    '[ 'Node 0 ('Leaf 1) ('Node 1 ('Leaf 0) ('Leaf 1))
     , 'Node 2 ('Leaf 1) ('Node 1 ('Leaf 0) ('Leaf 1))
     ]

type SmokeHom00 =
  AssertEqTreeRep
    (FuseTreeRep '[ 'Leaf 0] '[ 'Leaf 0])
    Hom00

type SmokeDom000 =
  AssertEqTreeRep
    (FuseTreeRep Hom00 Hom00)
    Dom000

type SmokeCupR000 =
  AssertEqTreeRep
    (FuseTreeRep '[ 'Leaf 0] (FuseTreeRep Hom00 '[ 'Leaf 0]))
    CupR000

-- | Flat layout equals reduced HMatrix packing for @½⊗½⊗½@ (both associations).
type Flat111 = (C 2 ⊗ C 2, C 1 ⊗ C 4)

type SmokeFlat111L =
  AssertEqType
    (ToVSpine (FuseFlat (FuseFlat (Atom1 1) (Atom1 1)) (Atom1 1)))
    Flat111

type SmokeFlat111R =
  AssertEqType
    (ToVSpine (FuseFlat (Atom1 1) (FuseFlat (Atom1 1) (Atom1 1))))
    Flat111

smokeBraidSector :: Proxy SmokeBraidSector
smokeBraidSector = Proxy

smokeBraid :: Proxy SmokeBraid
smokeBraid = Proxy

smokeMor :: Proxy SmokeMor
smokeMor = Proxy

smokeHomFused :: Proxy SmokeHomFused
smokeHomFused = Proxy

smokeComposeAssoc :: Proxy SmokeComposeAssoc
smokeComposeAssoc = Proxy

smokeCoalesceAtoms :: Proxy SmokeCoalesceAtoms
smokeCoalesceAtoms = Proxy

smokeCoalesceProds :: Proxy SmokeCoalesceProds
smokeCoalesceProds = Proxy

smokeCoalesceSort :: Proxy SmokeCoalesceSort
smokeCoalesceSort = Proxy

smokeSectorAtom :: Proxy SmokeSectorAtom
smokeSectorAtom = Proxy

smokeSectorProd :: Proxy SmokeSectorProd
smokeSectorProd = Proxy

smokeToVSpine :: Proxy SmokeToVSpine
smokeToVSpine = Proxy

smokeToVRtensor :: Proxy SmokeToVRtensor
smokeToVRtensor = Proxy

smokeFuseAtoms :: Proxy SmokeFuseAtoms
smokeFuseAtoms = Proxy

smokeFuseTensor :: Proxy SmokeFuseTensor
smokeFuseTensor = Proxy

smokeFuseBraidTensor :: Proxy SmokeFuseBraidTensor
smokeFuseBraidTensor = Proxy

smokeRmoveTarget :: Proxy SmokeRmoveTarget
smokeRmoveTarget = Proxy

smokeFusedLeafSym :: Proxy SmokeFusedLeafSym
smokeFusedLeafSym = Proxy

smokeFusedLeaf12 :: Proxy SmokeFusedLeaf12
smokeFusedLeaf12 = Proxy

smokeFilterTrivial :: Proxy SmokeFilterTrivial
smokeFilterTrivial = Proxy

smokeRepVSpine :: Proxy SmokeRepVSpine
smokeRepVSpine = Proxy

smokeFuseTrees :: Proxy SmokeFuseTrees
smokeFuseTrees = Proxy

smokeRootNode :: Proxy SmokeRootNode
smokeRootNode = Proxy

smokeToVTree :: Proxy SmokeToVTree
smokeToVTree = Proxy

smokeToVTreeRep :: Proxy SmokeToVTreeRep
smokeToVTreeRep = Proxy

smokeFuseTreeRep :: Proxy SmokeFuseTreeRep
smokeFuseTreeRep = Proxy

smokeFuseAssocL :: Proxy SmokeFuseAssocL
smokeFuseAssocL = Proxy

smokeFuseAssocR :: Proxy SmokeFuseAssocR
smokeFuseAssocR = Proxy

smokeForgetAssocLR :: Proxy SmokeForgetAssocLR
smokeForgetAssocLR = Proxy

smokeForgetEqFuseFlat :: Proxy SmokeForgetEqFuseFlat
smokeForgetEqFuseFlat = Proxy

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

smokeHom11 :: Proxy SmokeHom11
smokeHom11 = Proxy

smokeDom111 :: Proxy SmokeDom111
smokeDom111 = Proxy

smokeMid111 :: Proxy SmokeMid111
smokeMid111 = Proxy

smokeCupR111 :: Proxy SmokeCupR111
smokeCupR111 = Proxy

smokeAfterOuterF111 :: Proxy SmokeAfterOuterF111
smokeAfterOuterF111 = Proxy

smokeCupReady111 :: Proxy SmokeCupReady111
smokeCupReady111 = Proxy

smokeAfterCup111 :: Proxy SmokeAfterCup111
smokeAfterCup111 = Proxy

smokeHom00 :: Proxy SmokeHom00
smokeHom00 = Proxy

smokeDom000 :: Proxy SmokeDom000
smokeDom000 = Proxy

smokeCupR000 :: Proxy SmokeCupR000
smokeCupR000 = Proxy

smokeFlat111L :: Proxy SmokeFlat111L
smokeFlat111L = Proxy

smokeFlat111R :: Proxy SmokeFlat111R
smokeFlat111R = Proxy

-- | Sample left-assoc @½⊗½⊗½@ state for F-move self-tests.
sampleAssocL111 :: TreeV AssocL111
sampleAssocL111 =
  vToTreeV @AssocL111 (konst 1, (konst 0.5, konst 0.25))

sampleAssocL110 :: TreeV AssocL110
sampleAssocL110 =
  vToTreeV @AssocL110 (konst 1, konst 0.5)

sampleAssocL112 :: TreeV AssocL112
sampleAssocL112 =
  vToTreeV @AssocL112 (konst 1, (konst 0.5, (konst 0.25, konst 0.125)))

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
  let leaf = TCons (konst 1) TNil
      assocR = vToTreeV @AssocR111 (konst 0.5, (konst 0.25, konst 0.125))
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
   in approxHom16 (treeVToV @CupR111 cupGen) (treeVToV @CupR111 expected)

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
  :: TreeV Hom11 -> TreeV Hom11 -> TreeV Hom11
composeHomTreesLeaf1 = composeHomTrees @Leaf1 @Leaf1 @Leaf1

composeHomTreesLeaf1TypedOk :: Bool
composeHomTreesLeaf1TypedOk =
  let _ty = composeHomTreesLeaf1
      _cup = cupTensorIdHomLeaf1
   in True
