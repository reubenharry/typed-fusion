{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Smokes for 'Experiments.Symbolic': term-level checks and compile-time type equalities.
-- Covers 'RepExpr' / 'ToV' / 'fuseExpr' / 'rtensor' / 'cupRdual'.
module Experiments.SymbolicExamples where

import Data.Complex (Complex ((:+)), magnitude, realPart)
import Data.Kind (Type)
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (..))
import Data.VectorSpace ((*^))
import Experiments.Symbolic
import Experiments.Symbolic.Reference
  ( exCoherenceRmove11
  , exCoherenceRmove12
  , exFuseOneSectorProd12
  , fuseAtomPairCoalescedReference
  , repVApproxEq
  , repVFlat
  , repVFlatApproxEq
  , repVFlatProdToAtomM
  , sectorFlatDim
  )
import Math.LinearMap.Category (type (⊗), (⊗), DualVector)
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C)
import Symmetry.SU2
  ( SU2Element
  , su2FromQuaternion
  , su2Ident
  )
import qualified Data.Vector.Storable as VS

-- | Hexagon coherence via Reference CG fuse (see 'Experiments.Symbolic.Reference').
coherenceRmoveLeafOk :: Bool
coherenceRmoveLeafOk = exCoherenceRmove12

coherenceRmoveLeaf11Ok :: Bool
coherenceRmoveLeaf11Ok = exCoherenceRmove11

fuseOneSectorProdOk :: Bool
fuseOneSectorProdOk = exFuseOneSectorProd12

--------------------------------------------------------------------------------
-- SU(2) action on irreps / tensors
--------------------------------------------------------------------------------

-- | Active rotation by @π@ about @z@: @α = -i@, @β = 0@.
exRzPi :: SU2Element
exRzPi = fromJust (su2FromQuaternion 0 0 0 1)

-- | Spin-½, @m = 1@: @|↑⟩@.
sSpinHalfUp :: ToVSector ('Atom 1) ('AtomM 1)
sSpinHalfUp =
  unsafeFromArray $
    VS.fromList [1, 0]

-- | Identity acts as @id@ on a single irrep sector.
actRepIdentAtomOk :: Bool
actRepIdentAtomOk =
  let r = RConsAtomAtomM sSpinHalfUp RNil
            :: RepV '[ '( 'Atom 1, 'AtomM 1)]
      RConsAtomAtomM v RNil = actRep su2Ident r
   in toArray v == (toArray sSpinHalfUp :: VS.Vector (Complex Double))

-- | @R_z(π)@ on spin-½: @|↑⟩ ↦ (-i)|↑⟩@.
actRepRzPiSpinHalfOk :: Bool
actRepRzPiSpinHalfOk =
  let r = RConsAtomAtomM sSpinHalfUp RNil
            :: RepV '[ '( 'Atom 1, 'AtomM 1)]
      RConsAtomAtomM v RNil = actRep exRzPi r
      expected = VS.fromList [0 :+ (-1), 0]
   in all (\(a, b) -> magnitude (a - b) < 1e-9)
        (zip (VS.toList (toArray v)) (VS.toList expected))

-- | Kronecker action on unfused @½ ⊗ ½@ via 'rtensor'.
-- Each factor picks @(-i)@, so overall phase @(-i)² = -1@.
actRepRzPiTensorOk :: Bool
actRepRzPiTensorOk =
  let left = RConsAtomAtomM sSpinHalfUp RNil
                :: RepV '[ '( 'Atom 1, 'AtomM 1)]
      right = RConsAtomAtomM sSpinHalfUp RNil
      u = rtensor left right
      u' = rtensor (actRep exRzPi left) (actRep exRzPi right)
      expected = (-1) *^ u
   in all (\(a, b) -> magnitude (a - b) < 1e-9)
        (zip (VS.toList (toArray u')) (VS.toList (toArray expected)))

-- | CG intertwiner: @fuseExpr ∘ (act ⊗ act) ≅ act ∘ fuseExpr@ on @½ ⊗ ½@.
actRepFuseIntertwinesOk :: Bool
actRepFuseIntertwinesOk =
  let left = RConsAtomAtomM sSpinHalfUp RNil
                :: RepV '[ '( 'Atom 1, 'AtomM 1)]
      right = RConsAtomAtomM sSpinHalfUp RNil
      actThenFuse =
        fuseExpr (actRep exRzPi left) (actRep exRzPi right)
      fuseThenAct = actRep exRzPi (fuseExpr left right)
   in repVApproxEq actThenFuse fuseThenAct 1e-9

--------------------------------------------------------------------------------
-- Unfused tensor / fuse on atom spines
--------------------------------------------------------------------------------

-- | @j = 2@, @'AtomM 1@: one copy × @C 3@.
sTensorRight :: ToVSector ('Atom 2) ('AtomM 1)
sTensorRight =
  unsafeFromArray $
    VS.fromList [1, 0, 0]

-- | @j = 0@, @'AtomM 1@: vacuum copy × @C 1@.
sUnitAtom :: ToVSector ('Atom 0) ('AtomM 1)
sUnitAtom =
  unsafeFromArray $
    VS.fromList [1]

-- | 'rtensor' packages the full unfused product space (@(2·2)·(1·3)@ amplitudes).
rtensorFlatDimOk :: Bool
rtensorFlatDimOk =
  let left = RConsAtomAtomM sCoalesce1 RNil
                :: RepV '[ '( 'Atom 1, 'AtomM 2)]
      right = RConsAtomAtomM sTensorRight RNil
                :: RepV '[ '( 'Atom 2, 'AtomM 1)]
   in VS.length (toArray (rtensor left right)) == 12

-- | 'fuseExpr' on one atom pair agrees with the flat CG oracle.
fuseExprMatchesReferenceOk :: Bool
fuseExprMatchesReferenceOk =
  let left = RConsAtomAtomM sCoalesce1 RNil
                :: RepV '[ '( 'Atom 1, 'AtomM 2)]
      right = RConsAtomAtomM sTensorRight RNil
                :: RepV '[ '( 'Atom 2, 'AtomM 1)]
      pair = repVToV left ⊗ repVToV right :: AtomPairV 1 2 2 1
   in repVFlatApproxEq
        (repVFlatProdToAtomM (fuseExpr left right))
        (repVFlat (fuseAtomPairCoalescedReference @1 @2 @2 @1 pair))
        1e-10

--------------------------------------------------------------------------------
-- Dual + cup (InnerSpace Riesz DualVector; no euclideanNorm coerce)
--------------------------------------------------------------------------------

unitAmp :: ToVSector ('Atom 0) ('AtomM 1) -> Double
unitAmp u = abs (realPart (VS.head (toArray u)))

-- | @cup(x ⊗ dual x) = ‖x‖²@ on spin-½ via 'cupRdual'.
dualAtomSpinHalfOk :: Bool
dualAtomSpinHalfOk =
  let v :: ToVSector ('Atom 1) ('AtomM 1)
      v = unsafeFromArray (VS.fromList [1, 0])
      r = RConsAtomAtomM v RNil
      RConsAtomAtomM u RNil = cupRdual r
   in abs (unitAmp u - 1) < 1e-9

-- | @j = 0@: @cup(x ⊗ dual x) = |x|²@.
cupRdualTrivialOk :: Bool
cupRdualTrivialOk =
  let x :: ToVSector ('Atom 0) ('AtomM 1)
      x = unsafeFromArray (VS.fromList [3 :+ 4])
      r = RConsAtomAtomM x RNil
      RConsAtomAtomM u RNil = cupRdual r
   in abs (unitAmp u - 25) < 1e-9

-- | Multiplicity @m = 2@, @j = 0@.
cupRdualMultOk :: Bool
cupRdualMultOk =
  let x :: ToVSector ('Atom 0) ('AtomM 2)
      x = unsafeFromArray (VS.fromList [1, 2])
      r = RConsAtomAtomM x RNil
      RConsAtomAtomM u RNil = cupRdual r
   in abs (unitAmp u - 5) < 1e-9

-- | Two-sector spine: cup sums the sector pairings (@‖x‖² + ‖y‖²@).
cupRdualTwoSectorOk :: Bool
cupRdualTwoSectorOk =
  let x :: ToVSector ('Atom 0) ('AtomM 1)
      x = unsafeFromArray (VS.fromList [3 :+ 4])
      y :: ToVSector ('Atom 1) ('AtomM 1)
      y = unsafeFromArray (VS.fromList [1, 0])
      r =
        RConsAtomAtomM x (RConsAtomAtomM y RNil)
          :: RepV '[ '( 'Atom 0, 'AtomM 1), '( 'Atom 1, 'AtomM 1)]
      RConsAtomAtomM u RNil =
        cupRdual @'[ '( 'Atom 0, 'AtomM 1), '( 'Atom 1, 'AtomM 1)] r
   in abs (unitAmp u - 26) < 1e-9

-- | 'cupUnfused' on @x ⊗ dual x@ agrees with 'cupRdual'.
cupUnfusedMatchesCupRdualOk :: Bool
cupUnfusedMatchesCupRdualOk =
  let v :: ToVSector ('Atom 1) ('AtomM 1)
      v = unsafeFromArray (VS.fromList [1, 0])
      r = RConsAtomAtomM v RNil :: RepV '[ '( 'Atom 1, 'AtomM 1)]
      RConsAtomAtomM u1 RNil = cupRdual r
      RConsAtomAtomM u2 RNil =
        cupUnfused @'[ '( 'Atom 1, 'AtomM 1)] (repVToV r ⊗ rdual r)
   in abs (unitAmp u1 - unitAmp u2) < 1e-9

-- | Unfused snake: @cup ∘ cap = dim@ on @j = 0@ (@dim = 1@).
cupCapUnfusedSnakeTrivialOk :: Bool
cupCapUnfusedSnakeTrivialOk =
  let RConsAtomAtomM u RNil =
        cupUnfused @'[ '( 'Atom 0, 'AtomM 1)]
          (capUnfused @'[ '( 'Atom 0, 'AtomM 1)] (unitFromScalar 1))
   in abs (unitAmp u - 1) < 1e-9

-- | Unfused snake on spin-½: @cup ∘ cap = 2@.
cupCapUnfusedSnakeSpinHalfOk :: Bool
cupCapUnfusedSnakeSpinHalfOk =
  let RConsAtomAtomM u RNil =
        cupUnfused @'[ '( 'Atom 1, 'AtomM 1)]
          (capUnfused @'[ '( 'Atom 1, 'AtomM 1)] (unitFromScalar 1))
   in abs (unitAmp u - 2) < 1e-9

-- | Fused cup agrees with unfused on @j = 0@ (CS = id, scale 1).
cupFusedTrivialOk :: Bool
cupFusedTrivialOk =
  let x :: ToVSector ('Atom 0) ('AtomM 1)
      x = unsafeFromArray (VS.fromList [3 :+ 4])
      r = RConsAtomAtomM x RNil :: RepV '[ '( 'Atom 0, 'AtomM 1)]
      RConsAtomAtomM uUnf RNil =
        cupUnfused @'[ '( 'Atom 0, 'AtomM 1)] (repVToV r ⊗ rdual r)
      RConsAtomAtomM uFus RNil =
        cupFused @'[ '( 'Atom 0, 'AtomM 1)]
          ( projectToSymmetric
              ( fuseExpr @'[ '( 'Atom 0, 'AtomM 1)] @'[ '( 'Atom 0, 'AtomM 1)]
                  r
                  (vToRepV @'[ '( 'Atom 0, 'AtomM 1)] (undualSpine @'[ '( 'Atom 0, 'AtomM 1)] (rdual r)))
              )
          )
   in abs (unitAmp uFus - unitAmp uUnf) < 1e-9

-- | Fused cup on spin-½ agrees with unfused (CS + @√2@ in undual).
cupFusedSpinHalfCoherentOk :: Bool
cupFusedSpinHalfCoherentOk =
  let v :: ToVSector ('Atom 1) ('AtomM 1)
      v = unsafeFromArray (VS.fromList [1, 0])
      r = RConsAtomAtomM v RNil :: RepV '[ '( 'Atom 1, 'AtomM 1)]
      RConsAtomAtomM uUnf RNil =
        cupUnfused @'[ '( 'Atom 1, 'AtomM 1)] (repVToV r ⊗ rdual r)
      RConsAtomAtomM uFus RNil =
        cupFused @'[ '( 'Atom 1, 'AtomM 1)]
          ( projectToSymmetric
              ( fuseExpr @'[ '( 'Atom 1, 'AtomM 1)] @'[ '( 'Atom 1, 'AtomM 1)]
                  r
                  (vToRepV @'[ '( 'Atom 1, 'AtomM 1)] (undualSpine @'[ '( 'Atom 1, 'AtomM 1)] (rdual r)))
              )
          )
   in abs (unitAmp uFus - unitAmp uUnf) < 1e-9

-- | Fused snake @cupFused ∘ capFused@ on @j = 0@.
cupCapFusedSnakeTrivialOk :: Bool
cupCapFusedSnakeTrivialOk =
  let RConsAtomAtomM u RNil =
        cupFused @'[ '( 'Atom 0, 'AtomM 1)]
          (capFused @'[ '( 'Atom 0, 'AtomM 1)] (unitFromScalar 1))
   in abs (unitAmp u - 1) < 1e-9

-- | 'undualAtomAtomM' ∘ 'dualAtomAtomM' ≈ @√(j+1) · CS@ (pivotal undual).
undualDualRoundtripOk :: Bool
undualDualRoundtripOk =
  let v :: ToVSector ('Atom 1) ('AtomM 1)
      v = unsafeFromArray (VS.fromList [0.6, 0.8])
      -- CS on spin-½: |↑⟩↦|↓⟩, |↓⟩↦−|↑⟩; √2 scale.
      -- @CS (0.6, 0.8) = (−0.8, 0.6)@.
      expected =
        unsafeFromArray (VS.fromList [-(sqrt 2 * 0.8), sqrt 2 * 0.6])
          :: ToVSector ('Atom 1) ('AtomM 1)
      v' = undualAtomAtomM @1 @1 (dualAtomAtomM @1 @1 v)
   in VS.and $
        VS.zipWith
          (\a b -> magnitude (a - b) < 1e-9)
          (toArray expected)
          (toArray v')

-- | 'repVToV' / 'vToRepV' round-trip on a two-sector atom spine.
repVToVRoundTripOk :: Bool
repVToVRoundTripOk =
  let s1 :: ToVSector ('Atom 1) ('AtomM 2)
      s1 = unsafeFromArray (VS.fromList [1, 0, 0, 1])
      s0 :: ToVSector ('Atom 0) ('AtomM 1)
      s0 = unsafeFromArray (VS.fromList [2 :+ 0])
      r =
        RConsAtomAtomM s1 (RConsAtomAtomM s0 RNil)
          :: RepV '[ '( 'Atom 1, 'AtomM 2), '( 'Atom 0, 'AtomM 1)]
   in repVApproxEq
        r
        ( vToRepV @'[ '( 'Atom 1, 'AtomM 2), '( 'Atom 0, 'AtomM 1)]
            (repVToV r)
        )
        1e-12

--------------------------------------------------------------------------------
-- Coalesce merge (direct-sum layout)
--------------------------------------------------------------------------------

-- | @j = 1@, @'AtomM 2@: two copy slots × @C 2@.
sCoalesce1 :: ToVSector ('Atom 1) ('AtomM 2)
sCoalesce1 =
  unsafeFromArray $
    VS.fromList [1, 0, 0, 1]

-- | @j = 1@, @'AtomM 3@: three copy slots × @C 2@ (flat length @6@).
sCoalesce2 :: ToVSector ('Atom 1) ('AtomM 3)
sCoalesce2 =
  unsafeFromArray $
    VS.fromList [2, 0, 0, 2, 3, 0]

exCoalesceMerge :: RepV '[ '( 'Atom 1, 'AtomM 5)]
exCoalesceMerge =
  coalesce @'[ '( 'Atom 1, 'AtomM 2), '( 'Atom 1, 'AtomM 3)] $
    RConsAtomAtomM sCoalesce1 (RConsAtomAtomM sCoalesce2 RNil)

-- | Merged sector flat length matches coalesced multiplicity × irrep dim.
coalesceMergeFlatDimOk :: Bool
coalesceMergeFlatDimOk =
  let RConsAtomAtomM v RNil = exCoalesceMerge
   in VS.length (toArray v)
        == sectorFlatDim (Proxy @'( 'Atom 1, 'AtomM 5))

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
          @'[ '( 'Atom 1, 'AtomM 2)
             , '( 'Atom 1, 'AtomM 3)
             ]
          (RConsAtomAtomM sCoalesce1 (RConsAtomAtomM sCoalesce2 RNil))
   in VS.length (toArray v1) + VS.length (toArray v2)
        == VS.length (toArray vMerged)

--------------------------------------------------------------------------------
-- Singlet projection
--------------------------------------------------------------------------------

-- | @j = 0@, @'AtomM 2@: two copy slots × @C 1@.
sTrivial :: ToVSector ('Atom 0) ('AtomM 2)
sTrivial =
  unsafeFromArray $
    VS.fromList [4, 5]

-- | Keeps only @'Atom 0@; drops @'Atom 1@.
projectToSymmetricOk :: Bool
projectToSymmetricOk =
  let spine =
        RConsAtomAtomM sCoalesce1 (RConsAtomAtomM sTrivial RNil)
          :: RepV '[ '( 'Atom 1, 'AtomM 2), '( 'Atom 0, 'AtomM 2)]
      RConsAtomAtomM v RNil = projectToSymmetric spine
   in toArray v == VS.fromList [4, 5]

-- | All symbolic smokes in one place (for REPL / probes).
symbolicExamplesOk :: Bool
symbolicExamplesOk =
  and
    [ coherenceRmoveLeafOk
    , coherenceRmoveLeaf11Ok
    , fuseOneSectorProdOk
    , actRepIdentAtomOk
    , actRepRzPiSpinHalfOk
    , actRepRzPiTensorOk
    , actRepFuseIntertwinesOk
    , rtensorFlatDimOk
    , fuseExprMatchesReferenceOk
    , dualAtomSpinHalfOk
    , cupRdualTrivialOk
    , cupRdualMultOk
    , cupRdualTwoSectorOk
    , cupUnfusedMatchesCupRdualOk
    , cupCapUnfusedSnakeTrivialOk
    , cupCapUnfusedSnakeSpinHalfOk
    , cupFusedTrivialOk
    , cupFusedSpinHalfCoherentOk
    , cupCapFusedSnakeTrivialOk
    , undualDualRoundtripOk
    , repVToVRoundTripOk
    , coalesceMergeFlatDimOk
    , coalesceMergeDirectSumOk
    , coalescePreservesFlatDimOk
    , projectToSymmetricOk
    ]


--------------------------------------------------------------------------------
-- Compile-time smokes (type equalities)
--------------------------------------------------------------------------------

type family AssertEqIrrep (a :: IrrepExpr) (b :: IrrepExpr) :: Bool where
  AssertEqIrrep a a = 'True

type family AssertEqMult (a :: MultExpr) (b :: MultExpr) :: Bool where
  AssertEqMult a a = 'True

type family AssertEqSector (a :: Sector) (b :: Sector) :: Bool where
  AssertEqSector a a = 'True

type family AssertEqRep (a :: Rep) (b :: Rep) :: Bool where
  AssertEqRep a a = 'True

type family AssertEqType (a :: Type) (b :: Type) :: Bool where
  AssertEqType a a = 'True

type SmokeSector = '( 'Atom 1, 'Prod ('AtomM 3) ('AtomM 5))

type SmokeRep = '[SmokeSector]

-- | Braid swaps the copy factors and fixes the atom key.
type SmokeBraidSector =
  AssertEqSector
    (BraidSector SmokeSector)
    '( 'Atom 1, 'Prod ('AtomM 5) ('AtomM 3))

type SmokeBraid =
  AssertEqRep
    (Braid SmokeRep)
    '[ '( 'Atom 1, 'Prod ('AtomM 5) ('AtomM 3))]

-- | @MorExpr@: unfused dual⊗codomain space.
type SmokeMor =
  AssertEqType
    ( ToV
        ( MorExpr
            '[ '( 'Atom 1, 'AtomM 2)]
            '[ '( 'Atom 2, 'AtomM 3)]
        )
    )
    ( DualVector (C 2 ⊗ C 2)
      ⊗ (C 3 ⊗ C 3)
    )

-- | Same @'Atom 1@ sectors coalesce by adding multiplicities.
type SmokeCoalesceAtoms =
  AssertEqRep
    (Coalesce
      '[ '( 'Atom 1, 'AtomM 2)
       , '( 'Atom 1, 'AtomM 3)
       ])
    '[ '( 'Atom 1, 'AtomM 5)]

-- | @'Prod@ multiplicities on the same key collapse to @'AtomM@ of summed dims.
type SmokeCoalesceProds =
  AssertEqRep
    (Coalesce
      '[ '( 'Atom 1, 'Prod ('AtomM 2) ('AtomM 3))
       , '( 'Atom 1, 'Prod ('AtomM 1) ('AtomM 4))
       ])
    '[ '( 'Atom 1, 'AtomM 10)]

-- | Distinct keys stay sorted by irrep label.
type SmokeCoalesceSort =
  AssertEqRep
    (Coalesce
      '[ '( 'Atom 3, 'AtomM 1)
       , '( 'Atom 2, 'AtomM 1)
       ])
    '[ '( 'Atom 2, 'AtomM 1)
     , '( 'Atom 3, 'AtomM 1)
     ]

-- | Leaf sector @('Atom 1, 'AtomM 3)@ → @C 3 ⊗ C 2@.
type SmokeSectorAtom =
  AssertEqType
    (ToVSector ('Atom 1) ('AtomM 3))
    (C 3 ⊗ C 2)

-- | @'Prod@ copy sector: @(C m ⊗ C n) ⊗ C (j+1)@.
type SmokeSectorProd =
  AssertEqType
    (ToVSector ('Atom 1) ('Prod ('AtomM 2) ('AtomM 3)))
    ((C 2 ⊗ C 3) ⊗ C 2)

-- | Atom spine → right-nested sector tuples (no @()@ terminator).
type SmokeToVSpine =
  AssertEqType
    ( ToVSpine
        '[ '( 'Atom 1, 'AtomM 2)
         , '( 'Atom 0, 'AtomM 1)
         ]
    )
    ( C 2 ⊗ C 2
    , C 1 ⊗ C 1
    )

-- | Unfused atom sums: @ToV (RTensor (RSum r) (RSum q)) = ToVSpine r ⊗ ToVSpine q@.
type SmokeToVRtensor =
  AssertEqType
    ( ToV
        ( 'RTensor
            ('RSum '[ '( 'Atom 1, 'AtomM 2)])
            ('RSum '[ '( 'Atom 2, 'AtomM 1)])
        )
    )
    ( (C 2 ⊗ C 2)
      ⊗ (C 1 ⊗ C 3)
    )

-- | @1 ⊗ 2@ (SU2) → @j = 1, 3@ channels.
type SmokeFuseAtoms =
  AssertEqRep
    (FuseAtoms 1 2 ('AtomM 1))
    '[ '( 'Atom 1, 'AtomM 1)
     , '( 'Atom 3, 'AtomM 1)
     ]

-- | Fusing an atom sector is the identity (modulo the tagged multiplicity).
type SmokeFuseSector =
  AssertEqRep
    (FuseSector '( 'Atom 2, 'AtomM 5))
    '[ '( 'Atom 2, 'AtomM 5)]

-- | Atom sector is unchanged by a whole-spine 'Fuse'.
type SmokeFuseRepAtom =
  AssertEqRep
    (Fuse '[ '( 'Atom 2, 'AtomM 5)])
    '[ '( 'Atom 2, 'AtomM 5)]

-- | 'FuseExpr' on an unfused atom pair: CG channels tagged with the copy product.
type SmokeFuseTensor =
  AssertEqRep
    ( FuseExpr
        ( 'RTensor
            ('RSum '[ '( 'Atom 1, 'AtomM 2)])
            ('RSum '[ '( 'Atom 2, 'AtomM 3)])
        )
    )
    '[ '( 'Atom 1, 'Prod ('AtomM 2) ('AtomM 3))
     , '( 'Atom 3, 'Prod ('AtomM 2) ('AtomM 3))
     ]

-- | @FuseExpr (BraidExpr (RTensor …))@ swaps tensor legs.
type SmokeFuseBraidTensor =
  AssertEqRep
    ( FuseExpr
        ( BraidExpr
            ( 'RTensor
                ('RSum '[ '( 'Atom 1, 'AtomM 2)])
                ('RSum '[ '( 'Atom 2, 'AtomM 3)])
            )
        )
    )
    '[ '( 'Atom 1, 'Prod ('AtomM 3) ('AtomM 2))
     , '( 'Atom 3, 'Prod ('AtomM 3) ('AtomM 2))
     ]

-- | 'RmoveTarget' on fused 'FuseExpr' matches braided 'FuseExpr'.
type SmokeRmoveTarget =
  AssertEqRep
    ( RmoveTarget
        1
        2
        ( FuseExpr
            ( 'RTensor
                ('RSum '[ '( 'Atom 1, 'AtomM 2)])
                ('RSum '[ '( 'Atom 2, 'AtomM 3)])
            )
        )
    )
    ( FuseExpr
        ( BraidExpr
            ( 'RTensor
                ('RSum '[ '( 'Atom 1, 'AtomM 2)])
                ('RSum '[ '( 'Atom 2, 'AtomM 3)])
            )
        )
    )

-- | Swapped tensor legs yield the same fused atom spine (@SU(2)@ CG symmetry).
type SmokeFusedLeafSym =
  AssertEqRep
    (Coalesce (FuseAtoms 2 1 ('AtomM 6)))
    (Coalesce (FuseAtoms 1 2 ('AtomM 6)))

-- | Reference flat fuse layout for @1 ⊗ 2@, @m = 2@, @n = 3@.
type SmokeFusedLeaf12 =
  AssertEqRep
    (Coalesce (FuseAtoms 1 2 ('AtomM 6)))
    '[ '( 'Atom 1, 'AtomM 6)
     , '( 'Atom 3, 'AtomM 6)
     ]

-- | 'FilterTrivial' keeps only @'Atom 0@ sectors.
type SmokeFilterTrivial =
  AssertEqRep
    ( FilterTrivial
        '[ '( 'Atom 1, 'AtomM 2)
         , '( 'Atom 0, 'AtomM 3)
         , '( 'Atom 2, 'Prod ('AtomM 1) ('AtomM 1))
         , '( 'Atom 0, 'Prod ('AtomM 2) ('AtomM 2))
         ]
    )
    '[ '( 'Atom 0, 'AtomM 3)
     , '( 'Atom 0, 'Prod ('AtomM 2) ('AtomM 2))
     ]

-- | 'RepV' spine type is stable under its own index.
type SmokeRepVSpine =
  AssertEqType
    (RepV '[ '( 'Atom 1, 'AtomM 2), '( 'Atom 0, 'Prod ('AtomM 1) ('AtomM 1))])
    (RepV '[ '( 'Atom 1, 'AtomM 2), '( 'Atom 0, 'Prod ('AtomM 1) ('AtomM 1))])

smokeBraidSector :: Proxy SmokeBraidSector
smokeBraidSector = Proxy

smokeBraid :: Proxy SmokeBraid
smokeBraid = Proxy

smokeMor :: Proxy SmokeMor
smokeMor = Proxy

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

smokeFuseSector :: Proxy SmokeFuseSector
smokeFuseSector = Proxy

smokeFuseRepAtom :: Proxy SmokeFuseRepAtom
smokeFuseRepAtom = Proxy

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
