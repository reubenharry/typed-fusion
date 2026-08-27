{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Smokes for 'Experiments.Symbolic': term-level checks and compile-time type equalities.
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
  , repVApproxEq
  , sectorFlatDim
  )
import Math.LinearMap.Category (type (⊗), (⊗))
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

-- | Unfused @½ ⊗ ½@ product state @|↑↑⟩@ (@'AtomM 1@ layout).
sHalfHalfUpUp :: ToVSector ('Tensor ('Atom 1) ('Atom 1)) ('AtomM 1)
sHalfHalfUpUp =
  unsafeFromArray $
    VS.fromList [1, 0, 0, 0]

-- | Kronecker action on an unfused tensor sector: @R_z(π)⊗R_z(π)@ on @|↑↑⟩@.
-- Each factor picks @(-i)@, so overall phase @(-i)² = -1@.
actRepRzPiTensorOk :: Bool
actRepRzPiTensorOk =
  let r = RConsTensorAtomM sHalfHalfUpUp RNil
            :: RepV '[ '( 'Tensor ('Atom 1) ('Atom 1), 'AtomM 1)]
      RConsTensorAtomM v RNil = actRep exRzPi r
      expected = VS.fromList [-1, 0, 0, 0]
   in all (\(a, b) -> magnitude (a - b) < 1e-9)
        (zip (VS.toList (toArray v)) (VS.toList expected))

-- | CG intertwiner: @fuse ∘ act g ≅ act g ∘ fuse@ on @½ ⊗ ½@.
actRepFuseIntertwinesOk :: Bool
actRepFuseIntertwinesOk =
  let unfused =
        RConsTensorAtomM sHalfHalfUpUp RNil
          :: RepV '[ '( 'Tensor ('Atom 1) ('Atom 1), 'AtomM 1)]
      actThenFuse = fuse (actRep exRzPi unfused)
      fuseThenAct = actRep exRzPi (fuse unfused)
   in repVApproxEq actThenFuse fuseThenAct 1e-9

--------------------------------------------------------------------------------
-- Atom-spine tensor
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

-- | Single-sector 'tensor' matches 'tensorAtoms'.
tensorAtomsMatchesTensorOk :: Bool
tensorAtomsMatchesTensorOk =
  let RConsTensorProd vAtoms RNil = tensorAtoms sCoalesce1 sTensorRight
      RConsTensorProd vSpine RNil =
        tensor
          (RConsAtomAtomM sCoalesce1 RNil)
          (RConsAtomAtomM sTensorRight RNil)
   in toArray vAtoms == (toArray vSpine :: VS.Vector (Complex Double))

-- | Two left sectors × one right: Cartesian product, flat dims multiply.
tensorSpineDistributeOk :: Bool
tensorSpineDistributeOk =
  let left =
        RConsAtomAtomM sCoalesce1 (RConsAtomAtomM sUnitAtom RNil)
          :: RepV '[ '( 'Atom 1, 'AtomM 2), '( 'Atom 0, 'AtomM 1)]
      right = RConsAtomAtomM sTensorRight RNil
      RConsTensorProd v1 (RConsTensorProd v2 RNil) = tensor left right
   in VS.length (toArray v1) == 12  -- (2·2)·(1·3)
        && VS.length (toArray v2) == 3  -- (1·1)·(1·3)

-- | @lunitApply@: @Unit ⊗ q → q@ recovers flat length of @q@.
lunitApplyOk :: Bool
lunitApplyOk =
  let q = RConsAtomAtomM sTensorRight RNil
            :: RepV '[ '( 'Atom 2, 'AtomM 1)]
      uq = tensor (RConsAtomAtomM sUnitAtom RNil) q
      RConsAtomAtomM v RNil = lunitApply @_ @'[ '( 'Atom 2, 'AtomM 1)] uq
   in VS.length (toArray v) == VS.length (toArray sTensorRight)

--------------------------------------------------------------------------------
-- Dual + unfused cup (InnerSpace Riesz DualVector; no euclideanNorm coerce)
--------------------------------------------------------------------------------

unitAmp :: ToVSector ('Atom 0) ('AtomM 1) -> Double
unitAmp u = abs (realPart (VS.head (toArray u)))

-- | @cup(x ⊗ dual x) = ‖x‖²@ on spin-½.
dualAtomSpinHalfOk :: Bool
dualAtomSpinHalfOk =
  let v :: ToVSector ('Atom 1) ('AtomM 1)
      v = unsafeFromArray (VS.fromList [1, 0])
      r = RConsAtomAtomM v RNil
      RConsAtomAtomM u RNil = cupUnfused @1 @1 (tensorAtomDual r (dual r))
   in abs (unitAmp u - 1) < 1e-9

-- | @j = 0@: @cup(x ⊗ dual x) = |x|²@.
cupUnfusedTrivialOk :: Bool
cupUnfusedTrivialOk =
  let x :: ToVSector ('Atom 0) ('AtomM 1)
      x = unsafeFromArray (VS.fromList [3 :+ 4])
      r = RConsAtomAtomM x RNil
      RConsAtomAtomM u RNil =
        cupUnfused @0 @1 (tensorAtomDual r (dual r))
   in abs (unitAmp u - 25) < 1e-9

-- | Multiplicity @m = 2@, @j = 0@.
cupUnfusedMultOk :: Bool
cupUnfusedMultOk =
  let x :: ToVSector ('Atom 0) ('AtomM 2)
      x = unsafeFromArray (VS.fromList [1, 2])
      r = RConsAtomAtomM x RNil
      RConsAtomAtomM u RNil =
        cupUnfused @0 @2 (tensorAtomDual r (dual r))
   in abs (unitAmp u - 5) < 1e-9

-- | @|↑⟩ ⊗ dual(|↑⟩)@: pairing magnitude 1.
cupUnfusedSpinHalfProductOk :: Bool
cupUnfusedSpinHalfProductOk =
  let up :: ToVSector ('Atom 1) ('AtomM 1)
      up = unsafeFromArray (VS.fromList [1, 0])
      RConsAtomAtomM u RNil =
        cupUnfused @1 @1 $
          tensorAtomDual (RConsAtomAtomM up RNil) (dual (RConsAtomAtomM up RNil))
   in abs (unitAmp u - 1) < 1e-9

-- | 'undualAtomAtomM' ∘ 'dualAtomAtomM' ≈ @√(j+1) · CS@ (pivotal Fuse undual).
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

-- | Fused cup on @j = 0@: agrees with unfused (trivial irrep; CS = id, scale 1).
cupFusedTrivialOk :: Bool
cupFusedTrivialOk =
  let x :: ToVSector ('Atom 0) ('AtomM 1)
      x = unsafeFromArray (VS.fromList [3 :+ 4])
      r = RConsAtomAtomM x RNil :: RepV '[ '( 'Atom 0, 'AtomM 1)]
      td = tensorAtomDual r (dual r)
      RConsAtomAtomM uUnf RNil = cupUnfused @0 @1 td
      RConsAtomAtomM uFus RNil = cup @'[ '( 'Atom 0, 'AtomM 1)] (fuse td)
   in abs (unitAmp uFus - unitAmp uUnf) < 1e-9

-- | Fused cup on spin-½ agrees with unfused (CS + @√2@ in undual).
cupFusedSpinHalfCoherent :: Bool
cupFusedSpinHalfCoherent =
  let v :: ToVSector ('Atom 1) ('AtomM 1)
      v = unsafeFromArray (VS.fromList [1, 0])
      r = RConsAtomAtomM v RNil :: RepV '[ '( 'Atom 1, 'AtomM 1)]
      td = tensorAtomDual r (dual r)
      RConsAtomAtomM uUnf RNil = cupUnfused @1 @1 td
      RConsAtomAtomM uFus RNil = cup @'[ '( 'Atom 1, 'AtomM 1)] (fuse td)
   in abs (unitAmp uFus - unitAmp uUnf) < 1e-9

-- | @(cup ⊗ id)@ then 'lunitApply' recovers the cup-scale times @q@.
cupApplyLunitOk :: Bool
cupApplyLunitOk =
  let v :: ToVSector ('Atom 1) ('AtomM 1)
      v = unsafeFromArray (VS.fromList [1, 0])
      r = RConsAtomAtomM v RNil :: RepV '[ '( 'Atom 1, 'AtomM 1)]
      fused = fuse (tensorAtomDual r (dual r))
      RConsAtomProd h (RConsAtomProd t2 RNil) = fused
      assoc =
        RCons (h ⊗ v) (RCons (t2 ⊗ v) RNil)
          :: RepV
               ( ApplyAssoc
                   '[ '( 'Atom 1, 'AtomM 1)]
                   '[ '( 'Atom 1, 'AtomM 1)]
               )
      RConsAtomAtomM recovered RNil =
        lunitApply
          @'[ '( 'Atom 1, 'AtomM 1)]
          @'[ '( 'Atom 1, 'AtomM 1)]
          ( cupApply
              @'[ '( 'Atom 1, 'AtomM 1)]
              @'[ '( 'Atom 1, 'AtomM 1)]
              assoc
          )
      RConsAtomAtomM u RNil = cup @'[ '( 'Atom 1, 'AtomM 1)] fused
      scale = VS.head (toArray u)
      expected = scale *^ v
   in all (\(a, b) -> magnitude (a - b) < 1e-9)
        (zip (VS.toList (toArray recovered)) (VS.toList (toArray expected)))

-- | Two-sector spine: cup sums diagonal leaf cups (@‖x‖² + ‖y‖²@).
cupUnfusedRepTwoSectorOk :: Bool
cupUnfusedRepTwoSectorOk =
  let x :: ToVSector ('Atom 0) ('AtomM 1)
      x = unsafeFromArray (VS.fromList [3 :+ 4])
      y :: ToVSector ('Atom 1) ('AtomM 1)
      y = unsafeFromArray (VS.fromList [1, 0])
      r =
        RConsAtomAtomM x (RConsAtomAtomM y RNil)
          :: RepV '[ '( 'Atom 0, 'AtomM 1), '( 'Atom 1, 'AtomM 1)]
      RConsAtomAtomM u RNil =
        cupUnfusedRep @'[ '( 'Atom 0, 'AtomM 1), '( 'Atom 1, 'AtomM 1)]
          (tensorAtomDual r (dual r))
   in abs (unitAmp u - 26) < 1e-9

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
    , tensorAtomsMatchesTensorOk
    , tensorSpineDistributeOk
    , lunitApplyOk
    , dualAtomSpinHalfOk
    , cupUnfusedTrivialOk
    , cupUnfusedMultOk
    , cupUnfusedSpinHalfProductOk
    , undualDualRoundtripOk
    , cupFusedTrivialOk
    , cupFusedSpinHalfCoherent
    , cupApplyLunitOk
    , cupUnfusedRepTwoSectorOk
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

type SmokeSector =
  '( 'Tensor ('Atom 1) ('Atom 2)
   , 'Prod ('AtomM 3) ('AtomM 5)
   )

type SmokeRep = '[SmokeSector]

type SmokeBraidSector =
  AssertEqSector
    (BraidSector SmokeSector)
    '( 'Tensor ('Atom 2) ('Atom 1)
     , 'Prod ('AtomM 5) ('AtomM 3)
     )

type SmokeBraid =
  AssertEqRep
    (Braid SmokeRep)
    '[ '( 'Tensor ('Atom 2) ('Atom 1)
        , 'Prod ('AtomM 5) ('AtomM 3)
        )
     ]

-- | @Braid (Tensor r s)@ on a leaf × leaf distribute.
type SmokeBraidTensor =
  AssertEqRep
    ( Braid
        ( Tensor
            '[ '( 'Atom 1, 'AtomM 2)]
            '[ '( 'Atom 2, 'AtomM 3)]
        )
    )
    '[ '( 'Tensor ('Atom 2) ('Atom 1), 'Prod ('AtomM 3) ('AtomM 2))]

-- | Dual of an atom is the @'Dual@ / @'DualM@ constructors (not silent self-duality).
type SmokeDualAtom =
  AssertEqSector
    (DualSector '( 'Atom 1, 'AtomM 3))
    '( 'Dual ('Atom 1), 'DualM ('AtomM 3))

-- | @(j₁ ⊗ j₂)* ≅ Dual j₂ ⊗ Dual j₁@ with copy @'Prod@ reversed (distributed dual).
type SmokeDualTensor =
  AssertEqSector
    (DualSector '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 3) ('AtomM 5)))
    '( 'Tensor ('Dual ('Atom 2)) ('Dual ('Atom 1))
     , 'Prod ('DualM ('AtomM 5)) ('DualM ('AtomM 3))
     )

-- | Dual is involutive on a tensor sector (@Dual ∘ Dual = id@).
type SmokeDualInvolutive =
  AssertEqSector
    ( DualSector
        ( DualSector
            '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 3) ('AtomM 5))
        )
    )
    '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 3) ('AtomM 5))

-- | Dual of a leaf spine wraps each sector in @'Dual@ / @'DualM@.
type SmokeDualRep =
  AssertEqRep
    ( Dual
        '[ '( 'Atom 1, 'AtomM 2)
         , '( 'Atom 3, 'AtomM 1)
         ]
    )
    '[ '( 'Dual ('Atom 1), 'DualM ('AtomM 2))
     , '( 'Dual ('Atom 3), 'DualM ('AtomM 1))
     ]

-- | @Mor r q = Dual r ⊗ q@ on leaf atoms (unfused Dual×Atom distribute).
type SmokeMor =
  AssertEqRep
    ( Mor
        '[ '( 'Atom 1, 'AtomM 2)]
        '[ '( 'Atom 2, 'AtomM 3)]
    )
    '[ '( 'Tensor ('Dual ('Atom 1)) ('Atom 2)
        , 'Prod ('DualM ('AtomM 2)) ('AtomM 3)
        )
     ]

-- | Multi-sector left spine distributes over right (@Tensor@ Cartesian product).
type SmokeTensorSpine =
  AssertEqRep
    ( Tensor
        '[ '( 'Atom 1, 'AtomM 2), '( 'Atom 0, 'AtomM 1)]
        '[ '( 'Atom 2, 'AtomM 3)]
    )
    '[ '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 2) ('AtomM 3))
     , '( 'Tensor ('Atom 0) ('Atom 2), 'Prod ('AtomM 1) ('AtomM 3))
     ]

-- | Same @'Atom 1@ sectors coalesce by adding multiplicities.
type SmokeCoalesceAtoms =
  AssertEqRep
    (Coalesce
      '[ '( 'Atom 1, 'AtomM 2)
       , '( 'Atom 1, 'AtomM 3)
       ])
    '[ '( 'Atom 1, 'AtomM 5)]

-- | Same @'Tensor@ with @'Prod@ multiplicities → @'AtomM@ of summed dims.
type SmokeCoalesceTensors =
  AssertEqRep
    (Coalesce
      '[ '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 2) ('AtomM 3))
       , '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 1) ('AtomM 4))
       ])
    '[ '( 'Tensor ('Atom 1) ('Atom 2), 'AtomM 10)]

-- | Distinct keys stay sorted (@'Atom' < 'Tensor'@).
type SmokeCoalesceSort =
  AssertEqRep
    (Coalesce
      '[ '( 'Tensor ('Atom 0) ('Atom 1), 'AtomM 1)
       , '( 'Atom 2, 'AtomM 1)
       ])
    '[ '( 'Atom 2, 'AtomM 1)
     , '( 'Tensor ('Atom 0) ('Atom 1), 'AtomM 1)
     ]

-- | Leaf sector @('Atom 1, 'AtomM 3)@ → @C 3 ⊗ C 2@.
type SmokeSectorAtom =
  AssertEqType
    (ToVSector ('Atom 1) ('AtomM 3))
    (C 3 ⊗ C 2)

type SmokeSectorTensor =
  AssertEqType
    (ToVSector ('Tensor ('Atom 1) ('Atom 2)) ('Prod ('AtomM 2) ('AtomM 3)))
    ((C 2 ⊗ C 2) ⊗ (C 3 ⊗ C 3))

-- | @1 ⊗ 2@ (SU2) → @j = 1, 3@ channels.
type SmokeFuseIrrep =
  AssertEqRep
    (FuseIrrep ('Tensor ('Atom 1) ('Atom 2)))
    '[ '( 'Atom 1, 'AtomM 1)
     , '( 'Atom 3, 'AtomM 1)
     ]

-- | Sector fuse tags copy multiplicity onto each CG channel.
type SmokeFuseSector =
  AssertEqRep
    (FuseSector '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 2) ('AtomM 3)))
    '[ '( 'Atom 1, 'Prod ('AtomM 2) ('AtomM 3))
     , '( 'Atom 3, 'Prod ('AtomM 2) ('AtomM 3))
     ]

-- | Atom sector is unchanged (modulo unit mult tag).
type SmokeFuseRepAtom =
  AssertEqRep
    (Fuse '[ '( 'Atom 2, 'AtomM 5)])
    '[ '( 'Atom 2, 'AtomM 5)]

-- | @Tensor@ then @Fuse@ on two single-sector reps.
type SmokeFuseTensor =
  AssertEqRep
    ( Fuse
        ( Tensor
            '[ '( 'Atom 1, 'AtomM 2)]
            '[ '( 'Atom 2, 'AtomM 3)]
        )
    )
    '[ '( 'Atom 1, 'Prod ('AtomM 2) ('AtomM 3))
     , '( 'Atom 3, 'Prod ('AtomM 2) ('AtomM 3))
     ]

-- | @Fuse (Braid (Tensor …))@ swaps tensor legs and copy product.
type SmokeFuseBraidTensor =
  AssertEqRep
    ( Fuse
        ( Braid
            ( Tensor
                '[ '( 'Atom 1, 'AtomM 2)]
                '[ '( 'Atom 2, 'AtomM 3)]
            )
        )
    )
    '[ '( 'Atom 1, 'Prod ('AtomM 3) ('AtomM 2))
     , '( 'Atom 3, 'Prod ('AtomM 3) ('AtomM 2))
     ]

-- | 'RmoveTarget' on a leaf fused tensor matches @Fuse (Braid (Tensor …))@.
type SmokeRmoveTarget =
  AssertEqRep
    ( RmoveTarget
        1
        2
        ( Fuse
            ( Tensor
                '[ '( 'Atom 1, 'AtomM 2)]
                '[ '( 'Atom 2, 'AtomM 3)]
            )
        )
    )
    ( Fuse
        ( Braid
            ( Tensor
                '[ '( 'Atom 1, 'AtomM 2)]
                '[ '( 'Atom 2, 'AtomM 3)]
            )
        )
    )

-- | Swapped tensor legs yield the same fused atom spine (@SU(2)@ CG symmetry).
type SmokeFusedLeafSym =
  AssertEqRep
    ( Coalesce
        (TagMult ('AtomM 6) (FuseIrrep ('Tensor ('Atom 2) ('Atom 1))))
    )
    ( Coalesce
        (TagMult ('AtomM 6) (FuseIrrep ('Tensor ('Atom 1) ('Atom 2))))
    )

-- | Reference flat fuse layout for @1 ⊗ 2@, @m = 2@, @n = 3@.
type SmokeFusedLeaf12 =
  AssertEqRep
    (Coalesce (TagMult ('AtomM 6) (FuseIrrep ('Tensor ('Atom 1) ('Atom 2)))))
    '[ '( 'Atom 1, 'AtomM 6)
     , '( 'Atom 3, 'AtomM 6)
     ]

-- | 'FilterTrivial' keeps only @'Atom 0@ sectors.
type SmokeFilterTrivial =
  AssertEqRep
    ( FilterTrivial
        '[ '( 'Atom 1, 'AtomM 2)
         , '( 'Atom 0, 'AtomM 3)
         , '( 'Tensor ('Atom 1) ('Atom 1), 'Prod ('AtomM 1) ('AtomM 1))
         , '( 'Atom 0, 'Prod ('AtomM 2) ('AtomM 2))
         ]
    )
    '[ '( 'Atom 0, 'AtomM 3)
     , '( 'Atom 0, 'Prod ('AtomM 2) ('AtomM 2))
     ]

-- | 'RepV' spine type is stable under its own index.
type SmokeRepVSpine =
  AssertEqType
    (RepV '[ '( 'Atom 1, 'AtomM 2), '( 'Tensor ('Atom 0) ('Atom 1), 'AtomM 1)])
    (RepV '[ '( 'Atom 1, 'AtomM 2), '( 'Tensor ('Atom 0) ('Atom 1), 'AtomM 1)])

smokeBraidSector :: Proxy SmokeBraidSector
smokeBraidSector = Proxy

smokeBraid :: Proxy SmokeBraid
smokeBraid = Proxy

smokeBraidTensor :: Proxy SmokeBraidTensor
smokeBraidTensor = Proxy

smokeDualAtom :: Proxy SmokeDualAtom
smokeDualAtom = Proxy

smokeDualTensor :: Proxy SmokeDualTensor
smokeDualTensor = Proxy

smokeDualInvolutive :: Proxy SmokeDualInvolutive
smokeDualInvolutive = Proxy

smokeDualRep :: Proxy SmokeDualRep
smokeDualRep = Proxy

smokeMor :: Proxy SmokeMor
smokeMor = Proxy

smokeTensorSpine :: Proxy SmokeTensorSpine
smokeTensorSpine = Proxy

smokeCoalesceAtoms :: Proxy SmokeCoalesceAtoms
smokeCoalesceAtoms = Proxy

smokeCoalesceTensors :: Proxy SmokeCoalesceTensors
smokeCoalesceTensors = Proxy

smokeCoalesceSort :: Proxy SmokeCoalesceSort
smokeCoalesceSort = Proxy

smokeSectorAtom :: Proxy SmokeSectorAtom
smokeSectorAtom = Proxy

smokeSectorTensor :: Proxy SmokeSectorTensor
smokeSectorTensor = Proxy

smokeFuseIrrep :: Proxy SmokeFuseIrrep
smokeFuseIrrep = Proxy

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
