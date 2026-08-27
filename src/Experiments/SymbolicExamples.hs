{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

-- | Term-level smokes for 'Experiments.Symbolic' (merge layout, fuse pipeline).
module Experiments.SymbolicExamples where

import Data.Complex (Complex ((:+)), magnitude, realPart)
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (..))
import Experiments.Symbolic
import Experiments.Symbolic.Reference
  ( exCoherenceRmove11
  , exCoherenceRmove12
  , exFuseOneSectorProd12
  , repVApproxEq
  , sectorFlatDim
  )
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
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

-- | 'undualAtomAtomM' ∘ 'dualAtomAtomM' ≈ id on spin-½.
undualDualRoundtripOk :: Bool
undualDualRoundtripOk =
  let v :: ToVSector ('Atom 1) ('AtomM 1)
      v = unsafeFromArray (VS.fromList [0.6, 0.8])
      v' = undualAtomAtomM @1 @1 (dualAtomAtomM @1 @1 v)
   in VS.and $
        VS.zipWith
          (\a b -> magnitude (a - b) < 1e-9)
          (toArray v)
          (toArray v')

-- | Fused cup on @j = 0@: agrees with unfused (trivial irrep; no CS needed).
cupFusedTrivialOk :: Bool
cupFusedTrivialOk =
  let x :: ToVSector ('Atom 0) ('AtomM 1)
      x = unsafeFromArray (VS.fromList [3 :+ 4])
      r = RConsAtomAtomM x RNil :: RepV '[ '( 'Atom 0, 'AtomM 1)]
      td = tensorAtomDual r (dual r)
      RConsAtomAtomM uUnf RNil = cupUnfused @0 @1 td
      RConsAtomAtomM uFus RNil = cup @'[ '( 'Atom 0, 'AtomM 1)] (fuse td)
   in abs (unitAmp uFus - unitAmp uUnf) < 1e-9

-- | Probe: fused vs unfused cup on spin-½. Currently @False@ — CG singlet after
-- Riesz undual ≠ DualVector Hilbert pairing until Condon–Shortley is in undual.
-- Not part of 'symbolicExamplesOk'.
cupFusedSpinHalfCoherent :: Bool
cupFusedSpinHalfCoherent =
  let v :: ToVSector ('Atom 1) ('AtomM 1)
      v = unsafeFromArray (VS.fromList [1, 0])
      r = RConsAtomAtomM v RNil :: RepV '[ '( 'Atom 1, 'AtomM 1)]
      td = tensorAtomDual r (dual r)
      RConsAtomAtomM uUnf RNil = cupUnfused @1 @1 td
      RConsAtomAtomM uFus RNil = cup @'[ '( 'Atom 1, 'AtomM 1)] (fuse td)
   in abs (unitAmp uFus - unitAmp uUnf) < 1e-9

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
    , cupUnfusedRepTwoSectorOk
    , coalesceMergeFlatDimOk
    , coalesceMergeDirectSumOk
    , coalescePreservesFlatDimOk
    , projectToSymmetricOk
    ]
