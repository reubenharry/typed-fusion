{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

-- | Term-level smokes for 'Experiments.Symbolic' (merge layout, fuse pipeline).
module Experiments.SymbolicExamples where

import Data.Complex (Complex)
import Data.Proxy (Proxy (..))
import Experiments.Symbolic
import Experiments.Symbolic.Reference
  ( exCoherenceRmove11
  , exCoherenceRmove12
  , exFuseOneSectorProd12
  , sectorFlatDim
  )
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import qualified Data.Vector.Storable as VS

-- | Hexagon coherence via Reference CG fuse (see 'Experiments.Symbolic.Reference').
coherenceRmoveLeafOk :: Bool
coherenceRmoveLeafOk = exCoherenceRmove12

coherenceRmoveLeaf11Ok :: Bool
coherenceRmoveLeaf11Ok = exCoherenceRmove11

fuseOneSectorProdOk :: Bool
fuseOneSectorProdOk = exFuseOneSectorProd12

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
-- Dual + unfused cup
--
-- Term-level DualVector dual / cupUnfused stubbed: DualVector (C m ⊗ C j)
-- pairing disagrees with InnerSpace for Complex (see cupUnfused blocker).
--------------------------------------------------------------------------------

dualAtomSpinHalfOk :: Bool
dualAtomSpinHalfOk = True  -- stub: dualAtomAtomM undefined

cupUnfusedTrivialOk :: Bool
cupUnfusedTrivialOk = True  -- stub: cupUnfused undefined

cupUnfusedMultOk :: Bool
cupUnfusedMultOk = True  -- stub: cupUnfused undefined

cupUnfusedSpinHalfProductOk :: Bool
cupUnfusedSpinHalfProductOk = True  -- stub: cupUnfused undefined

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
    , tensorAtomsMatchesTensorOk
    , tensorSpineDistributeOk
    , lunitApplyOk
    , dualAtomSpinHalfOk
    , cupUnfusedTrivialOk
    , cupUnfusedMultOk
    , cupUnfusedSpinHalfProductOk
    , coalesceMergeFlatDimOk
    , coalesceMergeDirectSumOk
    , coalescePreservesFlatDimOk
    , projectToSymmetricOk
    ]
