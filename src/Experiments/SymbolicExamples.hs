{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

-- | Term-level smokes for 'Experiments.Symbolic' (merge layout, fuse pipeline).
module Experiments.SymbolicExamples where

import Data.Proxy (Proxy (..))
import Experiments.Symbolic
import Experiments.Symbolic.Reference (sectorFlatDim)
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import qualified Data.Vector.Storable as VS

--------------------------------------------------------------------------------
-- Coalesce merge (direct-sum layout)
--------------------------------------------------------------------------------

-- | @j = 1@, @'AtomM 2@: two copy slots × @C 2@.
sCoalesce1 :: SectorV ('Atom 1) ('AtomM 2)
sCoalesce1 =
  SV $
    unsafeFromArray $
      VS.fromList [1, 0, 0, 1]

-- | @j = 1@, @'AtomM 3@: three copy slots × @C 2@ (flat length @6@).
sCoalesce2 :: SectorV ('Atom 1) ('AtomM 3)
sCoalesce2 =
  SV $
    unsafeFromArray $
      VS.fromList [2, 0, 0, 2, 3, 0]

exCoalesceMerge :: RepV '[ '( 'Atom 1, 'AtomM 5)]
exCoalesceMerge =
  coalesce @'[ '( 'Atom 1, 'AtomM 2), '( 'Atom 1, 'AtomM 3)] $
    RCons sCoalesce1 (RCons sCoalesce2 RNil)

-- | Merged sector flat length matches coalesced multiplicity × irrep dim.
coalesceMergeFlatDimOk :: Bool
coalesceMergeFlatDimOk =
  let RCons (SV v) RNil = exCoalesceMerge
   in VS.length (toArray v)
        == sectorFlatDim (Proxy @'( 'Atom 1, 'AtomM 5))

-- | Merge stacks copy slots (via 'TensorNetwork.Categorical.mergeCopyAxis').
coalesceMergeDirectSumOk :: Bool
coalesceMergeDirectSumOk =
  let RCons (SV v) RNil = exCoalesceMerge
   in toArray v
        == VS.fromList [1, 0, 0, 1, 2, 0, 0, 2, 3, 0]

-- | Total flat dim unchanged by 'coalesce' on this spine.
coalescePreservesFlatDimOk :: Bool
coalescePreservesFlatDimOk =
  let SV v1 = sCoalesce1
      SV v2 = sCoalesce2
      RCons (SV vMerged) RNil =
        coalesce
          @'[ '( 'Atom 1, 'AtomM 2)
             , '( 'Atom 1, 'AtomM 3)
             ]
          (RCons sCoalesce1 (RCons sCoalesce2 RNil))
   in VS.length (toArray v1) + VS.length (toArray v2)
        == VS.length (toArray vMerged)

-- | All symbolic smokes in one place (for REPL / probes).
symbolicExamplesOk :: Bool
symbolicExamplesOk =
  and
    [ coalesceMergeFlatDimOk
    , coalesceMergeDirectSumOk
    , coalescePreservesFlatDimOk
    ]
