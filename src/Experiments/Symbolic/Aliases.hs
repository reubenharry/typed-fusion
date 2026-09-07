{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

-- | Concrete leaf / Hom / association spine aliases for symbolic SU(2).
--
-- 'Spine0'..'Spine3' are skeletal 'HomFused' objects. 'Leaf0'..'Leaf3' are the
-- expanded leaf 'Rep's (@SpineRep@) used by 'FuseRep' \/ F-moves.
module Experiments.Symbolic.Aliases
  ( Spine0
  , Spine1
  , Spine2
  , Spine3
  , Leaf0
  , Leaf1
  , Leaf2
  , Leaf3
  , Hom00
  , Hom11
  , Hom22
  , Hom33
  , Hom12
  , Hom21
  , Inter00
  , Inter11
  , Inter22
  , AssocL111
  , AssocR111
  , AssocL000
  , AssocR000
  , AssocL110
  , AssocR110
  , AssocL112
  , AssocR112
  , Dom111
  , Mid111
  , CupR111
  , Dom000
  , CupR000
  ) where

import Experiments.Symbolic.Expr
import Experiments.Symbolic.TypeLevel (FilterTrivial, FuseRep, SpineRep)

-- | Skeletal HomFused objects: finite-support @(2j, multiplicity)@.
type Spine0 = '[ '(0, 1)]
type Spine1 = '[ '(1, 1)]
type Spine2 = '[ '(2, 1)]
type Spine3 = '[ '(3, 1)]

-- | Leaf 'Rep' expand of the skeletal spines (FuseRep \/ F-move indices).
type Leaf0 = SpineRep Spine0
type Leaf1 = SpineRep Spine1
type Leaf2 = SpineRep Spine2
type Leaf3 = SpineRep Spine3

type Hom00 = FuseRep Leaf0 Leaf0
type Hom11 = FuseRep Leaf1 Leaf1
type Hom22 = FuseRep Leaf2 Leaf2
type Hom33 = FuseRep Leaf3 Leaf3
type Hom12 = FuseRep Leaf1 Leaf2
type Hom21 = FuseRep Leaf2 Leaf1

-- | Intertwiner spines: trivial sector of fused Hom.
type Inter00 = FilterTrivial Hom00
type Inter11 = FilterTrivial Hom11
type Inter22 = FilterTrivial Hom22

-- | Concrete @½⊗½⊗½@ association trees (matches compile-time AssocL/R smokes).
type AssocL111 =
  '[ 'Node 1 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Leaf 1)
   , 'Node 1 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 1)
   , 'Node 3 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 1)
   ]

type AssocR111 =
  '[ 'Node 1 ('Leaf 1) ('Node 0 ('Leaf 1) ('Leaf 1))
   , 'Node 1 ('Leaf 1) ('Node 2 ('Leaf 1) ('Leaf 1))
   , 'Node 3 ('Leaf 1) ('Node 2 ('Leaf 1) ('Leaf 1))
   ]

type AssocL000 =
  '[ 'Node 0 ('Node 0 ('Leaf 0) ('Leaf 0)) ('Leaf 0)]

type AssocR000 =
  '[ 'Node 0 ('Leaf 0) ('Node 0 ('Leaf 0) ('Leaf 0))]

type AssocL110 =
  '[ 'Node 0 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Leaf 0)
   , 'Node 2 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 0)
   ]

type AssocR110 =
  '[ 'Node 0 ('Leaf 1) ('Node 1 ('Leaf 1) ('Leaf 0))
   , 'Node 2 ('Leaf 1) ('Node 1 ('Leaf 1) ('Leaf 0))
   ]

type AssocL112 =
  '[ 'Node 2 ('Node 0 ('Leaf 1) ('Leaf 1)) ('Leaf 2)
   , 'Node 0 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 2)
   , 'Node 2 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 2)
   , 'Node 4 ('Node 2 ('Leaf 1) ('Leaf 1)) ('Leaf 2)
   ]

type AssocR112 =
  '[ 'Node 0 ('Leaf 1) ('Node 1 ('Leaf 1) ('Leaf 2))
   , 'Node 2 ('Leaf 1) ('Node 1 ('Leaf 1) ('Leaf 2))
   , 'Node 2 ('Leaf 1) ('Node 3 ('Leaf 1) ('Leaf 2))
   , 'Node 4 ('Leaf 1) ('Node 3 ('Leaf 1) ('Leaf 2))
   ]

type Dom111 = FuseRep (FuseRep Leaf1 Leaf1) Hom11
type Mid111 = FuseRep Leaf1 (FuseRep Leaf1 Hom11)
type CupR111 = FuseRep Leaf1 AssocL111
type Dom000 = FuseRep (FuseRep Leaf0 Leaf0) Hom00
type CupR000 = FuseRep Leaf0 (FuseRep Hom00 Leaf0)
