{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

-- | Concrete atom / Hom / association aliases for symbolic SU(2).
--
-- 'Atom0'..'Atom3' are 'HomFused' objects. 'Spine*' = 'ObjSpineSU2' of those
-- atoms; 'Leaf*' = 'ObjRep' \/ 'SpineRep' expand used by 'FuseRep' \/ F-moves.
module Experiments.Symbolic.Aliases
  ( Atom0
  , Atom1
  , Atom2
  , Atom3
  , Spine0
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

import Experiments.Fusion.Obj (Obj)
import qualified Experiments.Fusion.Obj as FObj
import Experiments.Symbolic.Expr
import Experiments.Symbolic.TypeLevel
  ( FilterTrivial
  , FuseRep
  , ObjRep
  , ObjSpineSU2
  , SpineRep
  )

-- | HomFused object atoms (@2j@ labels).
type Atom0 = 'FObj.Atom 0
type Atom1 = 'FObj.Atom 1
type Atom2 = 'FObj.Atom 2
type Atom3 = 'FObj.Atom 3

-- | Skeletal spines of the atoms (@ObjSpineSU2@).
type Spine0 = ObjSpineSU2 Atom0
type Spine1 = ObjSpineSU2 Atom1
type Spine2 = ObjSpineSU2 Atom2
type Spine3 = ObjSpineSU2 Atom3

-- | Leaf 'Rep' expand (@ObjRep@) for FuseRep \/ F-moves.
type Leaf0 = ObjRep Atom0
type Leaf1 = ObjRep Atom1
type Leaf2 = ObjRep Atom2
type Leaf3 = ObjRep Atom3

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
