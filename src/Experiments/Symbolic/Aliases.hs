{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

-- | Concrete atom / Hom / association aliases for symbolic SU(2).
--
-- 'Atom0'..'Atom3' are 'HomFused' objects. 'Spine*' = 'ObjSpineSU2' of those
-- atoms; 'I*' = 'ObjRep' \/ 'SpineRep' expand used by 'FuseRep' \/ F-moves.
module Experiments.Symbolic.Aliases
  ( Atom0
  , Atom1
  , Atom2
  , Atom3
  , Spine0
  , Spine1
  , Spine2
  , Spine3
  , I0
  , I1
  , I2
  , I3
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
  , Spin (..)
  , type (/)
  , TJ
  ) where

import Experiments.Fusion.Obj (Obj)
import qualified Experiments.Fusion.Obj as FObj
import Experiments.Fusion.SU2 (Spin (..), TJ, type (/))
import Experiments.Symbolic.Expr
import Experiments.Symbolic.TypeLevel
  ( FilterTrivial
  , FuseRep
  , ObjRep
  , ObjSpineSU2
  , SpineRep
  )

-- | HomFused object atoms (@2j@ labels; spin fractions via 'TJ' ∘ @('/')@).
type Atom0 = 'FObj.Atom 0
type Atom1 = 'FObj.Atom (TJ (1 / 2))
type Atom2 = 'FObj.Atom (TJ (1 / 1))
type Atom3 = 'FObj.Atom (TJ (3 / 2))

-- | Skeletal spines of the atoms (@ObjSpineSU2@).
type Spine0 = ObjSpineSU2 Atom0
type Spine1 = ObjSpineSU2 Atom1
type Spine2 = ObjSpineSU2 Atom2
type Spine3 = ObjSpineSU2 Atom3

-- | I 'Rep' expand (@ObjRep@) for FuseRep \/ F-moves.
type I0 = ObjRep Atom0
type I1 = ObjRep Atom1
type I2 = ObjRep Atom2
type I3 = ObjRep Atom3

type Hom00 = FuseRep I0 I0
type Hom11 = FuseRep I1 I1
type Hom22 = FuseRep I2 I2
type Hom33 = FuseRep I3 I3
type Hom12 = FuseRep I1 I2
type Hom21 = FuseRep I2 I1

-- | Intertwiner spines: trivial sector of fused Hom.
type Inter00 = FilterTrivial Hom00
type Inter11 = FilterTrivial Hom11
type Inter22 = FilterTrivial Hom22

-- | Concrete @½⊗½⊗½@ association trees (matches compile-time AssocL/R smokes).
type AssocL111 =
  '[ 'From 1 '( 'From 0 '( 'I 1, 'I 1), 'I 1)
   , 'From 1 '( 'From 2 '( 'I 1, 'I 1), 'I 1)
   , 'From 3 '( 'From 2 '( 'I 1, 'I 1), 'I 1)
   ]

type AssocR111 =
  '[ 'From 1 '( 'I 1, 'From 0 '( 'I 1, 'I 1))
   , 'From 1 '( 'I 1, 'From 2 '( 'I 1, 'I 1))
   , 'From 3 '( 'I 1, 'From 2 '( 'I 1, 'I 1))
   ]

type AssocL000 =
  '[ 'From 0 '( 'From 0 '( 'I 0, 'I 0), 'I 0)]

type AssocR000 =
  '[ 'From 0 '( 'I 0, 'From 0 '( 'I 0, 'I 0))]

type AssocL110 =
  '[ 'From 0 '( 'From 0 '( 'I 1, 'I 1), 'I 0)
   , 'From 2 '( 'From 2 '( 'I 1, 'I 1), 'I 0)
   ]

type AssocR110 =
  '[ 'From 0 '( 'I 1, 'From 1 '( 'I 1, 'I 0))
   , 'From 2 '( 'I 1, 'From 1 '( 'I 1, 'I 0))
   ]

type AssocL112 =
  '[ 'From 2 '( 'From 0 '( 'I 1, 'I 1), 'I 2)
   , 'From 0 '( 'From 2 '( 'I 1, 'I 1), 'I 2)
   , 'From 2 '( 'From 2 '( 'I 1, 'I 1), 'I 2)
   , 'From 4 '( 'From 2 '( 'I 1, 'I 1), 'I 2)
   ]

type AssocR112 =
  '[ 'From 0 '( 'I 1, 'From 1 '( 'I 1, 'I 2))
   , 'From 2 '( 'I 1, 'From 1 '( 'I 1, 'I 2))
   , 'From 2 '( 'I 1, 'From 3 '( 'I 1, 'I 2))
   , 'From 4 '( 'I 1, 'From 3 '( 'I 1, 'I 2))
   ]

type Dom111 = FuseRep (FuseRep I1 I1) Hom11
type Mid111 = FuseRep I1 (FuseRep I1 Hom11)
type CupR111 = FuseRep I1 AssocL111
type Dom000 = FuseRep (FuseRep I0 I0) Hom00
type CupR000 = FuseRep I0 (FuseRep Hom00 I0)
