{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Smokes for 'Experiments.Symbolic': term-level checks and compile-time type equalities.
-- Covers 'ToVSpine' / Dual-left Hom / 'fuseExpr' / 'rtensor' / 'cupRdual' / 'composeMor' /
-- Dual-left 'HomUnfused'; fused 'HomFused' as @ToVSpine (FuseHom …)@ (compose stubbed).
module Experiments.SymbolicExamples where

import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..), id)
import Data.Complex (Complex ((:+)), magnitude, realPart)
import Data.Kind (Type)
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (..))
import Data.VectorSpace ((*^))
import Experiments.Categorical.Associative (Associative (..))
import Experiments.Categorical.Bifunctor (Bifunctor (..))
import Experiments.Fusion.Obj as FObj
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

fuseOneSectorProdOk :: Bool
fuseOneSectorProdOk = exFuseOneSectorProd12

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

-- | CG intertwiner: @fuseExpr ∘ (act ⊗ act) ≅ act ∘ fuseExpr@ on @½ ⊗ ½@.
actRepFuseIntertwinesOk :: Bool
actRepFuseIntertwinesOk =
  let left = RConsAtomAtomM sSpinHalfUp RNil
                :: RepV '[ '(1, 'AtomM 1)]
      right = RConsAtomAtomM sSpinHalfUp RNil
      actThenFuse =
        fuseExpr (actRep exRzPi left) (actRep exRzPi right)
      fuseThenAct = actRep exRzPi (fuseExpr left right)
   in repVApproxEq actThenFuse fuseThenAct 1e-9

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

-- | 'fuseExpr' on one atom pair agrees with the flat CG oracle.
fuseExprMatchesReferenceOk :: Bool
fuseExprMatchesReferenceOk =
  let left = RConsAtomAtomM sCoalesce1 RNil
                :: RepV '[ '(1, 'AtomM 2)]
      right = RConsAtomAtomM sTensorRight RNil
                :: RepV '[ '(2, 'AtomM 1)]
      pair = repVToV left ⊗ repVToV right :: AtomPairV 1 2 2 1
   in repVFlatApproxEq
        (repVFlatProdToAtomM (fuseExpr left right))
        (repVFlat (fuseAtomPairCoalescedReference @1 @2 @2 @1 pair))
        1e-10

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

-- | Fused cup agrees with unfused on @j = 0@ (CS = id, scale 1).
cupFusedTrivialOk :: Bool
cupFusedTrivialOk =
  let x :: ToVSector 0 ('AtomM 1)
      x = unsafeFromArray (VS.fromList [3 :+ 4])
      r = RConsAtomAtomM x RNil :: RepV '[ '(0, 'AtomM 1)]
      uUnf =
        cupUnfused @'[ '(0, 'AtomM 1)] (repVToV r ⊗ rdual r)
      RConsAtomAtomM uFus RNil =
        cupFused @'[ '(0, 'AtomM 1)]
          ( projectToSymmetric
              ( fuseExpr @'[ '(0, 'AtomM 1)] @'[ '(0, 'AtomM 1)]
                  r
                  (vToRepV @'[ '(0, 'AtomM 1)] (undualSpine @'[ '(0, 'AtomM 1)] (rdual r)))
              )
          )
   in abs (unitAmp uFus - unitAmp uUnf) < 1e-9

-- | Fused cup on spin-½ agrees with unfused (CS + @√2@ in undual).
cupFusedSpinHalfCoherentOk :: Bool
cupFusedSpinHalfCoherentOk =
  let v :: ToVSector 1 ('AtomM 1)
      v = unsafeFromArray (VS.fromList [1, 0])
      r = RConsAtomAtomM v RNil :: RepV '[ '(1, 'AtomM 1)]
      uUnf =
        cupUnfused @'[ '(1, 'AtomM 1)] (repVToV r ⊗ rdual r)
      RConsAtomAtomM uFus RNil =
        cupFused @'[ '(1, 'AtomM 1)]
          ( projectToSymmetric
              ( fuseExpr @'[ '(1, 'AtomM 1)] @'[ '(1, 'AtomM 1)]
                  r
                  (vToRepV @'[ '(1, 'AtomM 1)] (undualSpine @'[ '(1, 'AtomM 1)] (rdual r)))
              )
          )
   in abs (unitAmp uFus - unitAmp uUnf) < 1e-9

-- | Fused snake @cupFused ∘ capFused@ on @j = 0@.
cupCapFusedSnakeTrivialOk :: Bool
cupCapFusedSnakeTrivialOk =
  let RConsAtomAtomM u RNil =
        cupFused @'[ '(0, 'AtomM 1)]
          (capFused @'[ '(0, 'AtomM 1)] (unitFromScalar 1))
   in abs (unitAmp u - 1) < 1e-9

-- | 'cupMiddleFused' on @Fuse(½⊗½)@ agrees with 'cupFused' ∘ project.
cupMiddleFusedSpinHalfOk :: Bool
cupMiddleFusedSpinHalfOk =
  let v :: ToVSector 1 ('AtomM 1)
      v = unsafeFromArray (VS.fromList [1, 0])
      r = RConsAtomAtomM v RNil :: RepV '[ '(1, 'AtomM 1)]
      mid =
        repVToV @(FuseHom '[ '(1, 'AtomM 1)] '[ '(1, 'AtomM 1)])
          ( fuseExpr @'[ '(1, 'AtomM 1)] @'[ '(1, 'AtomM 1)]
              r
              (vToRepV @'[ '(1, 'AtomM 1)] (undualSpine @'[ '(1, 'AtomM 1)] (rdual r)))
          )
      uMid = cupMiddleFused @'[ '(1, 'AtomM 1)] mid
      RConsAtomAtomM uFus RNil =
        cupFused @'[ '(1, 'AtomM 1)]
          ( projectToSymmetric
              ( fuseExpr @'[ '(1, 'AtomM 1)] @'[ '(1, 'AtomM 1)]
                  r
                  (vToRepV @'[ '(1, 'AtomM 1)] (undualSpine @'[ '(1, 'AtomM 1)] (rdual r)))
              )
          )
   in toVApproxEq (toArray uMid) (toArray (unitToVFromScalar (unitAmp uFus :+ 0)))

-- | Right unitor absorbs @Unit@ on Dual-left Hom (@m ⊗ 1 ≅ m@).
unitRunitMorTrivialOk :: Bool
unitRunitMorTrivialOk =
  let m = (5 :+ 0) *^ idMor @'[ '(0, 'AtomM 1)]
      u = unitToVFromScalar 1
   in toVApproxEq
        (toArray
           ( unitRunit
               @( DualVector (ToVSpine '[ '(0, 'AtomM 1)])
                    ⊗ ToVSpine '[ '(0, 'AtomM 1)]
                )
               $ (m ⊗ u)
           ))
        (toArray m)

-- | @(cup ⊗ id)@ then unitor on a packed assoc-shape state: @cup(η_b) = dim b@.
cupTensorIdUnitorOk :: Bool
cupTensorIdUnitorOk =
  let packed =
        rdual @'[ '(0, 'AtomM 1)] (unitFromScalar 1)
          ⊗ ( capUnfused @'[ '(1, 'AtomM 1)] (unitToVFromScalar 1)
                ⊗ repVToV @'[ '(0, 'AtomM 1)] (unitFromScalar 1)
            )
      out =
        unitorCompose
          @'[ '(0, 'AtomM 1)]
          @'[ '(0, 'AtomM 1)]
          ( cupTensorIdCompose
              @'[ '(0, 'AtomM 1)]
              @'[ '(1, 'AtomM 1)]
              @'[ '(0, 'AtomM 1)]
              packed
          )
      -- @cup ∘ cap = 2@ on spin-½; result is scale on Dual-left @η@.
      expected = 2 *^ idMor @'[ '(0, 'AtomM 1)]
   in all (\(x, y) -> magnitude (x - y) < 1e-9)
        (zip (VS.toList (toArray out)) (VS.toList (toArray expected)))

toVApproxEq :: VS.Vector (Complex Double) -> VS.Vector (Complex Double) -> Bool
toVApproxEq u v =
  VS.length u == VS.length v
    && VS.and (VS.zipWith (\x y -> magnitude (x - y) < 1e-9) u v)

-- | @composeMor id id ≅ id@ on @j = 0@.
composeMorIdIdOk :: Bool
composeMorIdIdOk =
  let i = idMor @'[ '(0, 'AtomM 1)]
   in toVApproxEq
        (toArray (composeMor @'[ '(0, 'AtomM 1)] @'[ '(0, 'AtomM 1)] @'[ '(0, 'AtomM 1)] i i))
        (toArray i)

-- | Left unit law: @composeMor id f ≅ f@ on spin-½.
composeMorLeftUnitOk :: Bool
composeMorLeftUnitOk =
  let i = idMor @'[ '(1, 'AtomM 1)]
      f = (3 :+ 0) *^ idMor @'[ '(1, 'AtomM 1)]
   in toVApproxEq
        (toArray (composeMor @'[ '(1, 'AtomM 1)] @'[ '(1, 'AtomM 1)] @'[ '(1, 'AtomM 1)] i f))
        (toArray f)

-- | Right unit law: @composeMor f id ≅ f@ on spin-½.
composeMorRightUnitOk :: Bool
composeMorRightUnitOk =
  let i = idMor @'[ '(1, 'AtomM 1)]
      f = (3 :+ 0) *^ idMor @'[ '(1, 'AtomM 1)]
   in toVApproxEq
        (toArray (composeMor @'[ '(1, 'AtomM 1)] @'[ '(1, 'AtomM 1)] @'[ '(1, 'AtomM 1)] f i))
        (toArray f)

-- | Unfused 'composeMor' matches ordinary map composition.
--
-- Spines: spin-½ (@C 1 ⊗ C 2@) → spin-½ → spin-1 (@C 1 ⊗ C 3@), with @id@ on
-- the trivial copy leg. Hom elements are @asTensor@ of the linear maps;
-- @composeMor f g@ is compared to @g ∘ f@ on the standard basis.
composeMorMatchesMatMulOk :: Bool
composeMorMatchesMatMulOk =
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
        asTensor -+$=> uf
          :: DualVector (ToVSpine '[ '(1, 'AtomM 1)])
               ⊗ ToVSpine '[ '(1, 'AtomM 1)]
      gHom =
        asTensor -+$=> ug
          :: DualVector (ToVSpine '[ '(1, 'AtomM 1)])
               ⊗ ToVSpine '[ '(2, 'AtomM 1)]
      hHom =
        composeMor
          @'[ '(1, 'AtomM 1)]
          @'[ '(1, 'AtomM 1)]
          @'[ '(2, 'AtomM 1)]
          fHom
          gHom
      h = fromTensor -+$=> hHom :: (C 1 ⊗ C 2) +> (C 1 ⊗ C 3)
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
    , cupMiddleFusedSpinHalfOk
    , unitRunitMorTrivialOk
    , cupTensorIdUnitorOk
    , composeMorIdIdOk
    , composeMorLeftUnitOk
    , composeMorRightUnitOk
    , composeMorMatchesMatMulOk
    , composeMorObjIdIdOk
    , bimapHomUnfusedIdIdOk
    , associateHomUnfusedRoundtripOk
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

-- | Fused Hom is @ToVSpine (FuseHom …)@ (coalesced Rep), not Dual-left.
type SmokeHomFused =
  AssertEqType
    (ToVSpine (FuseHom (FuseSym ('FObj.Atom 1)) (FuseSym ('FObj.Atom 1))))
    (ToVSpine (FuseHom '[ '(1, 'AtomM 1)] '[ '(1, 'AtomM 1)]))

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
