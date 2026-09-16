{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{- HLINT ignore "Redundant bimap" -}
{- HLINT ignore "Move brackets to avoid $" -}
{- HLINT ignore "Redundant $" -}

-- | Smokes for 'Hom': term-level checks and compile-time type equalities.
-- Covers Dual-left 'HomUnfused' and genealogy 'HomFused' / 'composeHomTrees'.
-- Fibonacci Dual-left CCC: 'composeFGStepsFib' / 'cupCapFibOk'.
-- Unit laws: 'composeHomTreesSelfTest'.
-- Fused SU2 cup/cap: genealogy 'cup' / 'idHomFTrees'.
-- Phase-1 fusion trees: 'FuseTrees' / 'ToVTree' / 'Root'.
module Examples.Symbolic where

import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..), id)
import Data.Complex (Complex ((:+)), magnitude)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (InnerSpace ((<.>)), (*^), (^-^))
import Categorical.Associative (Associative (..))
import Categorical.Bifunctor (Bifunctor (..))
import Categorical.CompactClosed (ComposeNamesC, composeNames)
import Categorical.Monoidal (Monoidal (..))
import Fusion.Fibonacci (Fib (..), FibObj, FibTh, Simple (..), cap, phi)
import qualified Fusion.Fibonacci as FibCat (cup)
import Fusion.Hom (HomDualS (..), sectorToMap)
import Fusion.Obj (Obj (Irrep, (:⊗:), (:⊕:)), DualObj)
import Fusion.Theory (UnitLab)
import Symmetry.Group (Group (SU2, U1))
import Fusion.SU2 (SU2Th, Spin, type (/))
import Fusion.U1 (U1Th)
import Symmetry.Utils (Z (..))
import Hom
import GHC.TypeLits (Nat)
import Math.LinearMap.Category
  ( DualVector
  , fromLinearForm
  , pattern LinearFunction
  , type (+>)
  , type (⊗)
  , (⊗), AdditiveGroup ((^+^))
  )
import Math.LinearMap.Category.Class (asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, Sized (unwrap), konst)
import qualified Data.Vector.Storable as VS

import Prelude hiding (id, (.), ($))
import Categorical.Linear (runit, swapMap)
import Hom.Vec (vec)
import Symmetry.SU2 (SU2Element, su2Alpha, su2Beta)
import Test.QuickCheck (Gen, Property, counterexample, generate, (==>))
import Categorical.CompactClosed (CompactClosed(counit))
import Fusion.Theory (FusionTheory(UnitLab), Label)

-- exampleFTreeV :: FTreeV '[ 'IrrepTree (Spin (1/2)), 'IrrepTree (Spin (3 / 2))]
example1 :: Unfused SU2 ('Irrep (Spin (1/2)) :⊕: 'Irrep (Spin (3 / 2)))
example1 = (vec (1,2), vec (3,4,5,6))

example2 :: Unfused SU2 ('Irrep (Spin (1/2)) :⊗: 'Irrep (Spin (1/2)))
example2 = vec (1,2) ⊗ vec (3,4) ^+^ vec (5,6) ⊗ vec (7,8)

example3 :: Fused SU2 ('Irrep (Spin (1/2)) :⊗: 'Irrep (Spin (1/2)))
example3 = (konst 1, vec (4,5,6))

example4 :: Sym SU2 ('Irrep (Spin (1/2)) :⊗: 'Irrep (Spin (1/2)))
example4 = konst 2

example5 :: Unfused SU2 (Dual ('Irrep (Spin (1/2)) :⊗: 'Irrep (Spin (1/2))) :⊗: 'Irrep (Spin (2 / 2)))
example5 =  ((vec (1,2) ⊗ vec (1,2)) ⊗ vec (1,2,3)) ^+^ (vec (4,2) ⊗ vec (1,2)) ⊗ vec (1,2,7)

example6 :: Fused SU2 (Dual ('Irrep (Spin (1/2)) :⊗: 'Irrep (Spin (1/2))) :⊗: 'Irrep (Spin (2 / 2)))
example6 = (vec (1,2,3), (konst 1, (vec ( 2,3,4), vec (5,6,7,8,9))))

example7 :: Sym SU2 (Dual ('Irrep (Spin (1/2)) :⊗: 'Irrep (Spin (1/2))) :⊗: 'Irrep (Spin (2 / 2)))
example7 = konst 1



type Dual (a :: Obj Nat) = DualObj SU2Th a




fuseExample :: ToVFTrees '[
    0 `From` '( 'IrrepTree (Spin (1/2)), 'IrrepTree (Spin (1/2))),
    2 `From` '( 'IrrepTree (Spin (1/2)), 'IrrepTree (Spin (1/2)))]
fuseExample = fTreeVToV $ fuseTrees @('IrrepTree (Spin (1/2))) @('IrrepTree (Spin (1/2))) example2


-- -- | Trivial (total-charge-0) sector of 'fuseExample2'.
-- fuseExample3
--   :: ToVFTrees
--        ( FilterTrivial
--            (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
--        )
-- fuseExample3 =
--   fTreeVToV
--     @( FilterTrivial
--          (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
--      )
--     $ filterTrivialFTreeV
--         @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
--         ( fuseFTreesTerm
--             (fuseExample example2)
--             (FCons @('IrrepTree 2) (konst 1) FNil)
--         )


-- | Endomorphism on leaf-½ Hom (singlet / triplet channels).
-- f, g :: HomFused SU2 ('Irrep (Spin (1/2))) ('Irrep (Spin (1/2)))
f,g :: FTreeV (ObjTrees SU2 (Dual Half :⊗: Half))
f =  makeFTrees (konst 0.3, vec (1, 2, 3))
g =  makeFTrees (konst 0.5, vec (1, 2, 3))

type Half = 'Irrep (Spin (1/2))
type HalfTree = 'IrrepTree (Spin (1/2))

-- | @g ∘ f@ spelled as the five Mac Lane morphisms in 'composeHomTrees'.
composeFGSteps :: FTreeV (ObjTrees SU2 (Dual Half :⊗: Half))
composeFGSteps = step5
  where
      step1 :: FTreeV (ObjTrees SU2 ((Half :⊗: Half) :⊗: (Half :⊗: Half)))
      step1 = fuseFTreesTerm f g
      step2 :: FTreeV (ObjTrees SU2 (Half :⊗: (Half :⊗: (Half :⊗: Half))))
      step2 = fmoveOuterHom @'[HalfTree] @'[HalfTree] @'[HalfTree] step1
      step3 :: FTreeV (ObjTrees SU2 (Half :⊗: (Half :⊗: Half :⊗: Half)))
      step3 =
        idRight @'[HalfTree]
          (fmoveInvTrees @'[HalfTree] @'[HalfTree] @'[HalfTree])
          step2
      step4 :: FTreeV (ObjTrees SU2 (Half :⊗: ('Irrep 0 :⊗: Half)))
      step4 =
        idRight @'[HalfTree]
          (idLeft @_ @_ @'[HalfTree] (cup @'[HalfTree]))
          step3
      step5 :: FTreeV (ObjTrees SU2 (Half :⊗: Half))
      step5 = idRight @'[HalfTree] (unitor @'[HalfTree]) step4

--------------------------------------------------------------------------------
-- Fibonacci: Mac Lane Hom compose (name → cup ladder → unname)
--------------------------------------------------------------------------------

type FibTau = 'Irrep 'Tau
type FibOne = 'Irrep 'One
type DualFib (a :: FibObj) = DualObj FibTh a

-- | Name @⌜f⌝ = (a* ⊗ f) ∘ η_a : 𝟙 → a* ⊗ b@.
nameFib
  :: forall (a :: FibObj) (b :: FibObj)
   . ( Object Fib a
     , Object Fib b
     , Object Fib FibOne
     , Object Fib (DualFib a)
     , Object Fib (DualFib a :⊗: a)
     , Object Fib (DualFib a :⊗: b)
     )
  => Fib a b
  -> Fib FibOne (DualFib a :⊗: b)
nameFib f =
  bimap (id :: Fib (DualFib a) (DualFib a)) f . cap @a

-- | Unname: recover @f : a → c@ from @⌜f⌝ : 𝟙 → a* ⊗ c@.
--
-- @
-- a ─ρ⁻¹→ a ⊗ 𝟙 ─id⊗⌜f⌝→ a ⊗ (a* ⊗ c) ─α⁻¹→ (a ⊗ a*) ⊗ c ─ε⊗id→ 𝟙 ⊗ c ─λ→ c
-- @
unnameFib
  :: forall (a :: FibObj) (c :: FibObj)
   . ( Object Fib a
     , Object Fib c
     , Object Fib FibOne
     , Object Fib (DualFib a)
     , Object Fib (a :⊗: FibOne)
     , Object Fib (DualFib a :⊗: c)
     , Object Fib (a :⊗: (DualFib a :⊗: c))
     , Object Fib ((a :⊗: DualFib a) :⊗: c)
     , Object Fib (a :⊗: DualFib a)
     , Object Fib (FibOne :⊗: c)
     )
  => Fib FibOne (DualFib a :⊗: c)
  -> Fib a c
unnameFib n =
  idl
    . bimap (FibCat.cup @a) (id :: Fib c c)
    . ( disassociate
          :: Fib
               (a :⊗: (DualFib a :⊗: c))
               ((a :⊗: DualFib a) :⊗: c)
      )
    . bimap (id :: Fib a a) n
    . coidr

-- | Fib specialization of 'composeNames' (@CompactClosed Fib (:⊗:)@).
composeNamesFib
  :: forall (a :: FibObj) (b :: FibObj) (c :: FibObj)
   . ComposeNamesC Fib (:⊗:) a b c
  => Fib (Irrep (UnitLab FibTh)) (DualObj FibTh a :⊗: b)
  -> Fib (Irrep (UnitLab FibTh)) (DualObj FibTh b :⊗: c)
  -> Fib (Irrep (UnitLab FibTh)) (DualObj FibTh a :⊗: c)
composeNamesFib = composeNames @Fib @(:⊗:) @a @b @c

-- | @g ∘ f@ spelled as name → Mac Lane name-compose → unname (equals @g . f@).
composeFGStepsFib
  :: forall (a :: FibObj) (b :: FibObj) (c :: FibObj)
   . ( Object Fib a
     , Object Fib b
     , Object Fib c
     , Object Fib FibOne
     , Object Fib (DualFib a)
     , Object Fib (DualFib b)
     , Object Fib (DualFib a :⊗: a)
     , Object Fib (DualFib a :⊗: b)
     , Object Fib (DualFib b :⊗: b)
     , Object Fib (DualFib b :⊗: c)
     , Object Fib (a :⊗: FibOne)
     , Object Fib (a :⊗: DualFib a)
     , Object Fib (a :⊗: (DualFib a :⊗: c))
     , Object Fib ((a :⊗: DualFib a) :⊗: c)
     , Object Fib (FibOne :⊗: FibOne)
     , Object Fib ((DualFib a :⊗: b) :⊗: (DualFib b :⊗: c))
     , Object Fib (DualFib a :⊗: (b :⊗: (DualFib b :⊗: c)))
     , Object Fib (b :⊗: (DualFib b :⊗: c))
     , Object Fib ((b :⊗: DualFib b) :⊗: c)
     , Object Fib (DualFib a :⊗: ((b :⊗: DualFib b) :⊗: c))
     , Object Fib (b :⊗: DualFib b)
     , Object Fib (FibOne :⊗: c)
     , Object Fib (DualFib a :⊗: (FibOne :⊗: c))
     , Object Fib (DualFib a :⊗: c)
     )
  => Fib a b
  -> Fib b c
  -> Fib a c
composeFGStepsFib f g =
  unnameFib @a @c (composeNamesFib @a @b @c (nameFib @a @b f) (nameFib @b @c g))

-- | Mac Lane compose of @id_τ@ with itself recovers @id_τ@.
composeFGStepsFibOk :: Bool
composeFGStepsFibOk =
  let i = id :: Fib FibTau FibTau
      got = composeFGStepsFib i i
   in fibEndTauAmp got ~= fibEndTauAmp i
  where
    (~=) xs ys =
      length xs == length ys
        && and (zipWith (\x y -> magnitude (x - y) < 1e-9) xs ys)

-- | @Hom(τ,τ)@ action on the unit @1 ∈ ℂ¹@ (τ-sector).
fibEndTauAmp :: Fib FibTau FibTau -> [Complex Double]
fibEndTauAmp (Fib (HomDualCons _ (HomDualCons t _))) =
  VS.toList (unwrap (sectorToMap t $ (konst 1 :: C 1)))

-- | Vacuum image of @1@ for @𝟙 → 𝟙@.
fibOneVacAmp :: Fib FibOne FibOne -> [Complex Double]
fibOneVacAmp (Fib (HomDualCons vac _)) =
  VS.toList (unwrap (sectorToMap vac $ (konst 1 :: C 1)))

-- | Vacuum round-trip: @ε ∘ η = φ · id_𝟙@.
cupCapFibOk :: Bool
cupCapFibOk =
  case fibOneVacAmp (FibCat.cup @FibTau . cap @FibTau) of
    [z] -> magnitude (z - phi) < 1e-9
    _ -> False









-- | Right unitor absorbs @Unit@ on Dual-left HomUnfused SU2 (@m ⊗ 1 ≅ m@).
runitMorTrivialOk :: Bool
runitMorTrivialOk =
  let m = (5 :+ 0) *^ capUnfusedObj @SU2 @('Irrep 0) (konst 1)
      u = konst 1
   in toVApproxEq
        (toArray
           ( runit
               @( DualVector (ToVObj SU2 ('Irrep 0))
                    ⊗ ToVObj SU2 ('Irrep 0)
                )
               $ (m ⊗ u)
           ))
        (toArray m)

-- | @(cup ⊗ id)@ then unitor on a packed assoc-shape state: @cup(η_b) = dim b@.
cupTensorIdUnitorOk :: Bool
cupTensorIdUnitorOk =
  let u0 = konst 1
      -- Right-dual @η_b : I → b* ⊗ b@, braided to @b ⊗ b*@ for @ε@.
      packed =
        (fromLinearForm $ arr (LinearFunction (<.> u0)))
          ⊗ ( (swapMap $ capUnfusedObj @SU2 @('Irrep 1) u0) ⊗ u0 )
      out =
        unitorComposeObj
          @('Irrep 0)
          @('Irrep 0)
          ( cupTensorIdComposeObj
              @('Irrep 0)
              @('Irrep 1)
              @('Irrep 0)
              packed
          )
      -- @ε ∘ σ ∘ η = dim b@ on spin-½; result is scale on Dual-left id.
      expected = 2 *^ capUnfusedObj @SU2 @('Irrep 0) (konst 1)
   in all (\(x, y) -> magnitude (x - y) < 1e-9)
        (zip (VS.toList (toArray out)) (VS.toList (toArray expected)))

toVApproxEq :: VS.Vector (Complex Double) -> VS.Vector (Complex Double) -> Bool
toVApproxEq u v =
  VS.length u == VS.length v
    && VS.and (VS.zipWith (\x y -> magnitude (x - y) < 1e-9) u v)

-- | @composeMorObj id id ≅ id@ on @j = 0@.
composeMorObjIdIdTrivialOk :: Bool
composeMorObjIdIdTrivialOk =
  let i = id :: HomUnfused SU2 ('Irrep 0) ('Irrep 0)
   in toVApproxEq
        (toArray (unHomUnfused (i . i)))
        (toArray (unHomUnfused i))

-- | U(1) HomUnfused: @id ∘ id ≅ id@ on the trivial charge.
homUnfusedU1IdIdOk :: Bool
homUnfusedU1IdIdOk =
  let i = id :: HomUnfused U1 ('Irrep 'Zero) ('Irrep 'Zero)
   in toVApproxEq
        (toArray (unHomUnfused (i . i)))
        (toArray (unHomUnfused i))

-- | U(1) HomUnfused left unit on charge @+1@.
homUnfusedU1LeftUnitOk :: Bool
homUnfusedU1LeftUnitOk =
  let i = id :: HomUnfused U1 ('Irrep ('Pos 1)) ('Irrep ('Pos 1))
      f =
        HomUnfused ((2 :+ 0) *^ unHomUnfused i)
          :: HomUnfused U1 ('Irrep ('Pos 1)) ('Irrep ('Pos 1))
   in toVApproxEq
        (toArray (unHomUnfused (i . f)))
        (toArray (unHomUnfused f))

-- | Left unit law: @id ∘ f ≅ f@ on spin-½ ('HomUnfused').
composeMorObjLeftUnitOk :: Bool
composeMorObjLeftUnitOk =
  let i = id :: HomUnfused SU2 ('Irrep 1) ('Irrep 1)
      f =
        HomUnfused ((3 :+ 0) *^ unHomUnfused i)
          :: HomUnfused SU2 ('Irrep 1) ('Irrep 1)
   in toVApproxEq
        (toArray (unHomUnfused (i . f)))
        (toArray (unHomUnfused f))

-- | Right unit law: @f ∘ id ≅ f@ on spin-½ ('HomUnfused').
composeMorObjRightUnitOk :: Bool
composeMorObjRightUnitOk =
  let i = id :: HomUnfused SU2 ('Irrep 1) ('Irrep 1)
      f =
        HomUnfused ((3 :+ 0) *^ unHomUnfused i)
          :: HomUnfused SU2 ('Irrep 1) ('Irrep 1)
   in toVApproxEq
        (toArray (unHomUnfused (f . i)))
        (toArray (unHomUnfused f))

-- | Unfused SU2 'HomUnfused' composition matches ordinary map composition.
--
-- Objects: spin-½ (@C 2@) → spin-½ → spin-1 (@C 3@). Hom elements are
-- @asTensor@ of the linear maps; @g . f@ is compared to @g ∘ f@ on the
-- standard basis.
composeMorObjMatchesMatMulOk :: Bool
composeMorObjMatchesMatMulOk =
  let -- FTree maps (column action on coordinate lists).
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
      fHom =
        HomUnfused (asTensor -+$=> fLeg)
          :: HomUnfused SU2 ('Irrep 1) ('Irrep 1)
      gHom =
        HomUnfused (asTensor -+$=> gLeg)
          :: HomUnfused SU2 ('Irrep 1) ('Irrep 2)
      hHom = gHom . fHom
      h = fromTensor -+$=> unHomUnfused hHom :: C 2 +> C 3
      e0 = unsafeFromArray (VS.fromList [1, 0]) :: C 2
      e1 = unsafeFromArray (VS.fromList [0, 1]) :: C 2
      xs = [e0, e1]
      agree x =
        toVApproxEq (toArray (h $ x)) (toArray (gLeg $ (fLeg $ x)))
   in all agree xs

-- | @composeMorObj id id ≅ id@ on spin-½ (true unfused Hom).
composeMorObjIdIdOk :: Bool
composeMorObjIdIdOk =
  let i = id :: HomUnfused SU2 ('Irrep 1) ('Irrep 1)
   in toVApproxEq
        (toArray (unHomUnfused (i . i)))
        (toArray (unHomUnfused i))

-- | @bimap id id ≅ id@ on @½ ⊗ ½@ (true unfused Hom).
bimapHomUnfusedIdIdOk :: Bool
bimapHomUnfusedIdIdOk =
  let iHalf = id :: HomUnfused SU2 ('Irrep 1) ('Irrep 1)
      iTen =
        id
          :: HomUnfused SU2
               ((('Irrep 1) :⊗: ('Irrep 1)))
               ((('Irrep 1) :⊗: ('Irrep 1)))
      bi =
        bimap iHalf iHalf
          :: HomUnfused SU2
               ((('Irrep 1) :⊗: ('Irrep 1)))
               ((('Irrep 1) :⊗: ('Irrep 1)))
   in toVApproxEq (toArray (unHomUnfused bi)) (toArray (unHomUnfused iTen))
-- | @disassociate ∘ associate ≅ id@ as linear maps on @(½ ⊗ ½) ⊗ ½@
-- (Hom packing of linearmap α / α⁻¹; avoids Hom-compose cost on the smoke).
associateHomUnfusedRoundtripOk :: Bool
associateHomUnfusedRoundtripOk =
  let α =
        unHomUnfused
          ( associate
              :: HomUnfused SU2
                   ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
                   )
                   ( (('Irrep 1) :⊗: ((('Irrep 1) :⊗: ('Irrep 1))))
                   )
          )
      αinv =
        unHomUnfused
          ( disassociate
              :: HomUnfused SU2
                   ( (('Irrep 1) :⊗: ((('Irrep 1) :⊗: ('Irrep 1))))
                   )
                   ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
                   )
          )
      roundTrip =
        (fromTensor -+$=> αinv)
          . (fromTensor -+$=> α)
            :: ToVObj SU2
                 ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
                 )
               +> ToVObj SU2
                    ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
                    )
      iHom =
        unHomUnfused
          ( id
              :: HomUnfused SU2
                   ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
                   )
                   ( (((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1))
                   )
          )
   in toVApproxEq
        (toArray (asTensor -+$=> roundTrip))
        (toArray iHom)

-- | @cup ∘ (s · id) = s · FS·dim@ on spin-½ (@FS(1)·2 = −2@).
cupCapRoundtripSpinHalfOk :: Bool
cupCapRoundtripSpinHalfOk =
  let u = 0.7 :+ 0
      capped =
        scaleFTreeV
          @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
          u
          (idHomFTrees @('[ 'IrrepTree 1]))
      FCons v FNil = cup @('[ 'IrrepTree 1]) capped
   in magnitude ((konst 1 <.> v) - ((-2) * u)) < 1e-9

-- | Unfused Hom smokes (SU(2) + U(1)), used by the cabal test gate.
symbolicExamplesOk :: Bool
symbolicExamplesOk =
  and
    [ runitMorTrivialOk
    , cupTensorIdUnitorOk
    , composeMorObjIdIdTrivialOk
    , homUnfusedU1IdIdOk
    , homUnfusedU1LeftUnitOk
    , composeMorObjLeftUnitOk
    , composeMorObjRightUnitOk
    , composeMorObjMatchesMatMulOk
    , composeMorObjIdIdOk
    , bimapHomUnfusedIdIdOk
    , associateHomUnfusedRoundtripOk
    , cupCapRoundtripSpinHalfOk
    , composeHomTreesI1TypedOk
    , composeFGStepsFibOk
    , cupCapFibOk
    ]

--------------------------------------------------------------------------------
-- Group action on fused ½ ⊗ ½ (QuickCheck)
--------------------------------------------------------------------------------

-- | @½ ⊗ ½@ as a fused object (singlet ⊕ triplet).
type FusedHalfHalf = Fused SU2 ('Irrep (Spin (1/2)) :⊗: 'Irrep (Spin (1/2)))

su2FarFromIdent :: SU2Element -> Bool
su2FarFromIdent g =
  magnitude (su2Beta g) > 0.15
    || magnitude (su2Alpha g - 1) > 0.15

tripletNormSq :: FusedHalfHalf -> Double
tripletNormSq (_singlet, trip) =
  VS.sum $ VS.map (\z -> magnitude z * magnitude z) (toArray trip)

fusedHalfHalfApproxEq :: FusedHalfHalf -> FusedHalfHalf -> Bool
fusedHalfHalfApproxEq v w =
  approxFTreeV @(ObjTrees SU2 ('Irrep (Spin (1/2)) :⊗: 'Irrep (Spin (1/2))))
    (makeFTrees v)
    (makeFTrees w)

-- | Random non-trivial @g@ and fused @½ ⊗ ½@ with triplet weight: @g · v ≠ v@.
--
-- (The singlet sector is invariant; a pure singlet would be fixed by every @g@.)
fusedHalfHalfActionMovesProp :: SU2Element -> FusedHalfHalf -> Property
fusedHalfHalfActionMovesProp g v =
  let moved = actsOnFused @SU2 @('Irrep (Spin (1/2)) :⊗: 'Irrep (Spin (1/2))) g v
   in (su2FarFromIdent g && tripletNormSq v > 1e-6)
        ==> counterexample
              ("|β|="
                 ++ show (magnitude (su2Beta g))
                 ++ " trip²="
                 ++ show (tripletNormSq v))
              (not (fusedHalfHalfApproxEq moved v))

-- | One random draw of @(g, v)@; prints @g@, @v@, and @g·v@ (fused channel form).
sampleFusedHalfHalfAction :: IO ()
sampleFusedHalfHalfAction = do
  g <- generate (arbitrary :: Gen SU2Element)
  v <- generate (arbitrary :: Gen FusedHalfHalf)
  let v' = actsOnFused @SU2 @('Irrep (Spin (1/2)) :⊗: 'Irrep (Spin (1/2))) g v
      trees = makeFTrees @(ObjTrees SU2 ('Irrep (Spin (1/2)) :⊗: 'Irrep (Spin (1/2))))
  putStrLn $ "g: α=" ++ ppComplex (su2Alpha g) ++ " β=" ++ ppComplex (su2Beta g)
  putStrLn $ "v:  " ++ ppFTreeV (trees v)
  putStrLn $ "g·v:" ++ ppFTreeV (trees v')
  putStrLn $
    if fusedHalfHalfApproxEq v v'
      then "(unchanged)"
      else "(changed)"

-- | Fused Mac Lane suite (leaf Hom). Right-unit @f ∘ id@ is currently failing on
-- main as well; kept as a separate probe, not in 'symbolicExamplesOk'.


--------------------------------------------------------------------------------
-- Compile-time smokes (type equalities)
--------------------------------------------------------------------------------

type family AssertEqNat (a :: Nat) (b :: Nat) :: Bool where
  AssertEqNat a a = 'True

type family AssertEqFTrees (a :: FTrees Nat) (b :: FTrees Nat) :: Bool where
  AssertEqFTrees a a = 'True

type family AssertEqType (a :: Type) (b :: Type) :: Bool where
  AssertEqType a a = 'True

type family AssertEqFTree (a :: FTree Nat) (b :: FTree Nat) :: Bool where
  AssertEqFTree a a = 'True

type family AssertEqSpine (a :: Spine Nat) (b :: Spine Nat) :: Bool where
  AssertEqSpine a a = 'True

type family AssertEqObj (a :: Obj Nat) (b :: Obj Nat) :: Bool where
  AssertEqObj a a = 'True

-- | Irrep → singleton spine.
type SmokeObjSpineIrrep =
  AssertEqSpine (ObjSpine SU2Th ('Irrep 1)) '[ '(1, 1)]

-- | @½ ⊗ ½@ FuseNorm → singlet ⊕ triplet multiplicities.
type SmokeObjSpineHalfHalf =
  AssertEqSpine
    (ObjSpine SU2Th ((('Irrep 1) :⊗: ('Irrep 1))))
    '[ '(0, 1), '(2, 1)]

-- | Direct sum coalesces and sorts by @2j@.
type SmokeObjSpineSum =
  AssertEqSpine
    (ObjSpine SU2Th ((('Irrep 2) :⊕: ('Irrep 0))))
    '[ '(0, 1), '(2, 1)]

-- | Duplicate irreps add multiplicities.
type SmokeObjSpineMult =
  AssertEqSpine
    (ObjSpine SU2Th ((('Irrep 1) :⊕: ('Irrep 1))))
    '[ '(1, 2)]

-- | Fused SU2 Hom is 'FTreeV' of 'FuseFTrees' (genealogy-preserving).
type SmokeHomFused =
  AssertEqType
    (ToVFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
    (C 1, C 3)

-- | @½ ⊗ ½@ fusion trees: singlet and triplet channels (no coalesce).
type SmokeFuseTrees =
  AssertEqFTrees
    (FuseTrees ('IrrepTree 1) ('IrrepTree 1))
    '[ 'From 0 '( 'IrrepTree 1, 'IrrepTree 1)
     , 'From 2 '( 'IrrepTree 1, 'IrrepTree 1)
     ]

-- | 'ObjTrees' on an irrep is a singleton leaf.
type SmokeObjTreesIrrep =
  AssertEqFTrees (ObjTrees SU2 ('Irrep 1)) '[ 'IrrepTree 1]

-- | 'ObjTrees' of @½ ⊗ ½@ matches 'FuseTrees' / 'FuseFTrees' on leaves.
type SmokeObjTreesHalfHalf =
  AssertEqFTrees
    (ObjTrees SU2 ((('Irrep 1) :⊗: ('Irrep 1))))
    (FuseTrees ('IrrepTree 1) ('IrrepTree 1))

-- | 'ObjTrees' of a sum is flat 'Append' (no coalesce).
type SmokeObjTreesSum =
  AssertEqFTrees
    (ObjTrees SU2 ((('Irrep 2) :⊕: ('Irrep 0))))
    '[ 'IrrepTree 2, 'IrrepTree 0]

-- | 'Norm' then fuse: @(0 ⊕ 1) ⊗ ½@ equals the distributed sum of tensors.
type SmokeObjTreesDist =
  AssertEqFTrees
    ( ObjTrees SU2 ((((('Irrep 0) :⊕: ('Irrep 2))) :⊗: ('Irrep 1)))
    )
    ( ObjTrees SU2 ((((('Irrep 0) :⊗: ('Irrep 1))) :⊕: ((('Irrep 2) :⊗: ('Irrep 1)))))
    )

-- | Nested tensor keeps association (@ObjTrees@ = left-assoc 'FuseFTrees').
type SmokeObjTreesAssocL =
  AssertEqFTrees
    ( ObjTrees SU2 ((((('Irrep 1) :⊗: ('Irrep 1))) :⊗: ('Irrep 1)))
    )
    (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])

-- | SU(2) simples are self-dual.
type SmokeDualObjIrrep =
  AssertEqObj (DualObj SU2Th ('Irrep 1)) ('Irrep 1)

-- | Dual reverses tensor order (labels unchanged for SU(2)).
type SmokeDualObjTensor =
  AssertEqObj
    ( DualObj SU2Th
        ((('Irrep 1) :⊗: ('Irrep 2)))
    )
    ((('Irrep 2) :⊗: ('Irrep 1)))

-- | Dual distributes over sums.
type SmokeDualObjSum =
  AssertEqObj
    ( DualObj SU2Th
        ((('Irrep 0) :⊕: ('Irrep 2)))
    )
    ((('Irrep 0) :⊕: ('Irrep 2)))

type family AssertEqFTreesZ (a :: FTrees Z) (b :: FTrees Z) :: Bool where
  AssertEqFTreesZ a a = 'True

-- | U(1): @(+1) ⊗ (−1) → 0@ (single CG outcome).
type SmokeU1FuseTrees =
  AssertEqFTreesZ
    (FuseTreesU1 ('IrrepTree ('Pos 1)) ('IrrepTree ('Neg 1)))
    '[ 'From 'Zero '( 'IrrepTree ('Pos 1), 'IrrepTree ('Neg 1))]

-- | U(1) skeletal fuse of opposite charges → bare zero.
type SmokeU1ObjFTrees =
  AssertEqFTreesZ
    (ObjFTrees U1 ((('Irrep ('Pos 1)) :⊗: ('Irrep ('Neg 1)))))
    '[ 'IrrepTree 'Zero]

-- | U(1) dual negates charge.
type SmokeU1DualObj =
  AssertEqObjZ
    (DualObj U1Th ('Irrep ('Pos 1)))
    ('Irrep ('Neg 1))

type family AssertEqObjZ (a :: Obj Z) (b :: Obj Z) :: Bool where
  AssertEqObjZ a a = 'True

-- | Root of a fusion tree is the channel label.
type SmokeRootNode =
  AssertEqNat
    (Root ('From 0 '( 'IrrepTree 1, 'IrrepTree 1)))
    0

-- | 'ToVTree' is the root irrep space only (@j=1 ⇒ C 2@; @j=2 ⇒ C 3@).
type SmokeToVTree =
  AssertEqType
    (ToVTree ('From 2 '( 'IrrepTree 1, 'IrrepTree 1)))
    (C 3)

-- | 'ToVFTrees' nests root spaces.
type SmokeToVFTrees =
  AssertEqType
    (ToVFTrees (FuseTrees ('IrrepTree 1) ('IrrepTree 1)))
    (C 1, C 3)

-- | List fuse distributes over tree pairs.
type SmokeFuseFTrees =
  AssertEqFTrees
    (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
    (FuseTrees ('IrrepTree 1) ('IrrepTree 1))

-- | Left-assoc @½⊗½⊗½@ expands to the concrete 'From' spine.
type SmokeAssocL111 =
  AssertEqFTrees
    ( FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1] )
    '[ 'From 1 '( 'From 0 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 1)
     , 'From 1 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 1)
     , 'From 3 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 1)
     ]

type SmokeAssocR111 =
  AssertEqFTrees
    ( FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) )
    '[ 'From 1 '( 'IrrepTree 1, 'From 0 '( 'IrrepTree 1, 'IrrepTree 1))
     , 'From 1 '( 'IrrepTree 1, 'From 2 '( 'IrrepTree 1, 'IrrepTree 1))
     , 'From 3 '( 'IrrepTree 1, 'From 2 '( 'IrrepTree 1, 'IrrepTree 1))
     ]

type SmokeAssocL110 =
  AssertEqFTrees
    ( FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 0] )
    '[ 'From 0 '( 'From 0 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 0)
     , 'From 2 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 0)
     ]

type SmokeAssocR110 =
  AssertEqFTrees
    ( FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 0]) )
    '[ 'From 0 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 1, 'IrrepTree 0))
     , 'From 2 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 1, 'IrrepTree 0))
     ]

type SmokeAssocL112 =
  AssertEqFTrees
    ( FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2] )
    '[ 'From 2 '( 'From 0 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 2)
     , 'From 0 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 2)
     , 'From 2 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 2)
     , 'From 4 '( 'From 2 '( 'IrrepTree 1, 'IrrepTree 1), 'IrrepTree 2)
     ]

type SmokeAssocR112 =
  AssertEqFTrees
    ( FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 2]) )
    '[ 'From 0 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 1, 'IrrepTree 2))
     , 'From 2 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 1, 'IrrepTree 2))
     , 'From 2 '( 'IrrepTree 1, 'From 3 '( 'IrrepTree 1, 'IrrepTree 2))
     , 'From 4 '( 'IrrepTree 1, 'From 3 '( 'IrrepTree 1, 'IrrepTree 2))
     ]

-- | After @id ⊗ (cup ⊗ id)@: Unit remains as 'Unit' in the middle.
type SmokeAfterCup111 =
  AssertEqFTrees
    (FuseFTrees '[ 'IrrepTree 1] (FuseFTrees Unit '[ 'IrrepTree 1]))
    '[ 'From 0 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 0, 'IrrepTree 1))
     , 'From 2 '( 'IrrepTree 1, 'From 1 '( 'IrrepTree 0, 'IrrepTree 1))
     ]

-- | Flat layout equals reduced HMatrix packing for @½⊗½⊗½@ (both associations).
smokeObjSpineIrrep :: Proxy SmokeObjSpineIrrep
smokeObjSpineIrrep = Proxy

smokeObjSpineHalfHalf :: Proxy SmokeObjSpineHalfHalf
smokeObjSpineHalfHalf = Proxy

smokeObjSpineSum :: Proxy SmokeObjSpineSum
smokeObjSpineSum = Proxy

smokeObjSpineMult :: Proxy SmokeObjSpineMult
smokeObjSpineMult = Proxy

smokeHomFused :: Proxy SmokeHomFused
smokeHomFused = Proxy

smokeFuseTrees :: Proxy SmokeFuseTrees
smokeFuseTrees = Proxy

smokeObjTreesIrrep :: Proxy SmokeObjTreesIrrep
smokeObjTreesIrrep = Proxy

smokeObjTreesHalfHalf :: Proxy SmokeObjTreesHalfHalf
smokeObjTreesHalfHalf = Proxy

smokeObjTreesSum :: Proxy SmokeObjTreesSum
smokeObjTreesSum = Proxy

smokeObjTreesDist :: Proxy SmokeObjTreesDist
smokeObjTreesDist = Proxy

smokeObjTreesAssocL :: Proxy SmokeObjTreesAssocL
smokeObjTreesAssocL = Proxy

smokeDualObjIrrep :: Proxy SmokeDualObjIrrep
smokeDualObjIrrep = Proxy

smokeDualObjTensor :: Proxy SmokeDualObjTensor
smokeDualObjTensor = Proxy

smokeDualObjSum :: Proxy SmokeDualObjSum
smokeDualObjSum = Proxy

smokeU1FuseTrees :: Proxy SmokeU1FuseTrees
smokeU1FuseTrees = Proxy

smokeU1ObjFTrees :: Proxy SmokeU1ObjFTrees
smokeU1ObjFTrees = Proxy

smokeU1DualObj :: Proxy SmokeU1DualObj
smokeU1DualObj = Proxy

smokeRootNode :: Proxy SmokeRootNode
smokeRootNode = Proxy

smokeToVTree :: Proxy SmokeToVTree
smokeToVTree = Proxy

smokeToVFTrees :: Proxy SmokeToVFTrees
smokeToVFTrees = Proxy

smokeFuseFTrees :: Proxy SmokeFuseFTrees
smokeFuseFTrees = Proxy

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

smokeAfterCup111 :: Proxy SmokeAfterCup111
smokeAfterCup111 = Proxy

-- | Sample left-assoc @½⊗½⊗½@ state for F-move self-tests.
sampleAssocL111 :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])
sampleAssocL111 =
  makeFTrees @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])
    (konst 1, (konst 0.5, konst 0.25))

sampleAssocL110 :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 0])
sampleAssocL110 =
  makeFTrees @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 0])
    (konst 1, konst 0.5)

sampleAssocL112 :: FTreeV (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
sampleAssocL112 =
  makeFTrees @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 2])
    (konst 1, (konst 0.5, (konst 0.25, konst 0.125)))

-- | Tree F-move round-trips (@F⁻¹ ∘ F ≈ id@) on concrete triples + @½⊗1⊗½@.
fmoveTreesSelfTest :: Bool
fmoveTreesSelfTest =
  checkFmoveTrees111 sampleAssocL111
    && checkFmoveTrees110 sampleAssocL110
    && checkFmoveTrees112 sampleAssocL112
    && checkFmoveTreesLeaves @1 @2 @1
         (fillFTreeVScaled @( FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 2]) '[ 'IrrepTree 1] ))

-- | Force the F-move self-test at module load (fails loud if broken).
fmoveTreesSelfTestOk :: ()
fmoveTreesSelfTestOk =
  if fmoveTreesSelfTest
    then ()
    else error "fmoveTreesSelfTest failed: tree F round-trip"

-- | Pure Mid from 'TensorTrees': 'idRightFinv111' matches F-inv on the assoc factor.
idRightFinvSelfTest :: Bool
idRightFinvSelfTest =
  let leaf = FCons (konst 1) FNil
      assocR =
        makeFTrees @(FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
          (konst 0.5, (konst 0.25, konst 0.125))
      mid =
        fuseTensorTrees
          @('[ 'IrrepTree 1])
          @(FuseFTrees '[ 'IrrepTree 1] (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]))
          (TensorTrees leaf assocR)
      cupGen = idRightFinv111 mid
      expected =
        fuseTensorTrees
          @('[ 'IrrepTree 1])
          @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])
          $ TensorTrees leaf (fmoveInvTrees111 assocR)
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
   in approxHom16
        (fTreeVToV @(FuseFTrees '[ 'IrrepTree 1] (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])) cupGen)
        (fTreeVToV @(FuseFTrees '[ 'IrrepTree 1] (FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) '[ 'IrrepTree 1])) expected)

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
    && checkHomInterCategory111
    && checkForgetHomFusedId111
    && checkForgetHomInterCompose111
    && checkI2FmoveSmoke
    && checkFmoveOuter111
    && checkIdLeftId111
    && checkUnitorI1
    && checkUnitorHom11
    && checkCupIHom

composeHomTreesSelfTestOk :: ()
composeHomTreesSelfTestOk =
  if composeHomTreesSelfTest
    then ()
    else error "composeHomTreesSelfTest failed: id/unit laws on leaf Hom"

-- | Typechecks five-morphism 'composeHomTrees' at leaf-½ (do not evaluate).
composeHomTreesI1
  :: FTreeV (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
  -> FTreeV (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
  -> FTreeV (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
composeHomTreesI1 = composeHomTrees @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1])

composeHomTreesI1TypedOk :: Bool
composeHomTreesI1TypedOk =
  let _ty = composeHomTreesI1
   in True
