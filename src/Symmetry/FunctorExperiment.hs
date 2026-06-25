{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ExplicitForAll #-}
-- The KnownNat solver discharges @KnownNat (m * n)@ (i.e. @KnownNat (HomBlockDim
-- m n)@) from @KnownNat m@ and @KnownNat n@. The charge-keyed @compose@
-- synthesizes blocks whose dimensions are existential (recovered from rep
-- singletons), so these products can't be solved from the literal types alone.
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Symmetry.FunctorExperiment
  ( -- * U(1) aliases (backward compatible)
    U1Rep
  , RepDim
  , U1RepList
  , HomSectorList
  , LookupMult
  , IntertwinerSectors
  , Intertwiner (..)
  , BuildIdHom
  , ApplyIntertwiner (..)
  , ToC (..)
  , -- * Group-indexed core (phase 1: @U1@ wired)
    RepListG
  , RepDimG
  , GroupSpine (..)
  , HomSectorListK
  , RepLookup (..)
  , LookupResult
  , IntertwinerG (..)
  , compose
  , mkIdHom
  , mkScalar
  , intertwinerLinear
  , repLinear
  , ActsOnRep (..)
  ) where

import Data.Complex (Complex((:+)))
import Data.Kind (Constraint, Type)
import GHC.TypeLits (Nat, KnownNat, natVal, type (+))
import qualified GHC.TypeNats
import Data.Proxy (Proxy(..))
import Data.Maybe (fromMaybe)
import Data.Singletons (sing, Sing)
import Data.Singletons.Decide (SDecide(..), Decision(..))
import Data.Type.Equality ((:~:)(..))
import Prelude hiding ((.), (<>), Functor(..))
import Control.Category.Constrained (Category(..))
import Control.Functor.Constrained (Functor(..))
import Math.LinearMap.Category hiding (Tensor)
import Math.LinearMap.Category.Instances.Deriving ()
-- Orphan instances for @C n@ (Eq, TensorSpace, …) — previously reached this
-- module transitively via @General@, now imported directly.
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static.Orphans ()
import Numeric.LinearAlgebra.Static
  (C, M, konst, create, extract, Sized(fromList), Domain(app))
import qualified Data.Vector.Storable as V
import Symmetry.Utils (Z(..), KnownZ, getZ)
import Symmetry.ChargeEq (ZEqResult(..), sZEq)
import Symmetry.Group
  ( Group (..), Rep, Irreps, RepDimG
  , GroupSpine (..), HomSectorListK, LookupMultK, IntertwinerHom
  , HomSectorListU1, LookupMultU1
  )
import Symmetry.IrrepDecide (IrrepDecide (..), IrrepEqResult (..))
import Symmetry.RepSingleton (SRep(..), KnownRep(..))
import Symmetry.HomBlock
  ( HomBlockDim, U1HomBlock(..), composeBlock, zeroBlock, blockAsMat
  )

--------------------------------------------------------------------------------
-- U(1) aliases
--------------------------------------------------------------------------------

type U1Rep = Rep U1

type RepDim :: U1Rep -> Nat
type RepDim r = RepDimG U1 r

type U1RepList :: U1Rep -> Constraint
type U1RepList = RepListG U1

type HomSectorList :: U1Rep -> U1Rep -> [(Z, Nat, Nat)]
type HomSectorList r q = HomSectorListU1 r q

type LookupMult :: Z -> U1Rep -> Maybe Nat
type LookupMult z q = LookupMultU1 z q

type Intertwiner :: U1Rep -> U1Rep -> Type
type Intertwiner = IntertwinerG U1

type IntertwinerSectors :: [(Z, Nat, Nat)] -> Type
type IntertwinerSectors hom = IntertwinerSectorsG U1 hom

type BuildIdHom :: [(Z, Nat, Nat)] -> Constraint
type BuildIdHom hom = BuildIdHomG U1 hom


--------------------------------------------------------------------------------
-- Group-indexed representation spine
--------------------------------------------------------------------------------

class RepListG (g :: Group) (rs :: Rep g)

instance RepListG U1 '[]
instance
  ( KnownNat m, KnownZ z, RepListG U1 rest
  ) => RepListG U1 ('(z, m) ': rest)

-- | Intertwiner data indexed by its hom-sector spine.
data IntertwinerSectorsG (g :: Group) (hom :: [(Irreps g, Nat, Nat)]) where
  InterNil  :: IntertwinerSectorsG g '[]
  InterCons :: forall g j m n rest.
    (KnownNat m, KnownNat n, KnownNat (HomBlockDim m n)) =>
    U1HomBlock m n
    -> IntertwinerSectorsG g rest
    -> IntertwinerSectorsG g ('(j, m, n) ': rest)

instance Show (IntertwinerSectorsG g hom) where
  show InterNil = "InterNil"
  show (InterCons block rest) =
    show block ++ " : " ++ show rest

newtype IntertwinerG (g :: Group) (r :: Rep g) (q :: Rep g) = MkIntertwiner
  { unIntertwiner :: IntertwinerSectorsG g (IntertwinerHom g r q)
  }
  deriving Show via (IntertwinerSectorsG g (IntertwinerHom g r q))

mkScalar :: Complex Double -> IntertwinerSectorsG U1 '[ '(charge, 1, 1)]
mkScalar z = InterCons (U1HomBlock (konst z) :: U1HomBlock 1 1) InterNil

class BuildIdHomG (g :: Group) (hom :: [(Irreps g, Nat, Nat)]) where
  idHom :: IntertwinerSectorsG g hom

instance BuildIdHomG U1 '[] where
  idHom = InterNil

instance
  ( KnownNat m, KnownNat (HomBlockDim m m), BuildIdHomG U1 rest
  ) => BuildIdHomG U1 ('(z, m, m) ': rest) where
  idHom = InterCons (U1HomBlock (konst 1) :: U1HomBlock m m) idHom

instance BuildIdHomG SU2 '[] where
  idHom = InterNil

instance
  ( KnownNat m, KnownNat (HomBlockDim m m), BuildIdHomG SU2 rest
  ) => BuildIdHomG SU2 ('(j, m, m) ': rest) where
  idHom = InterCons (U1HomBlock (konst 1) :: U1HomBlock m m) idHom

mkIdHom
  :: forall g a.
     ( GroupSpine g, RepLookup g, RepListG g a
     , BuildIdHomG g (IntertwinerHom g a a), KnownRep g a
     )
  => IntertwinerG g a a
mkIdHom = MkIntertwiner idHom

class (GroupSpine g, IrrepDecide g) => RepLookup g where
  sLookupMult :: Sing (j :: Irreps g) -> SRep g (q :: Rep g) -> LookupResult g j q

data family LookupResult (g :: Group) (j :: Irreps g) (q :: Rep g)

data instance LookupResult U1 (z :: Z) (q :: Rep U1) where
  Absent  :: LookupMultU1 z q ~ 'Nothing            => LookupResult U1 z q
  Present :: (LookupMultU1 z q ~ 'Just m, KnownNat m) => Proxy m -> LookupResult U1 z q

instance RepLookup U1 where
  sLookupMult _ SRepNilU1 = Absent
  sLookupMult sz (SRepCons @z2 @m sz2 rest) =
    case sIrrepEq @U1 sz sz2 of
      IrrepEqTrue  -> Present (Proxy @m)
      IrrepEqFalse -> case sLookupMult sz rest of
        Absent     -> Absent
        Present pm -> Present pm

--------------------------------------------------------------------------------
-- Label-keyed view of a @b -> c@ intertwiner (for composition)
--------------------------------------------------------------------------------

data family BCEntry (g :: Group) (c :: Rep g)

data instance BCEntry U1 (c :: Rep U1) where
  BCEntryU1 :: forall z src tgt c.
               ( KnownNat src, KnownNat tgt, LookupMultU1 z c ~ 'Just tgt )
            => Sing z -> U1HomBlock tgt src -> BCEntry U1 c

type BCEntryG g c = BCEntry g c

bcIndex
  :: SRep U1 b -> SRep U1 c
  -> IntertwinerSectors (HomSectorList b c) -> [BCEntry U1 c]
bcIndex SRepNilU1 _ InterNil = []
bcIndex (SRepCons sbz brest) sc homBC =
  case sLookupMult @U1 sbz sc of
    Absent -> bcIndex brest sc homBC
    Present (_ :: Proxy pc) -> case homBC of
      InterCons blk rest -> BCEntryU1 sbz blk : bcIndex brest sc rest

findBC
  :: forall az c m p.
     (LookupMultU1 az c ~ 'Just p, KnownNat m, KnownNat p)
  => Sing az -> [BCEntry U1 c] -> U1HomBlock p m
findBC _ [] =
  error "findBC: b->c block absent (unreachable: label present in both b and c)"
findBC saz (BCEntryU1 (sz :: Sing z) (blk :: U1HomBlock tgt src) : rest) =
  case saz %~ sz of
    Proved Refl -> case GHC.TypeNats.sameNat (Proxy @src) (Proxy @m) of
      Just Refl -> blk
      Nothing   -> error "findBC: source dim mismatch (unreachable by Schur)"
    Disproved _ -> findBC saz rest

composeGo
  :: SRep U1 a -> SRep U1 b -> SRep U1 c
  -> IntertwinerSectors (HomSectorList a b)
  -> [BCEntry U1 c]
  -> IntertwinerSectors (HomSectorList a c)
composeGo SRepNilU1 _ _ InterNil _ = InterNil
composeGo (SRepCons @az @an saz rest) sb sc ab bcIx =
  case (sLookupMult @U1 saz sb, sLookupMult @U1 saz sc) of
    (Absent, Absent) ->
      composeGo rest sb sc ab bcIx
    (Absent, Present (_ :: Proxy p)) ->
      InterCons (zeroBlock @p @an) (composeGo rest sb sc ab bcIx)
    (Present (_ :: Proxy m), Absent) ->
      case ab of
        InterCons _ abRest -> composeGo rest sb sc abRest bcIx
    (Present (_ :: Proxy m), Present (_ :: Proxy p)) ->
      case ab of
        InterCons abBlk abRest ->
          InterCons
            (composeBlock (findBC saz bcIx :: U1HomBlock p m) abBlk)
            (composeGo rest sb sc abRest bcIx)

compose
  :: forall a b c. (KnownRep U1 a, KnownRep U1 b, KnownRep U1 c)
  => Intertwiner b c -> Intertwiner a b -> Intertwiner a c
compose (MkIntertwiner bc) (MkIntertwiner ab) =
  MkIntertwiner
    (composeGo (repSing @U1 @a) (repSing @U1 @b) (repSing @U1 @c) ab
       (bcIndex (repSing @U1 @b) (repSing @U1 @c) bc))

instance Category (IntertwinerG U1) where
  type Object (IntertwinerG U1) a =
    ( RepLookup U1, KnownRep U1 a, U1RepList a, BuildIdHom (HomSectorList a a)
    , KnownNat (RepDim a)
    )
  id = mkIdHom @U1
  (.) = compose

newtype ToC (r :: U1Rep) = ToC (C (RepDim r))

zeroRep :: KnownNat (RepDim r) => ToC r
zeroRep = ToC (konst 0)

u1PhaseFactor :: forall z. KnownZ z => Double -> Complex Double
u1PhaseFactor theta =
  exp ((0 :+ 1) * (fromIntegral (getZ @z) * theta :+ 0))

class ActsOnRep (rs :: U1Rep) where
  repLinear :: Double -> (ToC rs -+> ToC rs)

instance ActsOnRep '[] where
  repLinear _ = LinearFunction (\(ToC v) -> ToC v)

instance (KnownZ z, KnownNat m) => ActsOnRep ('(z, m) ': '[]) where
  repLinear theta = LinearFunction (\(ToC v) -> ToC (u1PhaseFactor @z theta *^ v))

--------------------------------------------------------------------------------
-- Sector layout: prefix offsets in flat @C (RepDim r)@ storage
--------------------------------------------------------------------------------

natValInt :: KnownNat n => Proxy n -> Int
natValInt = fromIntegral . natVal

chargeSectorLoc :: forall (z :: Z) (q :: Rep U1). Sing z -> SRep U1 q -> Maybe (Int, Int)
chargeSectorLoc sz = go 0
  where
    go :: forall q0. Int -> SRep U1 q0 -> Maybe (Int, Int)
    go _ SRepNilU1 = Nothing
    go !off (SRepCons @z2 @m sz2 rest) =
      let mInt = natValInt (Proxy @m)
      in case sZEq sz sz2 of
           ZEqTrue  -> Just (off, mInt)
           ZEqFalse -> go (off + mInt) rest

targetChargeOffset :: forall (z :: Z) (q :: Rep U1). Sing z -> SRep U1 q -> Int
targetChargeOffset sz sq = case chargeSectorLoc @z @q sz sq of
  Just (off, _) -> off
  Nothing ->
    error "targetChargeOffset: charge absent (unreachable for hom blocks)"

takeAtOffset :: forall n total. (KnownNat n, KnownNat total) => Int -> C total -> C n
takeAtOffset off v =
  fromMaybe (error "takeAtOffset: slice out of range") $
    create (V.fromList (take (natValInt (Proxy @n)) (drop off (V.toList (extract v)))))

writeAtOffset :: forall m total. (KnownNat m, KnownNat total) => Int -> C m -> C total -> C total
writeAtOffset off block vec =
  fromMaybe (error "writeAtOffset: patch out of range") $
    create (V.fromList merged)
  where
    xs = V.toList (extract vec)
    ys = V.toList (extract block)
    m = natValInt (Proxy @m)
    merged = take off xs ++ ys ++ drop (off + m) xs

data CompiledStep where
  CompiledStep :: forall m n.
    (KnownNat m, KnownNat n) =>
    !Int -> !Int -> !(M m n) -> CompiledStep

runCompiledStep
  :: forall rdim qdim. (KnownNat rdim, KnownNat qdim)
  => CompiledStep -> C rdim -> C qdim -> C qdim
runCompiledStep (CompiledStep @m @n srcOff tgtOff mat) input output =
  writeAtOffset tgtOff (app mat (takeAtOffset @n srcOff input)) output

collectCompiledSteps
  :: forall r q hom. SRep U1 r -> SRep U1 q -> IntertwinerSectorsG U1 hom -> Int -> [CompiledStep]
collectCompiledSteps SRepNilU1 _ InterNil _ = []
collectCompiledSteps SRepNilU1 _ (InterCons _ _) _ =
  error "collectCompiledSteps: hom spine longer than source rep (unreachable)"
collectCompiledSteps (SRepCons @z @srcMult saz srest) sq hom !srcOff =
  let srcDim = natValInt (Proxy @srcMult)
  in case sLookupMult @U1 saz sq of
       Absent -> collectCompiledSteps srest sq hom (srcOff + srcDim)
       Present _ -> case hom of
         InterCons blk homRest ->
           CompiledStep srcOff (targetChargeOffset @z @q saz sq) (blockAsMat blk)
             : collectCompiledSteps srest sq homRest (srcOff + srcDim)
         InterNil ->
           error "collectCompiledSteps: hom spine exhausted early (unreachable)"
collectCompiledSteps (SRepCons _ _) _ InterNil _ =
  error "collectCompiledSteps: source rep longer than hom spine (unreachable)"

compileIntertwiner
  :: forall r q.
     ( KnownRep U1 r, KnownRep U1 q
     , KnownNat (RepDim r), KnownNat (RepDim q)
     )
  => IntertwinerSectorsG U1 (HomSectorList r q) -> C (RepDim r) -> C (RepDim q)
compileIntertwiner sectors input =
  foldl (\acc step -> runCompiledStep step input acc) (konst 0) steps
  where
    steps = collectCompiledSteps (repSing @U1 @r) (repSing @U1 @q) sectors 0

class ApplyInterGo (hom :: [(Z, Nat, Nat)]) (r :: U1Rep) (q :: U1Rep) where
  applyInterGo :: IntertwinerSectorsG U1 hom -> ToC r -> ToC q

instance
  ( KnownRep U1 r, KnownRep U1 q
  , KnownNat (RepDim r), KnownNat (RepDim q)
  , hom ~ HomSectorList r q
  ) => ApplyInterGo hom r q where
  applyInterGo sectors (ToC v) =
    ToC (compileIntertwiner @r @q sectors v)

class ApplyIntertwiner (r :: U1Rep) (q :: U1Rep) where
  applyInter
    :: IntertwinerSectorsG U1 (HomSectorList r q) -> ToC r -> ToC q

instance ApplyInterGo (HomSectorList r q) r q => ApplyIntertwiner r q where
  applyInter = applyInterGo

intertwinerLinear
  :: forall r q.
     ( KnownRep U1 r, KnownRep U1 q
     , U1RepList r, U1RepList q, ApplyIntertwiner r q
     , KnownNat (RepDim r), KnownNat (RepDim q)
     )
  => Intertwiner r q
  -> LinearFunction (Complex Double) (ToC r) (ToC q)
intertwinerLinear (MkIntertwiner sectors) =
  let steps = collectCompiledSteps (repSing @U1 @r) (repSing @U1 @q) sectors 0
      applyVec (v :: C (RepDim r)) =
        foldl (\acc step -> runCompiledStep step v acc) (konst 0) steps
  in LinearFunction (\(ToC v) -> ToC (applyVec v))

instance Functor ToC (IntertwinerG U1) (LinearFunction (Complex Double)) where
  fmap = intertwinerLinear

instance KnownNat (RepDim r) => AdditiveGroup (ToC r) where
  ToC a ^+^ ToC b = ToC (a ^+^ b)
  zeroV = ToC zeroV
  negateV (ToC v) = ToC (negateV v)

instance KnownNat (RepDim r) => VectorSpace (ToC r) where
  type Scalar (ToC r) = Complex Double
  μ *^ ToC v = ToC (μ *^ v)

instance KnownNat (RepDim r) => InnerSpace (ToC r) where
  ToC v <.> ToC w = v <.> w

instance KnownNat (RepDim r) => DimensionAware (ToC r) where
  type StaticDimension (ToC r) = StaticDimension (C (RepDim r))
  dimensionalityWitness = undefined

instance (KnownNat (RepDim r), n ~ RepDim r) => n `Dimensional` ToC r where
  knownDimensionalitySing = sing
  unsafeFromArrayWithOffset i ar =
    ToC (unsafeFromArrayWithOffset i ar)
  unsafeWriteArrayWithOffset ar i (ToC v) =
    unsafeWriteArrayWithOffset ar i v

instance KnownNat (RepDim r) => Semimanifold (ToC r) where
  type Needle (ToC r) = C (RepDim r)
  ToC _ .+~^ _ = undefined

instance KnownNat (RepDim r) => PseudoAffine (ToC r) where
  ToC _ .-~! ToC _ = undefined
  ToC _ .-~. ToC _ = undefined

instance KnownNat (RepDim r) => TensorSpace (ToC r) where
  type TensorProduct (ToC r) w = TensorProduct (C (RepDim r)) w
  scalarSpaceWitness = undefined
  linearManifoldWitness = undefined
  zeroTensor = undefined
  toFlatTensor = undefined
  fromFlatTensor = undefined
  addTensors = undefined
  subtractTensors = undefined
  scaleTensor = undefined
  negateTensor = undefined
  tensorProduct = undefined
  transposeTensor = undefined
  fmapTensor = undefined
  fzipTensorWith = undefined
  tensorUnsafeFromArrayWithOffset = undefined
  tensorUnsafeWriteArrayWithOffset = undefined
  coerceFmapTensorProduct = undefined
  wellDefinedVector (ToC v) = ToC <$> wellDefinedVector v
  wellDefinedTensor = undefined
  vectorConjugate = undefined

instance KnownNat (RepDim r) => Eq (ToC r) where
  ToC a == ToC b = a == b

instance KnownNat (RepDim r) => Show (ToC r) where
  show (ToC v) = show v

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

type Pos1       = '[ '( 'Pos 1, 1)]
type ZeroRep    = '[ '( 'Zero, 1)]
type DoublePos1 = '[ '( 'Pos 1, 2)]
type PosNeg1    = '[ '( 'Pos 1, 1), '( 'Neg 1, 1)]

type ZeroToOneHom  = HomSectorList ZeroRep Pos1
type PhaseHom      = HomSectorList Pos1 Pos1
type NegPosHom     = HomSectorList ('[ '( 'Neg 1, 1)]) Pos1
type DoublePos1Hom = HomSectorList DoublePos1 DoublePos1

zeroToOneEmpty :: (ZeroToOneHom ~ '[]) => ()
zeroToOneEmpty = ()

phaseHom :: (PhaseHom ~ '[ '( 'Pos 1, 1, 1)]) => ()
phaseHom = ()

negPosHom :: (NegPosHom ~ '[]) => ()
negPosHom = ()

doublePos1Hom :: (DoublePos1Hom ~ '[ '( 'Pos 1, 2, 2)]) => ()
doublePos1Hom = ()

zeroToOne :: Intertwiner ZeroRep Pos1
zeroToOne = MkIntertwiner InterNil

phase :: Intertwiner Pos1 Pos1
phase = MkIntertwiner (mkScalar (0 :+ 1))

phaseSquared :: Intertwiner Pos1 Pos1
phaseSquared = compose phase phase

posToEmpty :: Intertwiner Pos1 '[]
posToEmpty = MkIntertwiner InterNil

emptyToPos :: Intertwiner '[] Pos1
emptyToPos = MkIntertwiner InterNil

zeroThroughEmpty :: Intertwiner Pos1 Pos1
zeroThroughEmpty = compose emptyToPos posToEmpty

zeroThroughEmpty' ::  (ToC Pos1) -+> (ToC Pos1)
zeroThroughEmpty' = fmap zeroThroughEmpty

testZeroThroughEmpty :: ToC Pos1
testZeroThroughEmpty =
  getLinearFunction (intertwinerLinear zeroThroughEmpty) repSpace1

repSpace1 :: ToC Pos1
repSpace1 = ToC (konst 1)

repDoublePos1 :: ToC DoublePos1
repDoublePos1 = ToC (konst 1)

phaseLinear :: LinearFunction (Complex Double) (ToC Pos1) (ToC Pos1)
phaseLinear = intertwinerLinear (phase :: Intertwiner Pos1 Pos1)

testPhaseSquared :: ToC Pos1
testPhaseSquared = getLinearFunction (intertwinerLinear phaseSquared) repSpace1

phaseLinearFromAction :: LinearFunction (Complex Double)
  (ToC Pos1) (ToC Pos1)
phaseLinearFromAction = repLinear @Pos1 (pi / 2)

composedLinearAction :: LinearFunction (Complex Double)
  (ToC Pos1) (ToC Pos1)
composedLinearAction = repLinear @Pos1 1 . repLinear @Pos1 2

doublePos1Inter :: Intertwiner DoublePos1 DoublePos1
doublePos1Inter =
  MkIntertwiner (InterCons (U1HomBlock (konst 1) :: U1HomBlock 2 2) InterNil)

testDoublePos1 :: ToC DoublePos1
testDoublePos1 = getLinearFunction (intertwinerLinear doublePos1Inter) repDoublePos1

repPosNeg1 :: ToC PosNeg1
repPosNeg1 = ToC (fromList [1, 2])

negPhase :: Intertwiner PosNeg1 PosNeg1
negPhase =
  MkIntertwiner
    ( InterCons (U1HomBlock (konst 1) :: U1HomBlock 1 1)
    $ InterCons (U1HomBlock (konst (0 :+ 1)) :: U1HomBlock 1 1)
    $ InterNil
    )

testPosNegPhase :: ToC PosNeg1
testPosNegPhase = getLinearFunction (intertwinerLinear negPhase) repPosNeg1
