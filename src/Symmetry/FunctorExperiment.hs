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
{-# LANGUAGE RankNTypes #-}
-- The KnownNat solver discharges @KnownNat (m * n)@ (i.e. @KnownNat (HomBlockDim
-- m n)@) from @KnownNat m@ and @KnownNat n@. The charge-keyed @compose@
-- synthesizes blocks whose dimensions are existential (recovered from rep
-- singletons), so these products can't be solved from the literal types alone.
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Symmetry.FunctorExperiment where

import Data.Complex (Complex((:+)))
import Data.Kind (Constraint, Type)
import GHC.TypeLits (Nat, KnownNat, natVal, type (+))
import qualified GHC.TypeNats
import Data.Proxy (Proxy(..))
import Data.Maybe (fromMaybe)
import Data.Singletons (sing, Sing)
import Data.Singletons.Decide (SDecide(..), Decision(..))
import Data.Type.Equality ((:~:)(..))
import Prelude hiding ((.), Functor(..))
import qualified Prelude as P
import Control.Category.Constrained (Category(..))
import Control.Functor.Constrained (Functor(..))
import Math.LinearMap.Category hiding (Tensor)
import Math.LinearMap.Asserted (getLinearFunction, type (-+>))
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
  ( Group (..), Rep, Irreps, RepDimG, SectorDim, IrrepDim, LookupMultSU2
  , GroupSpine (..), HomSectorListK, LookupMultK, IntertwinerHom, LookupMultG
  , HomSectorListU1, HomSectorListSU2, LookupMultU1
  )
import Symmetry.IrrepDecide (IrrepDecide (..), IrrepEqResult (..))
import Symmetry.RepSingleton (SRep(..), KnownRep(..))
import Symmetry.HomBlock
  ( HasHomBlock (..), HomBlock, HomBlockDim, HomBlockDimG, CoeffBlock (..)
  , composeCoeffBlock, zeroCoeffBlock, addCoeffBlock, scaleCoeffBlock
  , negateCoeffBlock, coeffBlockAsMat, su2ExpandBlock
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

instance RepListG SU2 '[]
instance
  ( KnownNat m, KnownNat j, RepListG SU2 rest
  ) => RepListG SU2 ('(j, m) ': rest)

-- | Intertwiner data indexed by its hom-sector spine.
-- Blocks store @m × n@ scalar coefficients (Schur); @j@ appears in the
-- hom-spine index and drives @blockAsMat @g @j@ at application time.
data IntertwinerSectorsG (g :: Group) (hom :: [(Irreps g, Nat, Nat)]) where
  InterNil  :: IntertwinerSectorsG g '[]
  InterCons
    :: ( KnownNat m, KnownNat n, KnownNat (HomBlockDim m n)
       ) =>
       CoeffBlock m n
    -> IntertwinerSectorsG g rest
    -> IntertwinerSectorsG g ('(j, m, n) ': rest)

instance Show (IntertwinerSectorsG g hom) where
  show InterNil = "InterNil"
  show (InterCons block rest) =
    P.show block ++ " : " ++ P.show rest

newtype IntertwinerG (g :: Group) (r :: Rep g) (q :: Rep g) = MkIntertwiner
  { unIntertwiner :: IntertwinerSectorsG g (IntertwinerHom g r q)
  }
  deriving Show via (IntertwinerSectorsG g (IntertwinerHom g r q))

mkScalar :: Complex Double -> IntertwinerSectorsG U1 '[ '( 'Pos 1, 1, 1)]
mkScalar z = InterCons (CoeffBlock (konst z)) InterNil

class BuildIdHomG (g :: Group) (hom :: [(Irreps g, Nat, Nat)]) where
  idHom :: IntertwinerSectorsG g hom

instance BuildIdHomG U1 '[] where
  idHom = InterNil

instance
  ( KnownNat m, KnownNat (HomBlockDim m m), BuildIdHomG U1 rest
  ) => BuildIdHomG U1 ('(z, m, m) ': rest) where
  idHom = InterCons (CoeffBlock (konst 1)) idHom

instance BuildIdHomG SU2 '[] where
  idHom = InterNil

instance
  ( KnownNat m, KnownNat j, KnownNat (HomBlockDim m m), BuildIdHomG SU2 rest
  ) => BuildIdHomG SU2 ('(j, m, m) ': rest) where
  idHom = InterCons (CoeffBlock (konst 1)) idHom

mkIdHom
  :: forall g a.
     ( GroupSpine g, RepLookup g, RepListG g a
     , BuildIdHomG g (IntertwinerHom g a a), KnownRep g a
     )
  => IntertwinerG g a a
mkIdHom = MkIntertwiner idHom

class (GroupSpine g, IrrepDecide g, LookupCase g) => RepLookup g where
  sLookupMult :: Sing (j :: Irreps g) -> SRep g (q :: Rep g) -> LookupResult g j q

class LookupCase (g :: Group) where
  caseLookup
    :: LookupResult g j q
    -> a
    -> (forall m. KnownNat m => Proxy m -> a)
    -> a

lookupPair
  :: LookupCase g
  => LookupResult g j bRes -> LookupResult g j cRes
  -> a -> (forall p. KnownNat p => Proxy p -> a)
  -> (forall m. KnownNat m => Proxy m -> a)
  -> (forall m p. (KnownNat m, KnownNat p) => Proxy m -> Proxy p -> a)
  -> a
lookupPair rB rC bothAbsent absentPresent presentAbsent bothPresent =
  caseLookup rB
    (caseLookup rC bothAbsent absentPresent)
    (\pm -> caseLookup rC (presentAbsent pm) (bothPresent pm))

data family LookupResult (g :: Group) (j :: Irreps g) (q :: Rep g)

data instance LookupResult U1 (z :: Z) (q :: Rep U1) where
  Absent  :: LookupMultU1 z q ~ 'Nothing            => LookupResult U1 z q
  Present :: (LookupMultU1 z q ~ 'Just m, KnownNat m) => Proxy m -> LookupResult U1 z q

data instance LookupResult SU2 (j :: Nat) (q :: Rep SU2) where
  SU2Absent  :: LookupMultSU2 j q ~ 'Nothing            => LookupResult SU2 j q
  SU2Present :: (LookupMultSU2 j q ~ 'Just m, KnownNat m) => Proxy m -> LookupResult SU2 j q

instance LookupCase U1 where
  caseLookup Absent a _ = a
  caseLookup (Present pm) _ k = k pm

instance LookupCase SU2 where
  caseLookup SU2Absent a _ = a
  caseLookup (SU2Present pm) _ k = k pm

instance RepLookup U1 where
  sLookupMult _ SRepNilU1 = Absent
  sLookupMult sz (SRepCons @z2 @m sz2 rest) =
    case sIrrepEq @U1 sz sz2 of
      IrrepEqTrue  -> Present (Proxy @m)
      IrrepEqFalse -> case sLookupMult sz rest of
        Absent     -> Absent
        Present pm -> Present pm

instance RepLookup SU2 where
  sLookupMult _ SRepNilSU2 = SU2Absent
  sLookupMult sj (SRepConsSU2 @j2 @m sj2 rest) =
    case sIrrepEq @SU2 sj sj2 of
      IrrepEqTrue  -> SU2Present (Proxy @m)
      IrrepEqFalse -> case sLookupMult sj rest of
        SU2Absent     -> SU2Absent
        SU2Present pm -> SU2Present pm

--------------------------------------------------------------------------------
-- Label-keyed view of a @b -> c@ intertwiner (for composition)
--------------------------------------------------------------------------------

data family BCEntry (g :: Group) (c :: Rep g)

data instance BCEntry U1 (c :: Rep U1) where
  BCEntryU1 :: forall z src tgt c.
               ( KnownNat src, KnownNat tgt, LookupMultU1 z c ~ 'Just tgt )
            => Sing z -> CoeffBlock tgt src -> BCEntry U1 c

data instance BCEntry SU2 (c :: Rep SU2) where
  BCEntrySU2 :: forall j src tgt c.
                ( KnownNat src, KnownNat tgt, KnownNat j
                , LookupMultSU2 j c ~ 'Just tgt
                )
             => Sing j -> CoeffBlock tgt src -> BCEntry SU2 c

type BCEntryG g c = BCEntry g c

bcIndexU1
  :: forall b c.
     RepLookup U1
  => SRep U1 b -> SRep U1 c
  -> IntertwinerSectorsG U1 (HomSectorListU1 b c) -> [BCEntry U1 c]
bcIndexU1 SRepNilU1 _ InterNil = []
bcIndexU1 (SRepCons sbz brest) sc homBC =
  case sLookupMult @U1 sbz sc of
    Absent -> bcIndexU1 brest sc homBC
    Present (_ :: Proxy pc) -> case homBC of
      InterCons blk rest -> BCEntryU1 sbz blk : bcIndexU1 brest sc rest

bcIndexSU2
  :: forall b c.
     RepLookup SU2
  => SRep SU2 b -> SRep SU2 c
  -> IntertwinerSectorsG SU2 (HomSectorListSU2 b c) -> [BCEntry SU2 c]
bcIndexSU2 SRepNilSU2 _ InterNil = []
bcIndexSU2 (SRepConsSU2 sbj brest) sc homBC =
  case sLookupMult @SU2 sbj sc of
    SU2Absent -> bcIndexSU2 brest sc homBC
    SU2Present (_ :: Proxy pc) -> case homBC of
      InterCons blk rest -> BCEntrySU2 sbj blk : bcIndexSU2 brest sc rest

class BCIndexGo (g :: Group) where
  bcIndex
    :: RepLookup g
    => SRep g b -> SRep g c
    -> IntertwinerSectorsG g (IntertwinerHom g b c) -> [BCEntry g c]

instance BCIndexGo U1 where
  bcIndex = bcIndexU1

instance BCIndexGo SU2 where
  bcIndex = bcIndexSU2

findBCU1
  :: forall az c m p.
     (LookupMultU1 az c ~ 'Just p, KnownNat m, KnownNat p)
  => Sing az -> [BCEntry U1 c] -> CoeffBlock p m
findBCU1 _ [] =
  error "findBC: b->c block absent (unreachable: label present in both b and c)"
findBCU1 saz (BCEntryU1 (sz :: Sing z) (blk :: CoeffBlock tgt src) : rest) =
  case saz %~ sz of
    Proved Refl -> case GHC.TypeNats.sameNat (Proxy @src) (Proxy @m) of
      Just Refl -> blk
      Nothing   -> error "findBC: source dim mismatch (unreachable by Schur)"
    Disproved _ -> findBCU1 saz rest

findBCSU2
  :: forall aj c m p.
     (LookupMultSU2 aj c ~ 'Just p, KnownNat m, KnownNat p)
  => Sing aj -> [BCEntry SU2 c] -> CoeffBlock p m
findBCSU2 _ [] =
  error "findBC: b->c block absent (unreachable: label present in both b and c)"
findBCSU2 saj (BCEntrySU2 (sj :: Sing j) (blk :: CoeffBlock tgt src) : rest) =
  case saj %~ sj of
    Proved Refl -> case GHC.TypeNats.sameNat (Proxy @src) (Proxy @m) of
      Just Refl -> blk
      Nothing   -> error "findBC: source dim mismatch (unreachable by Schur)"
    Disproved _ -> findBCSU2 saj rest

composeGoU1
  :: forall a b c.
     SRep U1 a -> SRep U1 b -> SRep U1 c
  -> IntertwinerSectorsG U1 (HomSectorListU1 a b)
  -> [BCEntry U1 c]
  -> IntertwinerSectorsG U1 (HomSectorListU1 a c)
composeGoU1 SRepNilU1 _ _ InterNil _ = InterNil
composeGoU1 (SRepCons @az @an saz rest) sb sc ab bcIx =
  case (sLookupMult @U1 saz sb, sLookupMult @U1 saz sc) of
    (Absent, Absent) ->
      composeGoU1 rest sb sc ab bcIx
    (Absent, Present (_ :: Proxy p)) ->
      InterCons (zeroCoeffBlock @p @an) (composeGoU1 rest sb sc ab bcIx)
    (Present (_ :: Proxy m), Absent) ->
      case ab of
        InterCons _ abRest -> composeGoU1 rest sb sc abRest bcIx
    (Present (_ :: Proxy m), Present (_ :: Proxy p)) ->
      case ab of
        InterCons abBlk abRest ->
          InterCons
            (composeCoeffBlock (findBCU1 saz bcIx) abBlk)
            (composeGoU1 rest sb sc abRest bcIx)

composeGoSU2
  :: forall a b c.
     SRep SU2 a -> SRep SU2 b -> SRep SU2 c
  -> IntertwinerSectorsG SU2 (HomSectorListSU2 a b)
  -> [BCEntry SU2 c]
  -> IntertwinerSectorsG SU2 (HomSectorListSU2 a c)
composeGoSU2 SRepNilSU2 _ _ InterNil _ = InterNil
composeGoSU2 (SRepConsSU2 @aj @an saj rest) sb sc ab bcIx =
  case (sLookupMult @SU2 saj sb, sLookupMult @SU2 saj sc) of
    (SU2Absent, SU2Absent) ->
      composeGoSU2 rest sb sc ab bcIx
    (SU2Absent, SU2Present (_ :: Proxy p)) ->
      InterCons (zeroCoeffBlock @p @an) (composeGoSU2 rest sb sc ab bcIx)
    (SU2Present (_ :: Proxy m), SU2Absent) ->
      case ab of
        InterCons _ abRest -> composeGoSU2 rest sb sc abRest bcIx
    (SU2Present (_ :: Proxy m), SU2Present (_ :: Proxy p)) ->
      case ab of
        InterCons abBlk abRest ->
          InterCons
            (composeCoeffBlock (findBCSU2 saj bcIx) abBlk)
            (composeGoSU2 rest sb sc abRest bcIx)

class ComposeGo (g :: Group) where
  composeGo
    :: RepLookup g
    => SRep g a -> SRep g b -> SRep g c
    -> IntertwinerSectorsG g (IntertwinerHom g a b)
    -> [BCEntry g c]
    -> IntertwinerSectorsG g (IntertwinerHom g a c)

instance ComposeGo U1 where
  composeGo = composeGoU1

instance ComposeGo SU2 where
  composeGo = composeGoSU2

--------------------------------------------------------------------------------
-- Vector space on Schur-block spines (blockwise @+@ / scale)
--------------------------------------------------------------------------------

zeroInterSectors
  :: BuildIdHomG g hom => IntertwinerSectorsG g hom
zeroInterSectors = scaleInterSectors 0 idHom

addInterSectors
  :: IntertwinerSectorsG g hom
  -> IntertwinerSectorsG g hom
  -> IntertwinerSectorsG g hom
addInterSectors InterNil InterNil = InterNil
addInterSectors (InterCons a as) (InterCons b bs) =
  InterCons (addCoeffBlock a b) (addInterSectors as bs)

scaleInterSectors
  :: Complex Double
  -> IntertwinerSectorsG g hom
  -> IntertwinerSectorsG g hom
scaleInterSectors _ InterNil = InterNil
scaleInterSectors μ (InterCons a as) =
  InterCons (scaleCoeffBlock μ a) (scaleInterSectors μ as)

negateInterSectors
  :: IntertwinerSectorsG g hom -> IntertwinerSectorsG g hom
negateInterSectors InterNil = InterNil
negateInterSectors (InterCons a as) =
  InterCons (negateCoeffBlock a) (negateInterSectors as)

instance
  BuildIdHomG g (IntertwinerHom g r q)
  => AdditiveGroup (IntertwinerG g r q) where
  zeroV = MkIntertwiner zeroInterSectors
  MkIntertwiner a ^+^ MkIntertwiner b = MkIntertwiner (addInterSectors a b)
  MkIntertwiner a ^-^ MkIntertwiner b = MkIntertwiner (addInterSectors a (negateInterSectors b))
  negateV (MkIntertwiner s) = MkIntertwiner (negateInterSectors s)

instance
  BuildIdHomG g (IntertwinerHom g r q)
  => VectorSpace (IntertwinerG g r q) where
  type Scalar (IntertwinerG g r q) = Complex Double
  μ *^ MkIntertwiner s = MkIntertwiner (scaleInterSectors μ s)

composeG
  :: forall g a b c.
     ( RepLookup g, BCIndexGo g, ComposeGo g
     , KnownRep g a, KnownRep g b, KnownRep g c
     )
  => IntertwinerG g b c -> IntertwinerG g a b -> IntertwinerG g a c
composeG (MkIntertwiner bc) (MkIntertwiner ab) =
  MkIntertwiner
    (composeGo (repSing @g @a) (repSing @g @b) (repSing @g @c) ab
       (bcIndex (repSing @g @b) (repSing @g @c) bc))

compose
  :: forall a b c. (KnownRep U1 a, KnownRep U1 b, KnownRep U1 c)
  => Intertwiner b c -> Intertwiner a b -> Intertwiner a c
compose = composeG @U1

instance Category (IntertwinerG U1) where
  type Object (IntertwinerG U1) a =
    ( RepLookup U1, HasHomBlock U1, KnownRep U1 a, U1RepList a
    , BuildIdHomG U1 (HomSectorList a a), KnownNat (RepDim a)
    , BCIndexGo U1, ComposeGo U1
    )
  id = mkIdHom @U1
  (.) = compose

instance Category (IntertwinerG SU2) where
  type Object (IntertwinerG SU2) a =
    ( RepLookup SU2, HasHomBlock SU2, KnownRep SU2 a, RepListG SU2 a
    , BuildIdHomG SU2 (IntertwinerHom SU2 a a), KnownNat (RepDimG SU2 a)
    , BCIndexGo SU2, ComposeGo SU2
    )
  id = mkIdHom @SU2
  (.) = composeG @SU2

newtype ToCG (g :: Group) (r :: Rep g) = ToCG (C (RepDimG g r))

type ToCU1 = ToCG U1

pattern ToCU1 :: C (RepDim r) -> ToCG U1 r
pattern ToCU1 v = ToCG v
{-# COMPLETE ToCU1 #-}

zeroRepG :: KnownNat (RepDimG g r) => ToCG g r
zeroRepG = ToCG (konst 0)

zeroRep :: KnownNat (RepDim r) => ToCU1 r
zeroRep = zeroRepG @U1

u1PhaseFactor :: forall z. KnownZ z => Double -> Complex Double
u1PhaseFactor theta =
  exp ((0 :+ 1) * (fromIntegral (getZ @z) * theta :+ 0))

class ActsOnRep (rs :: U1Rep) where
  repLinear :: Double -> (ToCU1 rs -+> ToCU1 rs)

instance ActsOnRep '[] where
  repLinear _ = LinearFunction (\(ToCU1 v) -> ToCU1 v)

instance (KnownZ z, KnownNat m) => ActsOnRep ('(z, m) ': '[]) where
  repLinear theta = LinearFunction (\(ToCU1 v) -> ToCU1 (u1PhaseFactor @z theta *^ v))

--------------------------------------------------------------------------------
-- Sector layout: prefix offsets in flat @C (RepDim r)@ storage
--------------------------------------------------------------------------------

natValInt :: KnownNat n => Proxy n -> Int
natValInt = fromIntegral . natVal

chargeSectorLoc
  :: forall (z :: Z) (q :: Rep U1). KnownRep U1 q => Sing z -> SRep U1 q -> Maybe (Int, Int)
chargeSectorLoc = irrepSectorLoc @U1 @z

irrepSectorLoc
  :: forall g (j :: Irreps g) (q :: Rep g). KnownRep g q
  => Sing j -> SRep g q -> Maybe (Int, Int)
irrepSectorLoc sj = go 0
  where
    go :: forall q0. Int -> SRep g q0 -> Maybe (Int, Int)
    go _ SRepNilU1  = Nothing
    go _ SRepNilSU2 = Nothing
    go !off (SRepCons @j2 @m sz2 rest) =
      let stride = natValInt (Proxy @(SectorDim U1 j2 m))
      in case sIrrepEq @U1 sj sz2 of
           IrrepEqTrue  -> Just (off, stride)
           IrrepEqFalse -> go (off + stride) rest
    go !off (SRepConsSU2 @j2 @m sj2 rest) =
      let stride = natValInt (Proxy @(SectorDim SU2 j2 m))
      in case sIrrepEq @SU2 sj sj2 of
           IrrepEqTrue  -> Just (off, stride)
           IrrepEqFalse -> go (off + stride) rest

targetChargeOffset
  :: forall (z :: Z) (q :: Rep U1). KnownRep U1 q => Sing z -> SRep U1 q -> Int
targetChargeOffset sz sq = targetIrrepOffset @U1 @z sz sq

targetIrrepOffset
  :: forall g (j :: Irreps g) (q :: Rep g). KnownRep g q
  => Sing j -> SRep g q -> Int
targetIrrepOffset sj sq = case irrepSectorLoc @g @j sj sq of
  Just (off, _) -> off
  Nothing ->
    error "targetIrrepOffset: irrep absent (unreachable for hom blocks)"

takeAtOffset :: forall n total. (KnownNat n, KnownNat total) => Int -> C total -> C n
takeAtOffset off v =
  fromMaybe (error "takeAtOffset: slice out of range") $
    create (V.fromList (P.take (natValInt (Proxy @n)) (P.drop off (V.toList (extract v)))))

writeAtOffset :: forall m total. (KnownNat m, KnownNat total) => Int -> C m -> C total -> C total
writeAtOffset off block vec =
  fromMaybe (error "writeAtOffset: patch out of range") $
    create (V.fromList merged)
  where
    xs = V.toList (extract vec)
    ys = V.toList (extract block)
    m = natValInt (Proxy @m)
    merged = P.take off xs P.++ ys P.++ P.drop (off + m) xs

data CompiledStep where
  CompiledStep :: forall sm sn.
    (KnownNat sm, KnownNat sn) =>
    !Int -> !Int -> !(M sm sn) -> CompiledStep

runCompiledStep
  :: forall rdim qdim. (KnownNat rdim, KnownNat qdim)
  => CompiledStep -> C rdim -> C qdim -> C qdim
runCompiledStep (CompiledStep @sm @sn srcOff tgtOff mat) input output =
  writeAtOffset @sm tgtOff (app mat (takeAtOffset @sn srcOff input)) output

class CollectCompiledGo (g :: Group) where
  collectCompiledSteps
    :: forall r q hom.
       (RepLookup g, HasHomBlock g, KnownRep g q)
    => SRep g r -> SRep g q -> IntertwinerSectorsG g hom -> Int -> [CompiledStep]

instance CollectCompiledGo U1 where
  collectCompiledSteps SRepNilU1 _ InterNil _ = []
  collectCompiledSteps SRepNilU1 _ (InterCons _ _) _ =
    error "collectCompiledSteps: hom spine longer than source rep (unreachable)"
  collectCompiledSteps (SRepCons @z @m saz srest) sq hom !off =
    let srcDim = natValInt (Proxy @(SectorDim U1 z m))
    in case sLookupMult @U1 saz sq of
         Absent -> collectCompiledSteps srest sq hom (off + srcDim)
         Present (_ :: Proxy srcMult) -> case hom of
           InterCons blk homRest ->
             CompiledStep off (targetIrrepOffset @U1 @z saz sq) (coeffBlockAsMat blk)
               : collectCompiledSteps srest sq homRest (off + srcDim)
           InterNil ->
             error "collectCompiledSteps: hom spine exhausted early (unreachable)"
  collectCompiledSteps (SRepCons _ _) _ InterNil _ =
    error "collectCompiledSteps: source rep longer than hom spine (unreachable)"

instance CollectCompiledGo SU2 where
  collectCompiledSteps SRepNilSU2 _ InterNil _ = []
  collectCompiledSteps SRepNilSU2 _ (InterCons _ _) _ =
    error "collectCompiledSteps: hom spine longer than source rep (unreachable)"
  collectCompiledSteps (SRepConsSU2 @j @m saj srest) sq hom !off =
    let srcDim = natValInt (Proxy @(SectorDim SU2 j m))
    in case sLookupMult @SU2 saj sq of
         SU2Absent -> collectCompiledSteps srest sq hom (off + srcDim)
         SU2Present (_ :: Proxy srcMult) -> case hom of
           InterCons blk homRest ->
             CompiledStep off (targetIrrepOffset @SU2 @j saj sq) (su2ExpandBlock @j blk)
               : collectCompiledSteps srest sq homRest (off + srcDim)
           InterNil ->
             error "collectCompiledSteps: hom spine exhausted early (unreachable)"
  collectCompiledSteps (SRepConsSU2 _ _) _ InterNil _ =
    error "collectCompiledSteps: source rep longer than hom spine (unreachable)"

compileIntertwinerG
  :: forall g r q.
     ( RepLookup g, HasHomBlock g, CollectCompiledGo g
     , KnownRep g r, KnownRep g q
     , KnownNat (RepDimG g r), KnownNat (RepDimG g q)
     )
  => IntertwinerSectorsG g (IntertwinerHom g r q) -> C (RepDimG g r) -> C (RepDimG g q)
compileIntertwinerG sectors input =
  foldl (\acc step -> runCompiledStep step input acc) (konst 0) steps
  where
    steps = collectCompiledSteps (repSing @g @r) (repSing @g @q) sectors 0

compileIntertwiner
  :: forall r q.
     ( KnownRep U1 r, KnownRep U1 q
     , KnownNat (RepDim r), KnownNat (RepDim q)
     )
  => IntertwinerSectors (HomSectorList r q) -> C (RepDim r) -> C (RepDim q)
compileIntertwiner = compileIntertwinerG @U1 @r @q

class ApplyInterGoG (g :: Group) (hom :: [(Irreps g, Nat, Nat)]) (r :: Rep g) (q :: Rep g) where
  applyInterGoG :: IntertwinerSectorsG g hom -> ToCG g r -> ToCG g q

instance
  ( RepLookup g, HasHomBlock g, CollectCompiledGo g
  , KnownRep g r, KnownRep g q
  , KnownNat (RepDimG g r), KnownNat (RepDimG g q)
  , hom ~ IntertwinerHom g r q
  ) => ApplyInterGoG g hom r q where
  applyInterGoG sectors (ToCG v) =
    ToCG (compileIntertwinerG @g @r @q sectors v)

class ApplyInterGo (hom :: [(Z, Nat, Nat)]) (r :: U1Rep) (q :: U1Rep) where
  applyInterGo :: IntertwinerSectorsG U1 hom -> ToCU1 r -> ToCU1 q

instance ApplyInterGoG U1 hom r q => ApplyInterGo hom r q where
  applyInterGo = applyInterGoG @U1 @hom @r @q

class ApplyIntertwinerG (g :: Group) (r :: Rep g) (q :: Rep g) where
  applyInterG
    :: IntertwinerSectorsG g (IntertwinerHom g r q) -> ToCG g r -> ToCG g q

instance ApplyInterGoG g (IntertwinerHom g r q) r q => ApplyIntertwinerG g r q where
  applyInterG = applyInterGoG

class ApplyIntertwiner (r :: U1Rep) (q :: U1Rep) where
  applyInter
    :: IntertwinerSectorsG U1 (HomSectorList r q) -> ToCU1 r -> ToCU1 q

instance ApplyIntertwinerG U1 r q => ApplyIntertwiner r q where
  applyInter = applyInterG @U1 @r @q

intertwinerLinearG
  :: forall g r q.
     ( RepLookup g, HasHomBlock g, CollectCompiledGo g
     , KnownRep g r, KnownRep g q
     , RepListG g r, RepListG g q, ApplyIntertwinerG g r q
     , KnownNat (RepDimG g r), KnownNat (RepDimG g q)
     )
  => IntertwinerG g r q
  -> LinearFunction (Complex Double) (ToCG g r) (ToCG g q)
intertwinerLinearG (MkIntertwiner sectors) =
  let steps = collectCompiledSteps (repSing @g @r) (repSing @g @q) sectors 0
      applyVec (v :: C (RepDimG g r)) =
        foldl (\acc step -> runCompiledStep step v acc) (konst 0) steps
  in LinearFunction (\(ToCG v) -> ToCG (applyVec v))

intertwinerLinear
  :: forall r q.
     ( KnownRep U1 r, KnownRep U1 q
     , U1RepList r, U1RepList q, ApplyIntertwiner r q
     , KnownNat (RepDim r), KnownNat (RepDim q)
     )
  => Intertwiner r q
  -> LinearFunction (Complex Double) (ToCU1 r) (ToCU1 q)
intertwinerLinear = intertwinerLinearG @U1 @r @q

instance Functor (ToCG U1) (IntertwinerG U1) (LinearFunction (Complex Double)) where
  fmap = intertwinerLinearG @U1

instance Functor (ToCG SU2) (IntertwinerG SU2) (LinearFunction (Complex Double)) where
  fmap = intertwinerLinearG @SU2

instance KnownNat (RepDimG g r) => AdditiveGroup (ToCG g r) where
  ToCG a ^+^ ToCG b = ToCG (a ^+^ b)
  zeroV = ToCG zeroV
  negateV (ToCG v) = ToCG (negateV v)

instance KnownNat (RepDimG g r) => VectorSpace (ToCG g r) where
  type Scalar (ToCG g r) = Complex Double
  μ *^ ToCG v = ToCG (μ *^ v)

instance KnownNat (RepDimG g r) => InnerSpace (ToCG g r) where
  ToCG v <.> ToCG w = v <.> w

instance KnownNat (RepDimG g r) => DimensionAware (ToCG g r) where
  type StaticDimension (ToCG g r) = StaticDimension (C (RepDimG g r))
  dimensionalityWitness = undefined

instance (KnownNat (RepDimG g r), n ~ RepDimG g r) => n `Dimensional` ToCG g r where
  knownDimensionalitySing = sing
  unsafeFromArrayWithOffset i ar =
    ToCG (unsafeFromArrayWithOffset i ar)
  unsafeWriteArrayWithOffset ar i (ToCG v) =
    unsafeWriteArrayWithOffset ar i v

instance KnownNat (RepDimG g r) => Semimanifold (ToCG g r) where
  type Needle (ToCG g r) = C (RepDimG g r)
  ToCG _ .+~^ _ = undefined

instance KnownNat (RepDimG g r) => PseudoAffine (ToCG g r) where
  ToCG _ .-~! ToCG _ = undefined
  ToCG _ .-~. ToCG _ = undefined

instance KnownNat (RepDimG g r) => TensorSpace (ToCG g r) where
  type TensorProduct (ToCG g r) w = TensorProduct (C (RepDimG g r)) w
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
  wellDefinedVector (ToCG v) = ToCG <$> wellDefinedVector v
  wellDefinedTensor = undefined
  vectorConjugate = undefined

instance KnownNat (RepDimG g r) => Eq (ToCG g r) where
  ToCG a == ToCG b = a == b

instance KnownNat (RepDimG g r) => Show (ToCG g r) where
  show (ToCG v) = show v

--------------------------------------------------------------------------------
-- Flatten @ToCG g r@ to bare @C (RepDimG g r)@
--
-- @ToCG@ already wraps flat storage; these helpers peel the tag off linear maps.
--------------------------------------------------------------------------------

unRepVec :: ToCG g r -> C (RepDimG g r)
unRepVec (ToCG v) = v

-- | Pull a @ToCG@-linear map down to @C (RepDimG g r) -+> C (RepDimG g q)@.
flatRepLinear
  :: forall g r q.
     ( KnownNat (RepDimG g r), KnownNat (RepDimG g q) )
  => LinearFunction (Complex Double) (ToCG g r) (ToCG g q)
  -> LinearFunction (Complex Double) (C (RepDimG g r)) (C (RepDimG g q))
flatRepLinear (LinearFunction f) =
  LinearFunction (\v -> unRepVec (f (ToCG v)))

-- | Compile an intertwiner directly on flat @C@ storage.
forgetLinearG
  :: forall g r q.
     ( RepLookup g, HasHomBlock g, CollectCompiledGo g
     , KnownRep g r, KnownRep g q
     , RepListG g r, RepListG g q, ApplyIntertwinerG g r q
     , KnownNat (RepDimG g r), KnownNat (RepDimG g q)
     )
  => IntertwinerG g r q
  -> LinearFunction (Complex Double) (C (RepDimG g r)) (C (RepDimG g q))
forgetLinearG = flatRepLinear . intertwinerLinearG

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

zeroThroughEmpty' ::  (ToCU1 Pos1) -+> (ToCU1 Pos1)
zeroThroughEmpty' = fmap zeroThroughEmpty

testZeroThroughEmpty :: ToCU1 Pos1
testZeroThroughEmpty =
  getLinearFunction (intertwinerLinear zeroThroughEmpty) repSpace1

repSpace1 :: ToCU1 Pos1
repSpace1 = ToCU1 (konst 1)

repDoublePos1 :: ToCU1 DoublePos1
repDoublePos1 = ToCU1 (konst 1)

phaseLinear :: LinearFunction (Complex Double) (ToCU1 Pos1) (ToCU1 Pos1)
phaseLinear = intertwinerLinear (phase :: Intertwiner Pos1 Pos1)

testPhaseSquared :: ToCU1 Pos1
testPhaseSquared = getLinearFunction (intertwinerLinear phaseSquared) repSpace1

phaseLinearFromAction :: LinearFunction (Complex Double)
  (ToCU1 Pos1) (ToCU1 Pos1)
phaseLinearFromAction = repLinear @Pos1 (pi / 2)

composedLinearAction :: LinearFunction (Complex Double)
  (ToCU1 Pos1) (ToCU1 Pos1)
composedLinearAction = repLinear @Pos1 1 . repLinear @Pos1 2

doublePos1Inter :: Intertwiner DoublePos1 DoublePos1
doublePos1Inter =
  MkIntertwiner (InterCons (CoeffBlock (konst 1)) InterNil)

testDoublePos1 :: ToCU1 DoublePos1
testDoublePos1 = getLinearFunction (intertwinerLinear doublePos1Inter) repDoublePos1

repPosNeg1 :: ToCU1 PosNeg1
repPosNeg1 = ToCU1 (fromList [1, 2])

negPhase :: Intertwiner PosNeg1 PosNeg1
negPhase =
  MkIntertwiner
    ( InterCons (CoeffBlock (konst 1))
    $ InterCons (CoeffBlock (konst (0 :+ 1)))
    $ InterNil
    )

testPosNegPhase :: ToCU1 PosNeg1
testPosNegPhase = getLinearFunction (intertwinerLinear negPhase) repPosNeg1

--------------------------------------------------------------------------------
-- SU(2) examples (j labels are twice the physical spin)
--------------------------------------------------------------------------------

type SU2Rep = Rep SU2
type SpinHalf = '[ '(1, 1)]   -- spin-½, dim 2
type SpinOne  = '[ '(2, 1)]   -- spin-1, dim 3

type SpinHalfHom = IntertwinerHom SU2 SpinHalf SpinHalf

spinHalfId :: IntertwinerG SU2 SpinHalf SpinHalf
spinHalfId = mkIdHom @SU2

repSpinHalf :: ToCG SU2 SpinHalf
repSpinHalf = ToCG (konst 1)

testSpinHalfId :: ToCG SU2 SpinHalf
testSpinHalfId = getLinearFunction (intertwinerLinearG @SU2 spinHalfId) repSpinHalf

spinHalfScale :: IntertwinerG SU2 '[ '(1, 1)] '[ '(2, 1)]
spinHalfScale =
  MkIntertwiner InterNil
-- (InterCons (CoeffBlock (konst 2)) InterNil)
spinHalfScaleLM :: ToCG SU2 '[ '(1, 1)] -+> ToCG SU2 '[ '(2, 1)]
spinHalfScaleLM = fmap spinHalfScale

-- | Same map on bare @C 2@ (drop the @ToCG@ tag).
spinHalfScaleFlat :: C 2 -+> C 3
spinHalfScaleFlat = forgetLinearG spinHalfScale

testSpinHalfScale :: ToCG SU2 '[ '(2, 1)]
testSpinHalfScale =
  getLinearFunction (intertwinerLinearG @SU2 spinHalfScale) repSpinHalf

testSpinHalfScale' :: C (RepDimG SU2 '[ '(2, 1)])
testSpinHalfScale' = getLinearFunction spinHalfScaleFlat (konst 2)


fancyExample :: IntertwinerG SU2 '[ '(1, 1), '(3, 2)] '[ '(3, 3), '(1, 1)]
fancyExample =
  MkIntertwiner
    ( InterCons (CoeffBlock (konst 1)) (InterCons undefined InterNil)
    )