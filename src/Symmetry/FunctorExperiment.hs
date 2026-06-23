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
-- The KnownNat solver discharges @KnownNat (m * n)@ (i.e. @KnownNat (HomBlockDim
-- m n)@) from @KnownNat m@ and @KnownNat n@. The charge-keyed @compose@
-- synthesizes blocks whose dimensions are existential (recovered from rep
-- singletons), so these products can't be solved from the literal types alone.
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Symmetry.FunctorExperiment where

import Data.Complex (Complex((:+)))
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
import Symmetry.Utils (Z(..), KnownZ, getZ, Append)
import Symmetry.ChargeEq (ZEq, ZEqResult(..), sZEq)
import Symmetry.RepSingleton (SRep(..), KnownRep(..))
import Symmetry.HomBlock
  ( HomBlockDim, U1HomBlock(..), composeBlock, zeroBlock, blockAsMat
  )

-- | A U(1) representation as a list of @(charge, multiplicity)@ sectors.
type U1Rep = [(Z, Nat)]

-- | Total dimension of a U(1) rep (sum of sector multiplicities).
type family RepDim (r :: U1Rep) :: Nat where
  RepDim '[] = 0
  RepDim ('(z, m) ': rs) = m + RepDim rs

-- | Every sector in the list has a known charge and multiplicity.
class U1RepList (rs :: U1Rep)

instance U1RepList '[]
instance
  ( KnownNat m, KnownZ z, U1RepList rest
  ) => U1RepList ('(z, m) ': rest)

-- | Look up the multiplicity of charge @z@ in a U(1) rep, if present. Defined by
-- branching on 'ZEq' (a @Bool@) rather than a non-linear type-family pattern, so
-- the singleton recursion in 'sLookupMult' can drive its reduction.
type family LookupMult (z :: Z) (q :: U1Rep) :: Maybe Nat where
  LookupMult _ '[]                = 'Nothing
  LookupMult z ('(z2, m) ': rest) = LookupMultGo (ZEq z z2) m (LookupMult z rest)

type family LookupMultGo (eq :: Bool) (m :: Nat) (rest :: Maybe Nat) :: Maybe Nat where
  LookupMultGo 'True  m _    = 'Just m
  LookupMultGo 'False _ rest = rest

-- | One hom block @(charge, target-mult, source-mult)@, or nothing when the
-- source charge has no matching target sector. The block records the /actual/
-- charge @z@ it came from (not @Zero@): composition merges blocks by charge and
-- must synthesize zero blocks where the middle rep drops a charge, so the charge
-- has to survive in the spine.
type family MkBlock (z :: Z) (mm :: Maybe Nat) (n :: Nat) :: [(Z, Nat, Nat)] where
  MkBlock _ 'Nothing  _ = '[]
  MkBlock z ('Just m) n = '[ '( z, m, n)]

-- | Hom-space sector list for intertwiners @r -> q@: one @(z, m, n)@ block
-- per charge @z@ shared by source @r@ (multiplicity @n@) and target @q@
-- (multiplicity @m@). By Schur, only matching charges contribute. Carries the
-- block /shapes/ @m@, @n@ /and the charge @z@/ so composition can merge by
-- charge (no flattening to @m*n@, no loss of the charge label).
type family HomSectorList (r :: U1Rep) (q :: U1Rep) :: [(Z, Nat, Nat)] where
  HomSectorList '[] _              = '[]
  HomSectorList ('(z, n) ': rs) q  =
    Append (MkBlock z (LookupMult z q) n) (HomSectorList rs q)

-- | Intertwiner data indexed by its hom-sector spine. Each block records its
-- charge and @m@×@n@ shape in the spine index @('(z, m, n))@, so an endomorphism
-- block is just @InterCons@ with @m ~ n@ — there is no separate endo constructor
-- and no constructor overlap.
data IntertwinerSectors (hom :: [(Z, Nat, Nat)]) where
  InterNil  :: IntertwinerSectors '[]
  InterCons :: forall z m n rest.
    (KnownNat m, KnownNat n, KnownNat (HomBlockDim m n)) =>
    U1HomBlock m n
    -> IntertwinerSectors rest
    -> IntertwinerSectors ('(z, m, n) ': rest)

instance Show (IntertwinerSectors hom) where
  show InterNil = "InterNil"
  show (InterCons block rest) =
    show block ++ " : " ++ show rest

newtype Intertwiner (r :: U1Rep) (q :: U1Rep) = MkIntertwiner
  { unIntertwiner :: IntertwinerSectors (HomSectorList r q)
  }
  deriving Show via (IntertwinerSectors (HomSectorList r q))

mkScalar :: Complex Double -> IntertwinerSectors '[ '(charge, 1, 1)]
mkScalar z = InterCons (U1HomBlock (konst z) :: U1HomBlock 1 1) InterNil

class BuildIdHom (hom :: [(Z, Nat, Nat)]) where
  idHom :: IntertwinerSectors hom

instance BuildIdHom '[] where
  idHom = InterNil

-- | Identity recurses structurally over the endo spine; @m@ is fixed by the
-- instance head @('(z, m, m))@ rather than recovered from a flattened
-- dimension (covers @Pos1@, @DoublePos1@, …).
instance
  ( KnownNat m, KnownNat (HomBlockDim m m), BuildIdHom rest
  ) => BuildIdHom ('(z, m, m) ': rest) where
  idHom = InterCons (U1HomBlock (konst 1) :: U1HomBlock m m) idHom

mkIdHom :: forall a. (U1RepList a, BuildIdHom (HomSectorList a a)) => Intertwiner a a
mkIdHom = MkIntertwiner (idHom @(HomSectorList a a))

-- | Look up the multiplicity of charge @z@ in a rep, returning a witness that
-- ties the value-level answer to the 'LookupMult' type family — the singleton
-- counterpart of 'LookupMult'. Decided via 'sZEq' (so GHC reduces the family on
-- the resulting @'True@\/@'False@), recursing on the rep singleton 'SRep'.
data LookupResult (z :: Z) (q :: U1Rep) where
  Absent  :: (LookupMult z q ~ 'Nothing)            => LookupResult z q
  Present :: (LookupMult z q ~ 'Just m, KnownNat m) => Proxy m -> LookupResult z q

sLookupMult :: forall z q. Sing (z :: Z) -> SRep q -> LookupResult z q
sLookupMult _  SRepNil = Absent
sLookupMult sz (SRepCons @z2 @m @rs (sz2 :: Sing z2) (rest :: SRep rs)) =
  case sZEq sz sz2 of
    ZEqTrue  -> Present (Proxy @m)
    ZEqFalse -> case sLookupMult sz rest of
      Absent     -> Absent
      Present pm -> Present pm

--------------------------------------------------------------------------------
-- Charge-keyed view of a @b -> c@ intertwiner (for composition)
--------------------------------------------------------------------------------

-- | One @b -> c@ block tagged with the charge @z@ it lives at. Indexed by the
-- (fixed) target rep @c@ so it carries the proof @LookupMult z c ~ 'Just tgt@:
-- once 'findBC' matches the charge, the /target/ dimension lines up for free by
-- @'Just@-injectivity. The /source/ dimension @src@ is existential (the source
-- rep @b@ is consumed by 'bcIndex' and not in the index), so it is reconciled by
-- a 'GHC.TypeNats.sameNat' check that Schur guarantees succeeds.
data BCEntry (c :: U1Rep) where
  BCEntry :: forall z src tgt c.
             ( KnownNat src, KnownNat tgt, LookupMult z c ~ 'Just tgt )
          => Sing z -> U1HomBlock tgt src -> BCEntry c

-- | Flatten a @b -> c@ intertwiner into its charge-tagged blocks. Recurses on
-- the rep spine of @b@ in lockstep with the hom spine (both are driven by @b@),
-- so the two stay aligned with no lookups.
bcIndex
  :: forall b c. SRep b -> SRep c
  -> IntertwinerSectors (HomSectorList b c) -> [BCEntry c]
bcIndex SRepNil _ InterNil = []
bcIndex (SRepCons (sbz :: Sing bz) (brest :: SRep brest)) sc homBC =
  case sLookupMult sbz sc of
    Absent -> bcIndex brest sc homBC
    Present (_ :: Proxy pc) -> case homBC of
      InterCons blk rest -> BCEntry sbz blk : bcIndex brest sc rest

-- | Find the @b -> c@ block at charge @az@. Called only when @az@ is present in
-- both @b@ and @c@, so the block exists (the empty-list case is unreachable).
-- The target dim @p@ matches by injectivity; the source dim @m@ is recovered by
-- a 'GHC.TypeNats.sameNat' check (Schur guarantees the stored block has source
-- dimension @m@, the @b@-multiplicity of @az@).
findBC
  :: forall az c m p.
     ( LookupMult az c ~ 'Just p, KnownNat m, KnownNat p )
  => Sing az -> [BCEntry c] -> U1HomBlock p m
findBC _ [] =
  error "findBC: b->c block absent (unreachable: charge present in both b and c)"
findBC saz (BCEntry (sz :: Sing z) (blk :: U1HomBlock tgt src) : rest) =
  case saz %~ sz of
    Proved Refl -> case GHC.TypeNats.sameNat (Proxy @src) (Proxy @m) of
      Just Refl -> blk
      Nothing   -> error "findBC: source dim mismatch (unreachable by Schur)"
    Disproved _ -> findBC saz rest

--------------------------------------------------------------------------------
-- Composition: a charge-keyed merge over the source rep spine
--------------------------------------------------------------------------------

-- | The heart of 'compose'. Recurses on the source rep @a@ (which drives both
-- @HomSectorList a b@ and @HomSectorList a c@), consuming the @a -> b@ spine in
-- lockstep and looking @b -> c@ blocks up by charge in @bcIx@. At each charge:
--
--   * present in neither @b@ nor @c@: nothing to do;
--   * present in @c@ only: emit the zero block (composite through absent @b@);
--   * present in @b@ only: consume the @a -> b@ block, emit nothing (the target
--     sector is absent in @c@);
--   * present in both: compose the looked-up @b -> c@ block with the @a -> b@
--     block.
composeGo
  :: forall a b c.
     SRep a -> SRep b -> SRep c
  -> IntertwinerSectors (HomSectorList a b)
  -> [BCEntry c]
  -> IntertwinerSectors (HomSectorList a c)
composeGo SRepNil _ _ InterNil _ = InterNil
composeGo (SRepCons @az @an (saz :: Sing az) (arest :: SRep arest)) sb sc ab bcIx =
  case (sLookupMult saz sb, sLookupMult saz sc) of
    (Absent, Absent) ->
      composeGo arest sb sc ab bcIx
    (Absent, Present (_ :: Proxy p)) ->
      InterCons (zeroBlock @p @an) (composeGo arest sb sc ab bcIx)
    (Present (_ :: Proxy m), Absent) ->
      case ab of
        InterCons _ abRest -> composeGo arest sb sc abRest bcIx
    (Present (_ :: Proxy m), Present (_ :: Proxy p)) ->
      case ab of
        InterCons abBlk abRest ->
          InterCons
            (composeBlock (findBC saz bcIx :: U1HomBlock p m) abBlk)
            (composeGo arest sb sc abRest bcIx)

-- | Compose intertwiners @a -> b@ and @b -> c@ into @a -> c@, by structural
-- recursion on the rep singletons (no @unsafeCoerce@). The result is exactly
-- @Intertwiner a c@: functoriality of @Hom@ holds /by construction/, including
-- the zero-block case where the middle rep drops a shared charge.
compose
  :: forall a b c. (KnownRep a, KnownRep b, KnownRep c)
  => Intertwiner b c -> Intertwiner a b -> Intertwiner a c
compose (MkIntertwiner bc) (MkIntertwiner ab) =
  MkIntertwiner
    (composeGo (repSing @a) (repSing @b) (repSing @c) ab
       (bcIndex (repSing @b) (repSing @c) bc))

-- | Intertwiners form a category: identity is 'mkIdHom', composition is the
-- singleton-recursive 'compose'. Now that 'compose' is total (no @unsafeCoerce@),
-- this instance is honest. The object constraint bundles everything @id@ and
-- @(.)@ need: a runtime rep singleton ('KnownRep'), the per-sector witnesses
-- ('U1RepList'), and the identity-hom builder.
instance Category Intertwiner where
  type Object Intertwiner a =
    ( KnownRep a, U1RepList a, BuildIdHom (HomSectorList a a)
    , KnownNat (RepDim a)
    )
  id = mkIdHom
  (.) = compose

-- | Representation space: one flat complex vector @C (RepDim r)@.
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

-- | @(offset, multiplicity)@ of charge @z@ in @q@, walking sectors in spine order.
chargeSectorLoc :: forall (z :: Z) (q :: U1Rep). Sing z -> SRep q -> Maybe (Int, Int)
chargeSectorLoc sz = go 0
  where
    go :: forall q0. Int -> SRep q0 -> Maybe (Int, Int)
    go _ SRepNil = Nothing
    go !off (SRepCons @z2 @m (sz2 :: Sing z2) rest) =
      let mInt = natValInt (Proxy @m)
      in case sZEq @z @z2 sz sz2 of
           ZEqTrue  -> Just (off, mInt)
           ZEqFalse -> go (off + mInt) rest

-- | Prefix offset of the sector at charge @z@ in rep @q@, if present.
targetChargeOffset :: forall (z :: Z) (q :: U1Rep). Sing z -> SRep q -> Int
targetChargeOffset sz sq = case chargeSectorLoc @z @q sz sq of
  Just (off, _) -> off
  Nothing ->
    error "targetChargeOffset: charge absent (unreachable for hom blocks)"

-- | Read a length-@n@ slice from flat vector @v@ starting at byte offset @off@.
takeAtOffset :: forall n total. (KnownNat n, KnownNat total) => Int -> C total -> C n
takeAtOffset off v =
  fromMaybe (error "takeAtOffset: slice out of range") $
    create (V.fromList (take (natValInt (Proxy @n)) (drop off (V.toList (extract v)))))

-- | Write @block@ into @vec@ at offset @off@ (target sectors do not overlap).
writeAtOffset :: forall m total. (KnownNat m, KnownNat total) => Int -> C m -> C total -> C total
writeAtOffset off block vec =
  fromMaybe (error "writeAtOffset: patch out of range") $
    create (V.fromList merged)
  where
    xs = V.toList (extract vec)
    ys = V.toList (extract block)
    m = natValInt (Proxy @m)
    merged = take off xs ++ ys ++ drop (off + m) xs

-- | One compiled block: source/target offsets and a pre-built matrix.
data CompiledStep where
  CompiledStep :: forall m n.
    (KnownNat m, KnownNat n) =>
    !Int -> !Int -> !(M m n) -> CompiledStep

runCompiledStep
  :: forall rdim qdim. (KnownNat rdim, KnownNat qdim)
  => CompiledStep -> C rdim -> C qdim -> C qdim
runCompiledStep (CompiledStep @m @n srcOff tgtOff mat) input output =
  writeAtOffset tgtOff (app mat (takeAtOffset @n srcOff input)) output

-- | Walk @SRep r@ in lockstep with the hom spine (same alignment as 'bcIndex').
collectCompiledSteps
  :: forall r q hom. SRep r -> SRep q -> IntertwinerSectors hom -> Int -> [CompiledStep]
collectCompiledSteps SRepNil _ InterNil _ = []
collectCompiledSteps SRepNil _ (InterCons _ _) _ =
  error "collectCompiledSteps: hom spine longer than source rep (unreachable)"
collectCompiledSteps (SRepCons @z @srcMult (saz :: Sing z) srest) sq hom !srcOff =
  let srcDim = natValInt (Proxy @srcMult)
  in case sLookupMult saz sq of
       Absent -> collectCompiledSteps srest sq hom (srcOff + srcDim)
       Present _ -> case hom of
         InterCons blk homRest ->
           CompiledStep srcOff (targetChargeOffset @z @q saz sq) (blockAsMat blk)
             : collectCompiledSteps srest sq homRest (srcOff + srcDim)
         InterNil ->
           error "collectCompiledSteps: hom spine exhausted early (unreachable)"
collectCompiledSteps (SRepCons _ _) _ InterNil _ =
  error "collectCompiledSteps: source rep longer than hom spine (unreachable)"

-- | Compile an intertwiner to a flat @C (RepDim r) -> C (RepDim q)@ function.
-- Block matrices are built once; each application only slices and matmuls.
compileIntertwiner
  :: forall r q.
     ( KnownRep r, KnownRep q
     , KnownNat (RepDim r), KnownNat (RepDim q)
     )
  => IntertwinerSectors (HomSectorList r q) -> C (RepDim r) -> C (RepDim q)
compileIntertwiner sectors input =
  foldl (\acc step -> runCompiledStep step input acc) (konst 0) steps
  where
    steps = collectCompiledSteps (repSing @r) (repSing @q) sectors 0

-- | Apply an intertwiner to a rep vector (@hom@ fixed by @r@ and @q@).
class ApplyInterGo (hom :: [(Z, Nat, Nat)]) (r :: U1Rep) (q :: U1Rep) where
  applyInterGo :: IntertwinerSectors hom -> ToC r -> ToC q

instance
  ( KnownRep r, KnownRep q
  , KnownNat (RepDim r), KnownNat (RepDim q)
  , hom ~ HomSectorList r q
  ) => ApplyInterGo hom r q where
  applyInterGo sectors (ToC v) =
    ToC (compileIntertwiner @r @q sectors v)

-- | Apply an intertwiner to a rep vector (@hom@ fixed by @r@ and @q@).
class ApplyIntertwiner (r :: U1Rep) (q :: U1Rep) where
  applyInter
    :: IntertwinerSectors (HomSectorList r q) -> ToC r -> ToC q

instance ApplyInterGo (HomSectorList r q) r q => ApplyIntertwiner r q where
  applyInter = applyInterGo

intertwinerLinear
  :: forall r q.
     ( KnownRep r, KnownRep q
     , U1RepList r, U1RepList q, ApplyIntertwiner r q
     , KnownNat (RepDim r), KnownNat (RepDim q)
     )
  => Intertwiner r q
  -> LinearFunction (Complex Double) (ToC r) (ToC q)
intertwinerLinear (MkIntertwiner sectors) =
  let steps = collectCompiledSteps (repSing @r) (repSing @q) sectors 0
      applyVec (v :: C (RepDim r)) =
        foldl (\acc step -> runCompiledStep step v acc) (konst 0) steps
  in LinearFunction (\(ToC v) -> ToC (applyVec v))

-- | Hom functor @Rep_{U(1)} -> Vect@: objects @r |-> ToC r@, morphisms via
-- compiled block matmul ('intertwinerLinear').
instance Functor ToC Intertwiner (LinearFunction (Complex Double)) where
  fmap = intertwinerLinear

-- | @TensorSpace@ delegates to flat @C (RepDim r)@ (no @HList@).
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

-- | Composition through an /empty/ middle rep — the case the old @unsafeCoerce@
-- got wrong. @Pos1 -> '[] -> Pos1@: both legs are the (only) zero map to\/from
-- the empty rep, so the composite is the zero endomorphism of @Pos1@.
--
-- @HomSectorList Pos1 Pos1 ~ '[ '( 'Pos 1, 1, 1)]@, so the honest composite is
-- @InterCons (1×1 zero block) InterNil@ — NOT @InterNil@ (which is what
-- @unsafeCoerce@ produced, and which crashed when applied).
posToEmpty :: Intertwiner Pos1 '[]
posToEmpty = MkIntertwiner InterNil

emptyToPos :: Intertwiner '[] Pos1
emptyToPos = MkIntertwiner InterNil

zeroThroughEmpty :: Intertwiner Pos1 Pos1
zeroThroughEmpty = compose emptyToPos posToEmpty

zeroThroughEmpty' ::  (ToC Pos1) -+> (ToC Pos1)
zeroThroughEmpty' = fmap zeroThroughEmpty

-- zeroThroughEmpty'' ::  (ToC Pos1) +> (ToC Pos1)
-- zeroThroughEmpty'' = arr zeroThroughEmpty'

-- | Applying 'zeroThroughEmpty' yields the zero vector (the payoff: a genuine
-- zero block, applied without crashing).
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

-- | Block-diagonal action: @+1@ on the @Pos@ sector, @i@ on the @Neg@ sector.
testPosNegPhase :: ToC PosNeg1
testPosNegPhase = getLinearFunction (intertwinerLinear negPhase) repPosNeg1

