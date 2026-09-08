{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | F-moves and FuseRep naturality on genealogy spines.
--
-- Production 'fuseMapRight'/'fuseMapLeft' use expanded spine-order flats
-- (no coalesced 'ForgetRep'). Atom F-moves still route through Fusion.SU2
-- collect/scatter flats as an oracle — typed per-channel @C (d+1)@ F is a
-- follow-on (Phase 4).
module Experiments.Symbolic.FMove
  ( CanFmoveTrees (..)
  , CanFmoveOuterHom (..)
  , fmoveTreesAtoms
  , fmoveInvTreesAtoms
  , fmoveTreesHomLeft
  , fmoveInvTreesHomLeft
  , fmoveOuterLeafHom
  , fmoveInvOuterLeafHom
  , TensorTrees (..)
  , fuseTensorTrees
  , fuseMapRight
  , fuseMapLeft
  , repVToExpandedFlat
  , expandedFlatToRepV
  ) where

import Data.Complex (Complex ((:+)))
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
import qualified Data.Vector.Storable as VS
import Experiments.Fusion.SU2
  ( allowedE
  , allowedF
  , fmoveAtomsFlat
  , leftSectors
  , packAtomsFlat
  , rightSectors
  , unpackAtomsFlat
  )
import Experiments.Symbolic.Expr
import Experiments.Symbolic.RepV
import Experiments.Symbolic.Singletons
import Experiments.Symbolic.TypeLevel
import GHC.TypeLits (KnownNat, natVal)
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Symmetry.CG.SU2
  ( fuseMapLeftFlatSectors
  , fuseMapRightFlatSectors
  )

-- | 3-factor F-move on fusion-tree spines: @(x⊗y)⊗z → x⊗(y⊗z)@.
--
-- Bare triples: polymorphic instance via 'fmoveTreesBares' → 'fmoveTreesAtoms'
-- (@FuseRep (FuseRep a b) c → FuseRep a (FuseRep b c)@). Outer Hom F
-- (@z = FuseRep b c@) cannot put that type family in an instance head — use
-- 'CanFmoveOuterHom' instead.
class CanFmoveTrees (a :: Rep) (b :: Rep) (c :: Rep) where
  fmoveTrees
    :: RepV (FuseRep (FuseRep a b) c)
    -> RepV (FuseRep a (FuseRep b c))
  fmoveInvTrees
    :: RepV (FuseRep a (FuseRep b c))
    -> RepV (FuseRep (FuseRep a b) c)

-- | Outer Hom F for leaf objects: @(a⊗b) ⊗ Hom(b,c) → a ⊗ (b ⊗ Hom(b,c))@.
-- Instance head is three bare spines (no 'FuseRep' in the head).
class CanFmoveOuterHom (a :: Rep) (b :: Rep) (c :: Rep) where
  fmoveOuterHom
    :: RepV (FuseRep (FuseRep a b) (FuseRep b c))
    -> RepV (FuseRep a (FuseRep b (FuseRep b c)))
  fmoveInvOuterHom
    :: RepV (FuseRep a (FuseRep b (FuseRep b c)))
    -> RepV (FuseRep (FuseRep a b) (FuseRep b c))

-- | Collect left-assoc channels from @((a_i⊗b_j)_e ⊗ c_k)_d@.
--
-- Keys include roots of the embedded factors so multi-tree spines
-- (e.g. Hom⊗leaf⊗leaf) do not collide on @(d,e)@ alone.
collectAssocLChannel
  :: SRep ts
  -> RepV ts
  -> [(Int, Int, Int, Int, Int, VS.Vector (Complex Double))]
collectAssocLChannel SRepNil RNil = []
collectAssocLChannel (SRepCons t rest) (RCons v rs) =
  case t of
    SFrom @d left right ->
      case left of
        SFrom @_ a_i b_j ->
          ( fromIntegral (natVal (Proxy @d))
          , rootLab left
          , rootLab a_i
          , rootLab b_j
          , rootLab right
          , toArray v
          )
            : collectAssocLChannel rest rs
        SBare {} ->
          error "collectAssocLChannel: expected From intermediate (not left-assoc FuseRep?)"
        SBare {} ->
          error "collectAssocLChannel: leaf in association spine (not left-assoc FuseRep?)"

-- | Collect right-assoc channels from @(a_i ⊗ (b_j⊗c_k)_f)_d@.
collectAssocRChannel
  :: SRep ts
  -> RepV ts
  -> [(Int, Int, Int, Int, Int, VS.Vector (Complex Double))]
collectAssocRChannel SRepNil RNil = []
collectAssocRChannel (SRepCons t rest) (RCons v rs) =
  case t of
    SFrom @d left right ->
      case right of
        SFrom @_ b_j c_k ->
          ( fromIntegral (natVal (Proxy @d))
          , rootLab right
          , rootLab left
          , rootLab b_j
          , rootLab c_k
          , toArray v
          )
            : collectAssocRChannel rest rs
        SBare {} ->
          error "collectAssocRChannel: expected From intermediate (not right-assoc FuseRep?)"
        SBare {} ->
          error "collectAssocRChannel: leaf in association spine (not right-assoc FuseRep?)"

-- | @(d, mid, ra, rb, rc)@ channel map → AssocL spine.
scatterAssocLChannel
  :: SRep ts
  -> Map.Map (Int, Int, Int, Int, Int) (VS.Vector (Complex Double))
  -> RepV ts
scatterAssocLChannel SRepNil _ = RNil
scatterAssocLChannel (SRepCons (t :: SIrrepTree u) rest) m =
  case t of
    SFrom @d left right ->
      case left of
        SFrom @_ a_i b_j ->
          let key =
                ( fromIntegral (natVal (Proxy @d))
                , rootLab left
                , rootLab a_i
                , rootLab b_j
                , rootLab right
                )
           in RCons @u
                (unsafeFromArray (Map.findWithDefault (zeroLike5 key m) key m))
                (scatterAssocLChannel rest m)
        SBare {} ->
          error "scatterAssocLChannel: expected From intermediate"
    SBare {} ->
      error "scatterAssocLChannel: leaf in association spine"

scatterAssocRChannel
  :: SRep ts
  -> Map.Map (Int, Int, Int, Int, Int) (VS.Vector (Complex Double))
  -> RepV ts
scatterAssocRChannel SRepNil _ = RNil
scatterAssocRChannel (SRepCons (t :: SIrrepTree u) rest) m =
  case t of
    SFrom @d left right ->
      case right of
        SFrom @_ b_j c_k ->
          let key =
                ( fromIntegral (natVal (Proxy @d))
                , rootLab right
                , rootLab left
                , rootLab b_j
                , rootLab c_k
                )
           in RCons @u
                (unsafeFromArray (Map.findWithDefault (zeroLike5 key m) key m))
                (scatterAssocRChannel rest m)
        SBare {} ->
          error "scatterAssocRChannel: expected From intermediate"
    SBare {} ->
      error "scatterAssocRChannel: leaf in association spine"

-- | Zero vector for a missing 5-key channel (same @d@-block length as peers).
zeroLike5
  :: (Int, Int, Int, Int, Int)
  -> Map.Map (Int, Int, Int, Int, Int) (VS.Vector (Complex Double))
  -> VS.Vector (Complex Double)
zeroLike5 (d, _, _, _, _) m =
  case [v | ((d', _, _, _, _), v) <- Map.toList m, d' == d] of
    (v : _) -> VS.replicate (VS.length v) 0
    [] -> VS.replicate (d + 1) 0

-- | 3-factor F-move: @FuseRep (FuseRep a b) c → FuseRep a (FuseRep b c)@.
--
-- 'FuseRep' distributes into channels @((a_i⊗b_j)_e ⊗ c_k)_d@. For each
-- distinct root triple @(r(a_i),r(b_j),r(c_k))@ apply dense Racah
-- @F^{ra rb rc}@, keeping genealogy in the channel key.
fmoveTreesAtoms
  :: forall a b c
   . ( KnownRep (FuseRep (FuseRep a b) c)
     , KnownRep (FuseRep a (FuseRep b c))
     )
  => RepV (FuseRep (FuseRep a b) c)
  -> RepV (FuseRep a (FuseRep b c))
fmoveTreesAtoms tv =
  let chans = collectAssocLChannel (repSing @(FuseRep (FuseRep a b) c)) tv
      triples =
        Map.keys $
          Map.fromList [((ra, rb, rc), ()) | (_, _, ra, rb, rc, _) <- chans]
      out =
        concatMap
          ( \(ra, rb, rc) ->
              let chH =
                    [ (d, e, v)
                    | (d, e, ra', rb', rc', v) <- chans
                    , ra' == ra
                    , rb' == rb
                    , rc' == rc
                    ]
                  buf =
                    packAtomsFlat
                      (leftSectors ra rb rc)
                      (\d -> allowedE ra rb rc d)
                      chH
                  buf' = fmoveAtomsFlat False ra rb rc buf
                  unpacked =
                    unpackAtomsFlat
                      (rightSectors ra rb rc)
                      (\d -> allowedF ra rb rc d)
                      buf'
               in [(d, f, ra, rb, rc, v) | (d, f, v) <- unpacked]
          )
          triples
   in scatterAssocRChannel
        (repSing @(FuseRep a (FuseRep b c)))
        (Map.fromList [((d, f, ra, rb, rc), v) | (d, f, ra, rb, rc, v) <- out])

fmoveInvTreesAtoms
  :: forall a b c
   . ( KnownRep (FuseRep (FuseRep a b) c)
     , KnownRep (FuseRep a (FuseRep b c))
     )
  => RepV (FuseRep a (FuseRep b c))
  -> RepV (FuseRep (FuseRep a b) c)
fmoveInvTreesAtoms tv =
  let chans = collectAssocRChannel (repSing @(FuseRep a (FuseRep b c))) tv
      triples =
        Map.keys $
          Map.fromList [((ra, rb, rc), ()) | (_, _, ra, rb, rc, _) <- chans]
      out =
        concatMap
          ( \(ra, rb, rc) ->
              let chH =
                    [ (d, f, v)
                    | (d, f, ra', rb', rc', v) <- chans
                    , ra' == ra
                    , rb' == rb
                    , rc' == rc
                    ]
                  buf =
                    packAtomsFlat
                      (rightSectors ra rb rc)
                      (\d -> allowedF ra rb rc d)
                      chH
                  buf' = fmoveAtomsFlat True ra rb rc buf
                  unpacked =
                    unpackAtomsFlat
                      (leftSectors ra rb rc)
                      (\d -> allowedE ra rb rc d)
                      buf'
               in [(d, e, ra, rb, rc, v) | (d, e, v) <- unpacked]
          )
          triples
   in scatterAssocLChannel
        (repSing @(FuseRep (FuseRep a b) c))
        (Map.fromList [((d, e, ra, rb, rc), v) | (d, e, ra, rb, rc, v) <- out])

-- | Atom-leaf triple F-move from type-level @2j@.
fmoveTreesBares
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) '[ 'Bare jc] )
     , KnownRep ( FuseRep '[ 'Bare ja] (FuseRep '[ 'Bare jb] '[ 'Bare jc]) )
     )
  => RepV ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) '[ 'Bare jc] )
  -> RepV ( FuseRep '[ 'Bare ja] (FuseRep '[ 'Bare jb] '[ 'Bare jc]) )
fmoveTreesBares =
  fmoveTreesAtoms @('[ 'Bare ja]) @('[ 'Bare jb]) @('[ 'Bare jc])

fmoveInvTreesLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) '[ 'Bare jc] )
     , KnownRep ( FuseRep '[ 'Bare ja] (FuseRep '[ 'Bare jb] '[ 'Bare jc]) )
     )
  => RepV ( FuseRep '[ 'Bare ja] (FuseRep '[ 'Bare jb] '[ 'Bare jc]) )
  -> RepV ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) '[ 'Bare jc] )
fmoveInvTreesLeaves =
  fmoveInvTreesAtoms @('[ 'Bare ja]) @('[ 'Bare jb]) @('[ 'Bare jc])

-- | Outer Hom F for three bare labels (Hom = 'FuseRep' of the last two).
fmoveOuterHomLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep
         ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) (FuseRep '[ 'Bare jb] '[ 'Bare jc])
         )
     , KnownRep
         ( FuseRep '[ 'Bare ja] (FuseRep '[ 'Bare jb] (FuseRep '[ 'Bare jb] '[ 'Bare jc]))
         )
     )
  => RepV
       ( FuseRep
           (FuseRep '[ 'Bare ja] '[ 'Bare jb])
           (FuseRep '[ 'Bare jb] '[ 'Bare jc])
       )
  -> RepV
       ( FuseRep
           '[ 'Bare ja]
           (FuseRep '[ 'Bare jb] (FuseRep '[ 'Bare jb] '[ 'Bare jc]))
       )
fmoveOuterHomLeaves =
  fmoveOuterLeafHom @ja @jb
    @( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) (FuseRep '[ 'Bare jb] '[ 'Bare jc])
     )
    @( FuseRep '[ 'Bare ja] (FuseRep '[ 'Bare jb] (FuseRep '[ 'Bare jb] '[ 'Bare jc]))
     )

fmoveInvOuterHomLeaves
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep
         ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) (FuseRep '[ 'Bare jb] '[ 'Bare jc])
         )
     , KnownRep
         ( FuseRep '[ 'Bare ja] (FuseRep '[ 'Bare jb] (FuseRep '[ 'Bare jb] '[ 'Bare jc]))
         )
     )
  => RepV
       ( FuseRep
           '[ 'Bare ja]
           (FuseRep '[ 'Bare jb] (FuseRep '[ 'Bare jb] '[ 'Bare jc]))
       )
  -> RepV
       ( FuseRep
           (FuseRep '[ 'Bare ja] '[ 'Bare jb])
           (FuseRep '[ 'Bare jb] '[ 'Bare jc])
       )
fmoveInvOuterHomLeaves =
  fmoveInvOuterLeafHom @ja @jb
    @( FuseRep '[ 'Bare ja] (FuseRep '[ 'Bare jb] (FuseRep '[ 'Bare jb] '[ 'Bare jc]))
     )
    @( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) (FuseRep '[ 'Bare jb] '[ 'Bare jc])
     )

-- | Any three atom leaves: F via 'fmoveTreesBares' (no per-triple FlatXXX).
instance
  ( KnownNat ja
  , KnownNat jb
  , KnownNat jc
  , KnownRep ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) '[ 'Bare jc] )
  , KnownRep ( FuseRep '[ 'Bare ja] (FuseRep '[ 'Bare jb] '[ 'Bare jc]) )
  ) =>
  CanFmoveTrees '[ 'Bare ja] '[ 'Bare jb] '[ 'Bare jc]
  where
  fmoveTrees = fmoveTreesBares @ja @jb @jc
  fmoveInvTrees = fmoveInvTreesLeaves @ja @jb @jc

-- | Bare outer Hom F: any three bare labels (Hom = 'FuseRep' of last two).
instance
  ( KnownNat ja
  , KnownNat jb
  , KnownNat jc
  , KnownRep
      ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare jb]) (FuseRep '[ 'Bare jb] '[ 'Bare jc])
      )
  , KnownRep
      ( FuseRep '[ 'Bare ja] (FuseRep '[ 'Bare jb] (FuseRep '[ 'Bare jb] '[ 'Bare jc]))
      )
  ) =>
  CanFmoveOuterHom '[ 'Bare ja] '[ 'Bare jb] '[ 'Bare jc]
  where
  fmoveOuterHom = fmoveOuterHomLeaves @ja @jb @jc
  fmoveInvOuterHom = fmoveInvOuterHomLeaves @ja @jb @jc

-- | Nested unfused @a ⊗ q@ before CG (layout for Fuse-right naturality).
data TensorTrees (a :: Rep) (q :: Rep) where
  TensorTrees :: RepV a -> RepV q -> TensorTrees a q

fuseTensorTrees
  :: forall a q
   . ( KnownRep a
     , KnownRep q
     , FuseRepTermC a q
     )
  => TensorTrees a q
  -> RepV (FuseRep a q)
fuseTensorTrees (TensorTrees a q) = fuseRepTerm @a @q a q

-- | Hom-left nested F: left factor @FuseRep '[ 'Bare ja] '[ 'Bare ja]@.
-- Plain functions (Nat-indexed so 'FuseRep' stays out of instance heads).
fmoveTreesHomLeft
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep
         ( FuseRep (FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare ja]) '[ 'Bare jb]) '[ 'Bare jc]
         )
     , KnownRep
         ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare ja]) (FuseRep '[ 'Bare jb] '[ 'Bare jc])
         )
     )
  => RepV
       ( FuseRep (FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare ja]) '[ 'Bare jb]) '[ 'Bare jc]
       )
  -> RepV
       ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare ja]) (FuseRep '[ 'Bare jb] '[ 'Bare jc])
       )
fmoveTreesHomLeft =
  fmoveTreesAtoms
    @(FuseRep '[ 'Bare ja] '[ 'Bare ja])
    @('[ 'Bare jb])
    @('[ 'Bare jc])

fmoveInvTreesHomLeft
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownRep
         ( FuseRep (FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare ja]) '[ 'Bare jb]) '[ 'Bare jc]
         )
     , KnownRep
         ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare ja]) (FuseRep '[ 'Bare jb] '[ 'Bare jc])
         )
     )
  => RepV
       ( FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare ja]) (FuseRep '[ 'Bare jb] '[ 'Bare jc])
       )
  -> RepV
       ( FuseRep (FuseRep (FuseRep '[ 'Bare ja] '[ 'Bare ja]) '[ 'Bare jb]) '[ 'Bare jc]
       )
fmoveInvTreesHomLeft =
  fmoveInvTreesAtoms
    @(FuseRep '[ 'Bare ja] '[ 'Bare ja])
    @('[ 'Bare jb])
    @('[ 'Bare jc])

-- | Collect left-assoc Hom channels @(d, e, h, irrep)@ from
-- @((a⊗b)_e ⊗ Hom_h)_d@. Key includes Hom root @h@ so F cannot reshuffle
-- distinct Hom genealogies that share the same outer root.
collectAssocLHom
  :: SRep ts
  -> RepV ts
  -> [(Int, Int, Int, VS.Vector (Complex Double))]
collectAssocLHom SRepNil RNil = []
collectAssocLHom (SRepCons t rest) (RCons v rs) =
  case t of
    SFrom @d left right ->
      case left of
        SFrom {} ->
          ( fromIntegral (natVal (Proxy @d))
          , rootLab left
          , rootLab right
          , toArray v
          )
            : collectAssocLHom rest rs
        SBare {} ->
          error "collectAssocLHom: expected From intermediate"
    SBare {} ->
      error "collectAssocLHom: leaf in association spine"

-- | Collect right-assoc Hom channels @(d, f, h, irrep)@ from
-- @(a ⊗ (b ⊗ Hom_h)_f)_d@.
collectAssocRHom
  :: SRep ts
  -> RepV ts
  -> [(Int, Int, Int, VS.Vector (Complex Double))]
collectAssocRHom SRepNil RNil = []
collectAssocRHom (SRepCons t rest) (RCons v rs) =
  case t of
    SFrom @d _left right ->
      case right of
        SFrom @_ _ midHom ->
          ( fromIntegral (natVal (Proxy @d))
          , rootLab right
          , rootLab midHom
          , toArray v
          )
            : collectAssocRHom rest rs
        SBare {} ->
          error "collectAssocRHom: expected From intermediate"
    SBare {} ->
      error "collectAssocRHom: leaf in association spine"

scatterAssocLHom
  :: SRep ts
  -> Map.Map (Int, Int, Int) (VS.Vector (Complex Double))
  -> RepV ts
scatterAssocLHom SRepNil _ = RNil
scatterAssocLHom (SRepCons (t :: SIrrepTree u) rest) m =
  case t of
    SFrom @d left right ->
      let key =
            ( fromIntegral (natVal (Proxy @d))
            , rootLab left
            , rootLab right
            )
       in RCons @u
            (unsafeFromArray (Map.findWithDefault (zeroLike key m) key m))
            (scatterAssocLHom rest m)
    SBare {} ->
      error "scatterAssocLHom: leaf in association spine"

scatterAssocRHom
  :: SRep ts
  -> Map.Map (Int, Int, Int) (VS.Vector (Complex Double))
  -> RepV ts
scatterAssocRHom SRepNil _ = RNil
scatterAssocRHom (SRepCons (t :: SIrrepTree u) rest) m =
  case t of
    SFrom @d _left right ->
      case right of
        SFrom @_ _ midHom ->
          let key =
                ( fromIntegral (natVal (Proxy @d))
                , rootLab right
                , rootLab midHom
                )
           in RCons @u
                (unsafeFromArray (Map.findWithDefault (zeroLike key m) key m))
                (scatterAssocRHom rest m)
        SBare {} ->
          error "scatterAssocRHom: expected From intermediate"
    SBare {} ->
      error "scatterAssocRHom: leaf in association spine"

-- | Zero vector matching any sample in @m@ (same irrep dim as that @d@ block).
zeroLike
  :: (Int, Int, Int)
  -> Map.Map (Int, Int, Int) (VS.Vector (Complex Double))
  -> VS.Vector (Complex Double)
zeroLike (d, _, _) m =
  case [v | ((d', _, _), v) <- Map.toList m, d' == d] of
    (v : _) -> VS.replicate (VS.length v) 0
    [] -> VS.replicate (d + 1) 0

-- | Outer F for @Fuse(Fuse(a,b), Hom) → Fuse(a, Fuse(b, Hom))@ with Hom a
-- list of leaf–leaf channels. Runs atom F per Hom root @h@ so genealogy of
-- the Hom factor is preserved (forgetful flat F reshuffles same-root copies).
fmoveOuterLeafHom
  :: forall ja jb ls rs
   . ( KnownNat ja
     , KnownNat jb
     , KnownRep ls
     , KnownRep rs
     )
  => RepV ls
  -> RepV rs
fmoveOuterLeafHom tv =
  let a = fromIntegral (natVal (Proxy @ja)) :: Int
      b = fromIntegral (natVal (Proxy @jb)) :: Int
      chans = collectAssocLHom (repSing @ls) tv
      hs = Map.keys $ Map.fromList [(h, ()) | (_, _, h, _) <- chans]
      out =
        concatMap
          ( \h ->
              let chH = [(d, e, v) | (d, e, h', v) <- chans, h' == h]
                  buf =
                    packAtomsFlat
                      (leftSectors a b h)
                      (\d -> allowedE a b h d)
                      chH
                  buf' = fmoveAtomsFlat False a b h buf
                  unpacked =
                    unpackAtomsFlat
                      (rightSectors a b h)
                      (\d -> allowedF a b h d)
                      buf'
               in [(d, f, h, v) | (d, f, v) <- unpacked]
          )
          hs
   in scatterAssocRHom
        (repSing @rs)
        (Map.fromList [((d, f, h), v) | (d, f, h, v) <- out])

fmoveInvOuterLeafHom
  :: forall ja jb rs ls
   . ( KnownNat ja
     , KnownNat jb
     , KnownRep rs
     , KnownRep ls
     )
  => RepV rs
  -> RepV ls
fmoveInvOuterLeafHom tv =
  let a = fromIntegral (natVal (Proxy @ja)) :: Int
      b = fromIntegral (natVal (Proxy @jb)) :: Int
      chans = collectAssocRHom (repSing @rs) tv
      hs = Map.keys $ Map.fromList [(h, ()) | (_, _, h, _) <- chans]
      out =
        concatMap
          ( \h ->
              let chH = [(d, f, v) | (d, f, h', v) <- chans, h' == h]
                  buf =
                    packAtomsFlat
                      (rightSectors a b h)
                      (\d -> allowedF a b h d)
                      chH
                  buf' = fmoveAtomsFlat True a b h buf
                  unpacked =
                    unpackAtomsFlat
                      (leftSectors a b h)
                      (\d -> allowedE a b h d)
                      buf'
               in [(d, e, h, v) | (d, e, v) <- unpacked]
          )
          hs
   in scatterAssocLHom
        (repSing @ls)
        (Map.fromList [((d, e, h), v) | (d, e, h, v) <- out])

-- | Naturality of @Fuse(a, –)@: @refuse ∘ (id ⊗ f) ∘ unfuse@ on fusion trees.
--
-- Production path packs/unpacks /expanded/ spine-order root flats (one slot per
-- tree) — never coalesced 'ForgetRep' sectors — then applies the CG naturality
-- helpers. Same-root genealogies stay distinct, matching 'Expr' / 'FuseRep'.
fuseMapRight
  :: forall a q q'
   . ( KnownRep a
     , KnownRep q
     , KnownRep q'
     , KnownRep (FuseRep a q)
     , KnownRep (FuseRep a q')
     )
  => (RepV q -> RepV q')
  -> RepV (FuseRep a q)
  -> RepV (FuseRep a q')
fuseMapRight f tv =
  let secsA = repExpandedSectors (repSing @a)
      secsQ = repExpandedSectors (repSing @q)
      secsQ' = repExpandedSectors (repSing @q')
      fFlat = repVToExpandedFlat @q' . f . expandedFlatToRepV @q
      vin = repVToExpandedFlat @(FuseRep a q) tv
      vout = fuseMapRightFlatSectors secsA secsQ secsQ' fFlat vin
   in expandedFlatToRepV @(FuseRep a q') vout

-- | Naturality of @Fuse(–, b)@: @refuse ∘ (f ⊗ id) ∘ unfuse@.
fuseMapLeft
  :: forall a a' b
   . ( KnownRep a
     , KnownRep a'
     , KnownRep b
     , KnownRep (FuseRep a b)
     , KnownRep (FuseRep a' b)
     )
  => (RepV a -> RepV a')
  -> RepV (FuseRep a b)
  -> RepV (FuseRep a' b)
fuseMapLeft f tv =
  let secsA = repExpandedSectors (repSing @a)
      secsA' = repExpandedSectors (repSing @a')
      secsB = repExpandedSectors (repSing @b)
      fFlat = repVToExpandedFlat @a' . f . expandedFlatToRepV @a
      vin = repVToExpandedFlat @(FuseRep a b) tv
      vout = fuseMapLeftFlatSectors secsA secsA' secsB fFlat vin
   in expandedFlatToRepV @(FuseRep a' b) vout

-- | Expanded @(tj, 1, off)@ sectors — one slot per tree (spine order).
repExpandedSectors :: SRep ts -> [(Int, Int, Int)]
repExpandedSectors = go 0
  where
    go :: Int -> SRep ts' -> [(Int, Int, Int)]
    go _ SRepNil = []
    go off (SRepCons t rest) =
      let tj = rootLab t
          d = tj + 1
       in (tj, 1, off) : go (off + d) rest

-- | Concatenate root vectors in spine order (matches 'repExpandedSectors').
repVToExpandedFlat
  :: forall ts
   . KnownRep ts
  => RepV ts
  -> VS.Vector (Complex Double)
repVToExpandedFlat = go (repSing @ts)
  where
    go :: SRep ts' -> RepV ts' -> VS.Vector (Complex Double)
    go SRepNil RNil = VS.empty
    go (SRepCons t rest) (RCons v rs) =
      case t of
        SBare {} -> toArray v VS.++ go rest rs
        SFrom {} -> toArray v VS.++ go rest rs
    go _ _ = error "repVToExpandedFlat: RepV / SRep mismatch"

-- | Inverse of 'repVToExpandedFlat'.
expandedFlatToRepV
  :: forall ts
   . KnownRep ts
  => VS.Vector (Complex Double)
  -> RepV ts
expandedFlatToRepV buf = go 0 (repSing @ts)
  where
    go :: Int -> SRep ts' -> RepV ts'
    go _ SRepNil = RNil
    go off (SRepCons (t :: SIrrepTree u) rest) =
      case t of
        SBare @j ->
          let d = fromIntegral (natVal (Proxy @j)) + 1
              v = unsafeFromArray (VS.slice off d buf)
           in RCons @u v (go (off + d) rest)
        SFrom @j _ _ ->
          let d = fromIntegral (natVal (Proxy @j)) + 1
              v = unsafeFromArray (VS.slice off d buf)
           in RCons @u v (go (off + d) rest)
