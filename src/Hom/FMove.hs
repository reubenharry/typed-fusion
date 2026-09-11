{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | F-moves and FuseFTrees naturality on genealogy spines.
--
-- Production 'idRight'/'idLeft' use expanded spine-order flats
-- (no coalesced 'ForgetRep'). Irrep F-moves still route through Fusion.SU2
-- collect/scatter flats as an oracle — typed per-channel @C (d+1)@ F is a
-- follow-on (Phase 4).
module Hom.FMove
  ( fmoveTrees
  , fmoveInvTrees
  , fmoveOuterHom
  , fmoveInvOuterHom
  , fmoveTreesHomLeft
  , fmoveInvTreesHomLeft
  , TensorTrees (..)
  , fuseTensorTrees
  , idRight
  , idLeft
  , fTreeVToExpandedFlat
  , expandedFlatToFTreeV
  ) where

import Data.Complex (Complex)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
import qualified Data.Vector.Storable as VS
import Fusion.SU2
  ( allowedE
  , allowedF
  , fmoveIrrepsFlat
  , leftSectors
  , packIrrepsFlat
  , rightSectors
  , unpackIrrepsFlat
  )
import Hom.Expr
import Hom.FTreeV
import Hom.Singletons
import Hom.TypeLevel
import GHC.TypeLits (KnownNat, Nat, natVal)
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Symmetry.CG.SU2
  ( fuseMapLeftFlatSectors
  , fuseMapRightFlatSectors
  )

-- | Collect left-assoc channels from @((a_i⊗b_j)_e ⊗ c_k)_d@.
--
-- Keys include roots of the embedded factors so multi-tree spines
-- (e.g. Hom⊗leaf⊗leaf) do not collide on @(d,e)@ alone.
collectAssocLChannel
  :: SFTrees ts
  -> FTreeV ts
  -> [(Int, Int, Int, Int, Int, VS.Vector (Complex Double))]
collectAssocLChannel SFTreesNil FNil = []
collectAssocLChannel (SFTreesCons t rest) (FCons v rs) =
  case t of
    SFrom left right ->
      case left of
        SFrom a_i b_j ->
          ( rootLab t
          , rootLab left
          , rootLab a_i
          , rootLab b_j
          , rootLab right
          , toArray v
          )
            : collectAssocLChannel rest rs
        SIrrepTree {} ->
          error "collectAssocLChannel: expected From intermediate (not left-assoc FuseFTrees?)"
        SIrrepTree {} ->
          error "collectAssocLChannel: leaf in association spine (not left-assoc FuseFTrees?)"

-- | Collect right-assoc channels from @(a_i ⊗ (b_j⊗c_k)_f)_d@.
collectAssocRChannel
  :: SFTrees ts
  -> FTreeV ts
  -> [(Int, Int, Int, Int, Int, VS.Vector (Complex Double))]
collectAssocRChannel SFTreesNil FNil = []
collectAssocRChannel (SFTreesCons t rest) (FCons v rs) =
  case t of
    SFrom left right ->
      case right of
        SFrom b_j c_k ->
          ( rootLab t
          , rootLab right
          , rootLab left
          , rootLab b_j
          , rootLab c_k
          , toArray v
          )
            : collectAssocRChannel rest rs
        SIrrepTree {} ->
          error "collectAssocRChannel: expected From intermediate (not right-assoc FuseFTrees?)"
        SIrrepTree {} ->
          error "collectAssocRChannel: leaf in association spine (not right-assoc FuseFTrees?)"

-- | @(d, mid, ra, rb, rc)@ channel map → AssocL spine.
scatterAssocLChannel
  :: SFTrees ts
  -> Map.Map (Int, Int, Int, Int, Int) (VS.Vector (Complex Double))
  -> FTreeV ts
scatterAssocLChannel SFTreesNil _ = FNil
scatterAssocLChannel (SFTreesCons (t :: SFTree u) rest) m =
  case t of
    SFrom left right ->
      case left of
        SFrom a_i b_j ->
          let key =
                ( rootLab t
                , rootLab left
                , rootLab a_i
                , rootLab b_j
                , rootLab right
                )
           in FCons @u
                (unsafeFromArray (Map.findWithDefault (zeroLike5 key m) key m))
                (scatterAssocLChannel rest m)
        SIrrepTree {} ->
          error "scatterAssocLChannel: expected From intermediate"
    SIrrepTree {} ->
      error "scatterAssocLChannel: leaf in association spine"

scatterAssocRChannel
  :: SFTrees ts
  -> Map.Map (Int, Int, Int, Int, Int) (VS.Vector (Complex Double))
  -> FTreeV ts
scatterAssocRChannel SFTreesNil _ = FNil
scatterAssocRChannel (SFTreesCons (t :: SFTree u) rest) m =
  case t of
    SFrom left right ->
      case right of
        SFrom b_j c_k ->
          let key =
                ( rootLab t
                , rootLab right
                , rootLab left
                , rootLab b_j
                , rootLab c_k
                )
           in FCons @u
                (unsafeFromArray (Map.findWithDefault (zeroLike5 key m) key m))
                (scatterAssocRChannel rest m)
        SIrrepTree {} ->
          error "scatterAssocRChannel: expected From intermediate"
    SIrrepTree {} ->
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

-- | 3-factor F-move: @FuseFTrees (FuseFTrees a b) c → FuseFTrees a (FuseFTrees b c)@.
--
-- 'FuseFTrees' distributes into channels @((a_i⊗b_j)_e ⊗ c_k)_d@. For each
-- distinct root triple @(r(a_i),r(b_j),r(c_k))@ apply dense Racah
-- @F^{ra rb rc}@, keeping genealogy in the channel key.
fmoveTrees
  :: forall a b c
   . ( KnownFTrees (FuseFTrees (FuseFTrees a b) c)
     , KnownFTrees (FuseFTrees a (FuseFTrees b c))
     )
  => FTreeV (FuseFTrees (FuseFTrees a b) c)
  -> FTreeV (FuseFTrees a (FuseFTrees b c))
fmoveTrees tv =
  let chans = collectAssocLChannel (fTreesSing @_ @(FuseFTrees (FuseFTrees a b) c)) tv
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
                    packIrrepsFlat
                      (leftSectors ra rb rc)
                      (\d -> allowedE ra rb rc d)
                      chH
                  buf' = fmoveIrrepsFlat False ra rb rc buf
                  unpacked =
                    unpackIrrepsFlat
                      (rightSectors ra rb rc)
                      (\d -> allowedF ra rb rc d)
                      buf'
               in [(d, f, ra, rb, rc, v) | (d, f, v) <- unpacked]
          )
          triples
   in scatterAssocRChannel
        (fTreesSing @_ @(FuseFTrees a (FuseFTrees b c)))
        (Map.fromList [((d, f, ra, rb, rc), v) | (d, f, ra, rb, rc, v) <- out])

fmoveInvTrees
  :: forall a b c
   . ( KnownFTrees (FuseFTrees (FuseFTrees a b) c)
     , KnownFTrees (FuseFTrees a (FuseFTrees b c))
     )
  => FTreeV (FuseFTrees a (FuseFTrees b c))
  -> FTreeV (FuseFTrees (FuseFTrees a b) c)
fmoveInvTrees tv =
  let chans = collectAssocRChannel (fTreesSing @_ @(FuseFTrees a (FuseFTrees b c))) tv
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
                    packIrrepsFlat
                      (rightSectors ra rb rc)
                      (\d -> allowedF ra rb rc d)
                      chH
                  buf' = fmoveIrrepsFlat True ra rb rc buf
                  unpacked =
                    unpackIrrepsFlat
                      (leftSectors ra rb rc)
                      (\d -> allowedE ra rb rc d)
                      buf'
               in [(d, e, ra, rb, rc, v) | (d, e, v) <- unpacked]
          )
          triples
   in scatterAssocLChannel
        (fTreesSing @_ @(FuseFTrees (FuseFTrees a b) c))
        (Map.fromList [((d, e, ra, rb, rc), v) | (d, e, ra, rb, rc, v) <- out])

-- | Outer Hom F: @(a⊗b) ⊗ Hom(b,c) → a ⊗ (b ⊗ Hom(b,c))@.
fmoveOuterHom
  :: forall a b c
   . ( KnownFTrees (FuseFTrees (FuseFTrees a b) (FuseFTrees b c))
     , KnownFTrees (FuseFTrees a (FuseFTrees b (FuseFTrees b c)))
     )
  => FTreeV (FuseFTrees (FuseFTrees a b) (FuseFTrees b c))
  -> FTreeV (FuseFTrees a (FuseFTrees b (FuseFTrees b c)))
fmoveOuterHom = fmoveTrees @a @b @(FuseFTrees b c)

fmoveInvOuterHom
  :: forall a b c
   . ( KnownFTrees (FuseFTrees (FuseFTrees a b) (FuseFTrees b c))
     , KnownFTrees (FuseFTrees a (FuseFTrees b (FuseFTrees b c)))
     )
  => FTreeV (FuseFTrees a (FuseFTrees b (FuseFTrees b c)))
  -> FTreeV (FuseFTrees (FuseFTrees a b) (FuseFTrees b c))
fmoveInvOuterHom = fmoveInvTrees @a @b @(FuseFTrees b c)

-- | Nested unfused @a ⊗ q@ before CG (layout for Fuse-right naturality).
data TensorTrees (a :: FTrees Nat) (q :: FTrees Nat) where
  TensorTrees :: FTreeV a -> FTreeV q -> TensorTrees a q

fuseTensorTrees
  :: forall a q
   . ( KnownFTrees a
     , KnownFTrees q
     , FuseFTreesTermC a q
     )
  => TensorTrees a q
  -> FTreeV (FuseFTrees a q)
fuseTensorTrees (TensorTrees a q) = fuseFTreesTerm @a @q a q

-- | Hom-left nested F: left factor @FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree ja]@.
-- Plain functions (Nat-indexed so 'FuseFTrees' stays out of instance heads).
fmoveTreesHomLeft
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownFTrees
         ( FuseFTrees (FuseFTrees (FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree ja]) '[ 'IrrepTree jb]) '[ 'IrrepTree jc]
         )
     , KnownFTrees
         ( FuseFTrees (FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree ja]) (FuseFTrees '[ 'IrrepTree jb] '[ 'IrrepTree jc])
         )
     )
  => FTreeV
       ( FuseFTrees (FuseFTrees (FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree ja]) '[ 'IrrepTree jb]) '[ 'IrrepTree jc]
       )
  -> FTreeV
       ( FuseFTrees (FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree ja]) (FuseFTrees '[ 'IrrepTree jb] '[ 'IrrepTree jc])
       )
fmoveTreesHomLeft =
  fmoveTrees
    @(FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree ja])
    @('[ 'IrrepTree jb])
    @('[ 'IrrepTree jc])

fmoveInvTreesHomLeft
  :: forall ja jb jc
   . ( KnownNat ja
     , KnownNat jb
     , KnownNat jc
     , KnownFTrees
         ( FuseFTrees (FuseFTrees (FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree ja]) '[ 'IrrepTree jb]) '[ 'IrrepTree jc]
         )
     , KnownFTrees
         ( FuseFTrees (FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree ja]) (FuseFTrees '[ 'IrrepTree jb] '[ 'IrrepTree jc])
         )
     )
  => FTreeV
       ( FuseFTrees (FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree ja]) (FuseFTrees '[ 'IrrepTree jb] '[ 'IrrepTree jc])
       )
  -> FTreeV
       ( FuseFTrees (FuseFTrees (FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree ja]) '[ 'IrrepTree jb]) '[ 'IrrepTree jc]
       )
fmoveInvTreesHomLeft =
  fmoveInvTrees
    @(FuseFTrees '[ 'IrrepTree ja] '[ 'IrrepTree ja])
    @('[ 'IrrepTree jb])
    @('[ 'IrrepTree jc])

-- | Naturality of @Fuse(a, –)@: @refuse ∘ (id ⊗ f) ∘ unfuse@ on fusion trees.
--
-- Production path packs/unpacks /expanded/ spine-order root flats (one slot per
-- tree) — never coalesced 'ForgetRep' sectors — then applies the CG naturality
-- helpers. Same-root genealogies stay distinct, matching 'Expr' / 'FuseFTrees'.
idRight
  :: forall a q q'
   . ( KnownFTrees a
     , KnownFTrees q
     , KnownFTrees q'
     , KnownFTrees (FuseFTrees a q)
     , KnownFTrees (FuseFTrees a q')
     )
  => (FTreeV q -> FTreeV q')
  -> FTreeV (FuseFTrees a q)
  -> FTreeV (FuseFTrees a q')
idRight f tv =
  let secsA = repExpandedSectors (fTreesSing @_ @a)
      secsQ = repExpandedSectors (fTreesSing @_ @q)
      secsQ' = repExpandedSectors (fTreesSing @_ @q')
      fFlat = fTreeVToExpandedFlat @q' . f . expandedFlatToFTreeV @q
      vin = fTreeVToExpandedFlat @(FuseFTrees a q) tv
      vout = fuseMapRightFlatSectors secsA secsQ secsQ' fFlat vin
   in expandedFlatToFTreeV @(FuseFTrees a q') vout

-- | Naturality of @Fuse(–, b)@: @refuse ∘ (f ⊗ id) ∘ unfuse@.
idLeft
  :: forall a a' b
   . ( KnownFTrees a
     , KnownFTrees a'
     , KnownFTrees b
     , KnownFTrees (FuseFTrees a b)
     , KnownFTrees (FuseFTrees a' b)
     )
  => (FTreeV a -> FTreeV a')
  -> FTreeV (FuseFTrees a b)
  -> FTreeV (FuseFTrees a' b)
idLeft f tv =
  let secsA = repExpandedSectors (fTreesSing @_ @a)
      secsA' = repExpandedSectors (fTreesSing @_ @a')
      secsB = repExpandedSectors (fTreesSing @_ @b)
      fFlat = fTreeVToExpandedFlat @a' . f . expandedFlatToFTreeV @a
      vin = fTreeVToExpandedFlat @(FuseFTrees a b) tv
      vout = fuseMapLeftFlatSectors secsA secsA' secsB fFlat vin
   in expandedFlatToFTreeV @(FuseFTrees a' b) vout

-- | Expanded @(tj, 1, off)@ sectors — one slot per tree (spine order).
repExpandedSectors :: SFTrees ts -> [(Int, Int, Int)]
repExpandedSectors = go 0
  where
    go :: Int -> SFTrees ts' -> [(Int, Int, Int)]
    go _ SFTreesNil = []
    go off (SFTreesCons t rest) =
      let tj = rootLab t
          d = tj + 1
       in (tj, 1, off) : go (off + d) rest

-- | Concatenate root vectors in spine order (matches 'repExpandedSectors').
fTreeVToExpandedFlat
  :: forall ts
   . KnownFTrees ts
  => FTreeV ts
  -> VS.Vector (Complex Double)
fTreeVToExpandedFlat = go (fTreesSing @_ @ts)
  where
    go :: SFTrees ts' -> FTreeV ts' -> VS.Vector (Complex Double)
    go SFTreesNil FNil = VS.empty
    go (SFTreesCons t rest) (FCons v rs) =
      case t of
        SIrrepTree {} -> toArray v VS.++ go rest rs
        SFrom {} -> toArray v VS.++ go rest rs
    go _ _ = error "fTreeVToExpandedFlat: FTreeV / SFTrees mismatch"

-- | Inverse of 'fTreeVToExpandedFlat'.
expandedFlatToFTreeV
  :: forall ts
   . KnownFTrees ts
  => VS.Vector (Complex Double)
  -> FTreeV ts
expandedFlatToFTreeV buf = go 0 (fTreesSing @_ @ts)
  where
    go :: Int -> SFTrees ts' -> FTreeV ts'
    go _ SFTreesNil = FNil
    go off (SFTreesCons (t :: SFTree u) rest) =
      case t of
        SIrrepTree {} ->
          let d = rootLab t + 1
              v = unsafeFromArray (VS.slice off d buf)
           in FCons @u v (go (off + d) rest)
        SFrom {} ->
          let d = rootLab t + 1
              v = unsafeFromArray (VS.slice off d buf)
           in FCons @u v (go (off + d) rest)
