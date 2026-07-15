{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Open-boundary MPS/MPO environments and value-level env updates for
-- 'MPS' chains.
module TensorNetwork.DMRG.Env where

import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import qualified Control.Functor.Constrained as CF
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗)
  , TensorSpace (..), contractTensorMap, (-+$>) )
import Math.LinearMap.Coercion (curryLinearMap, (-+$=>))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C)
import GHC.TypeLits (KnownNat, type (*))
import TensorNetwork.Categorical (lunit, lunitInv)
import TensorNetwork.Dagger
import TensorNetwork.MPS.Fixed
import TensorNetwork.DMRG.Chain

-- type LeftEnv w a b = C a +> (C w ⊗ C b)
-- type RightEnv w a b = (C w ⊗ C b) +> C a

-- leftBoundary :: LeftEnv 1 1 1
-- leftBoundary = lunitInv @(C 1)

-- rightBoundary :: RightEnv 1 1 1
-- rightBoundary = lunit @(C 1)

-- extendLeft
--   :: forall p wl wr al ar bl br.
--      ( OpWireNats p wl wr bl br
--      , KnownNat al, KnownNat ar
--      , KnownNat (al * p), KnownNat (wl * bl), KnownNat (p * ar)
--      , p * al ~ al * p )
--   => LeftEnv wl al bl
--   -> Site al p ar
--   -> OpSite wl p wr
--   -> Site bl p br
--   -> LeftEnv wr ar br
-- extendLeft env bra op ket = undefined

-- extendRight
--   :: forall p wl wr al ar bl br.
--      ( OpWireNats p wl wr bl br, KnownNat al, KnownNat ar
--      , KnownNat (p * al), KnownNat (ar * p), p * ar ~ ar * p )
--   => Site ar p al
--   -> OpSite wl p wr
--   -> Site br p bl
--   -> RightEnv wr al bl
--   -> RightEnv wl ar br
-- extendRight (Site bra) (OpSite op) (Site ket) envR =
--   CF.fmap (contractTensorMap Cat.. CF.fmap transposeTensor)
--     -+$> (curryLinearMap -+$=> k)
--   where
--     k :: ((C wl ⊗ C br) ⊗ C p) +> (C ar ⊗ C p)
--     k = siteDagger bra . envR . opWire @p op ket

-- data MoveRightEnv = MoveRightInterior | MoveRightBoundary
-- data MoveLeftEnv = MoveLeftInterior | MoveLeftBoundary'

-- data LeftEnvAtCentre w b where
--   LeftEnvFirst :: LeftEnv 1 1 1 -> LeftEnvAtCentre w b
--   LeftEnvBulk  :: LeftEnv w b b -> LeftEnvAtCentre w b

-- data RightEnvAtCentre w b where
--   RightEnvLast :: RightEnv 1 1 1 -> RightEnvAtCentre w b
--   RightEnvBulk :: RightEnv w b b -> RightEnvAtCentre w b

-- moveRightEnv' :: forall l. KnownNat l => Int -> MoveRightEnv
-- moveRightEnv' i
--   | i + 1 == chainLength @l = MoveRightBoundary
--   | i + 1 < chainLength @l = MoveRightInterior
--   | otherwise =
--       error ("moveRightEnv': centre " ++ show i ++ " cannot move right")

-- moveLeftEnv' :: Int -> MoveLeftEnv
-- moveLeftEnv' i
--   | i <= 1 = error ("moveLeftEnv': centre " ++ show i ++ " cannot move left")
--   | i - 1 == 1 = MoveLeftBoundary'
--   | otherwise = MoveLeftInterior

-- buildLeftEnvUpTo
--   :: forall p w b l
--    . ( KnownNat l, OpWireNats p w w b b )
--   => Int
--   -> MPO p w l
--   -> MPS p b l
--   -> LeftEnvAtCentre w b
-- buildLeftEnvUpTo j _ _
--   | j <= 1 = LeftEnvFirst leftBoundary
-- buildLeftEnvUpTo j mpo mps
--   | j == 2 = LeftEnvBulk (extendLeftFirstSite mpo mps)
--   | otherwise =
--       LeftEnvBulk
--         (foldl (extendLeftBulkSite mpo mps) (extendLeftFirstSite mpo mps) [2 .. j - 1])

-- bulkLeftEnvUpTo
--   :: forall p w b l
--    . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
--      , OpWireNats p w w b b )
--   => Int
--   -> MPO p w l
--   -> MPS p b l
--   -> LeftEnv w b b
-- bulkLeftEnvUpTo j mpo mps
--   | j <= 1 =
--       error ("bulkLeftEnvUpTo: index " ++ show j ++ " must be at least 2")
--   | j == 2 = extendLeftFirstSite mpo mps
--   | otherwise =
--       foldl (extendLeftBulkSite mpo mps) (extendLeftFirstSite mpo mps) [2 .. j - 1]

-- extendLeftFirstSite
--   :: forall p w b l
--    . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
--      , OpWireNats p w w b b )
--   => MPO p w l
--   -> MPS p b l
--   -> LeftEnv w b b
-- extendLeftFirstSite mpo mps =
--   case (getSite 1 mps, getOp 1 mpo) of
--     (SiteLeft s, OpLeft o) -> extendLeft leftBoundary s o s
--     _ -> error "extendLeftFirstSite: expected site/op 1"

-- extendLeftBulkSite
--   :: forall p w b l
--    . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
--      , OpWireNats p w w b b )
--   => MPO p w l
--   -> MPS p b l
--   -> LeftEnv w b b
--   -> Int
--   -> LeftEnv w b b
-- extendLeftBulkSite mpo mps env k =
--   case (getSite k mps, getOp k mpo) of
--     (SiteBulk s, OpBulk o) -> extendLeft env s o s
--     _ -> error ("extendLeftBulkSite: expected bulk site/op at index " ++ show k)

-- buildRightEnvFromSite
--   :: forall p w b l
--    . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
--      , OpWireNats p w w b b )
--   => Int
--   -> MPO p w l
--   -> MPS p b l
--   -> RightEnv w b b
-- buildRightEnvFromSite start mpo mps = go start
--   where
--     n = chainLength @l
--     go k
--       | k > n =
--           error ("buildRightEnvFromSite: start " ++ show start ++ " past chain end")
--       | k == n = extendRightLastSite mpo mps k rightBoundary
--       | otherwise = extendRightBulkSite mpo mps k (go (k + 1))

-- extendRightLastSite
--   :: forall p w b l
--    . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
--      , OpWireNats p w w b b )
--   => MPO p w l
--   -> MPS p b l
--   -> Int
--   -> RightEnv 1 1 1
--   -> RightEnv w b b
-- extendRightLastSite mpo mps k env =
--   case (getSite k mps, getOp k mpo) of
--     (SiteRight s, OpRight o) -> extendRight s o s env
--     _ -> error ("extendRightLastSite: expected last site/op at index " ++ show k)

-- extendRightBulkSite
--   :: forall p w b l
--    . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
--      , OpWireNats p w w b b )
--   => MPO p w l
--   -> MPS p b l
--   -> Int
--   -> RightEnv w b b
--   -> RightEnv w b b
-- extendRightBulkSite mpo mps k env =
--   case (getSite k mps, getOp k mpo) of
--     (SiteBulk s, OpBulk o) -> extendRight s o s env
--     _ -> error ("extendRightBulkSite: expected bulk site/op at index " ++ show k)

-- extendLeftMoveRight
--   :: forall p w b.
--      ( KnownNat p, KnownNat w, KnownNat b
--      , OpWireNats p w w b b )
--   => Int
--   -> LeftEnvAtCentre w b
--   -> SomeSite p b
--   -> SomeOpSite p w
--   -> LeftEnvAtCentre w b
-- extendLeftMoveRight 1 (LeftEnvFirst l) (SiteLeft cn) (OpLeft op) =
--   LeftEnvBulk (extendLeft l cn op cn)
-- extendLeftMoveRight _ (LeftEnvBulk l) (SiteBulk cn) (OpBulk op) =
--   LeftEnvBulk (extendLeft l cn op cn)
-- extendLeftMoveRight _ _ _ _ =
--   error "extendLeftMoveRight: centre site/op shape mismatch"

-- extendRightMoveLeft
--   :: forall p w b.
--      ( KnownNat p, KnownNat w, KnownNat b
--      , OpWireNats p w w b b )
--   => SomeSite p b
--   -> SomeOpSite p w
--   -> RightEnvAtCentre w b
--   -> RightEnvAtCentre w b
-- extendRightMoveLeft (SiteBulk cn) (OpBulk op) (RightEnvBulk r) =
--   RightEnvBulk (extendRight cn op cn r)
-- extendRightMoveLeft (SiteRight cn) (OpRight op) (RightEnvLast r) =
--   RightEnvBulk (extendRight cn op cn r)
-- extendRightMoveLeft _ _ _ =
--   error "extendRightMoveLeft: centre site/op shape mismatch"

-- updateEnvsMoveRight
--   :: forall p w b l
--    . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
--      , OpWireNats p w w b b )
--   => Int
--   -> MoveRightEnv
--   -> MPO p w l
--   -> MPS p b l
--   -> (LeftEnvAtCentre w b, RightEnvAtCentre w b)
--   -> SomeSite p b
--   -> SomeOpSite p w
--   -> ( LeftEnvAtCentre w b, RightEnvAtCentre w b )
-- updateEnvsMoveRight i wit mpo mps (l,_r) cn op =
--   let l' = extendLeftMoveRight i l cn op
--       r' = case wit of
--         MoveRightBoundary -> RightEnvLast rightBoundary
--         MoveRightInterior ->
--           RightEnvBulk (buildRightEnvFromSite (i + 2) mpo mps)
--   in (l', r')

-- updateEnvsMoveLeft
--   :: forall p w b l
--    . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b
--      , OpWireNats p w w b b )
--   => Int
--   -> MoveLeftEnv
--   -> MPO p w l
--   -> MPS p b l
--   -> RightEnvAtCentre w b
--   -> SomeSite p b
--   -> SomeOpSite p w
--   -> ( LeftEnvAtCentre w b, RightEnvAtCentre w b )
-- updateEnvsMoveLeft i wit mpo mps r cn op =
--   let r' = extendRightMoveLeft cn op r
--       l' = case wit of
--         MoveLeftBoundary' -> LeftEnvFirst leftBoundary
--         MoveLeftInterior -> buildLeftEnvUpTo (i - 1) mpo mps
--   in (l', r')
