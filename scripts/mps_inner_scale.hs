{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE NoStarIsType #-}

-- | Scale 'mpsInner' vs bulk length (type-level @q@).
--   cabal run mps-inner-scale
import Control.Exception (evaluate)
import Control.Lens ((^.))
import Data.Complex (Complex, realPart)
import Data.Foldable (toList)
import Data.Proxy (Proxy (..))
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import GHC.TypeLits (KnownNat, Nat, natVal)
import Math.LinearMap.Category (getLinearMap)
import Numeric.LinearAlgebra.Static (C)
import Text.Printf (printf)

import TensorNetwork.DMRG.Fixed (productMPS)
import TensorNetwork.MPS.General
  ( FullNorm, hermitianNorm, mpsBulk, mpsInner, mpsLeft, mpsRight
  , siteDagger, transferBulkSite, transferLeftSite, transferRightSite
  )

timeMs :: String -> IO a -> IO a
timeMs label act = do
  t0 <- getCurrentTime
  a <- act
  t1 <- getCurrentTime
  printf "%-42s %10.3f ms\n" label (1000 * realToFrac (diffUTCTime t1 t0) :: Double)
  pure a

benchAt
  :: forall (q :: Nat)
   . KnownNat q
  => IO ()
benchAt = do
  let q = natVal (Proxy @q)
      nb = hermitianNorm :: FullNorm (C 3)
      np = hermitianNorm :: FullNorm (C 2)
      psi = productMPS @q
      nRep :: Int
      nRep = if q <= 4 then 20 else if q <= 16 then 5 else 1
  printf "\n== bulk length q = %d  (×%d) ==\n" q nRep
  _ <- timeMs ("mpsInner ×" ++ show nRep) $ do
    let zs = [ realPart (mpsInner nb np psi psi) | _ <- [1 .. nRep] ]
    evaluate (last zs)
  let l = psi ^. mpsLeft
      r = psi ^. mpsRight
      b0 = head (toList (psi ^. mpsBulk))
  env0 <- timeMs "transferLeftSite (force getLinearMap)" $ do
    let e = transferLeftSite nb np l l
    _ <- evaluate (getLinearMap e)
    pure e
  _ <- timeMs "siteDagger bulk (force getLinearMap)" $
    evaluate (getLinearMap (siteDagger nb np nb b0))
  _ <- timeMs "1× transferBulkSite (force mat)" $
    evaluate (getLinearMap (transferBulkSite nb np b0 b0 env0))
  _ <- timeMs "transferRightSite close" $
    evaluate (realPart (transferRightSite nb np r r env0 :: Complex Double))
  pure ()

main :: IO ()
main = do
  putStrLn "mpsInner scaling on productMPS @χ=3 @p=2"
  putStrLn "(expect ~linear in q if transfer is O(q·χ³))"
  benchAt @1
  benchAt @2
  benchAt @4
  benchAt @8
  benchAt @16
  benchAt @32
  benchAt @64
  benchAt @128
