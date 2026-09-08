{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE GADTs #-}

import Data.Complex
import Data.Proxy
import Experiments.Symbolic.Core
import Experiments.Symbolic.Expr
import Experiments.Symbolic.TypeLevel
import GHC.TypeLits (natVal)
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static (konst)
import qualified Data.Vector.Storable as VS

dumpNZ
  :: forall ts
   . KnownRep ts
  => String
  -> RepV ts
  -> IO ()
dumpNZ label tv = do
  putStrLn $ "=== " ++ label ++ " ==="
  go 0 (repSing @ts) tv
  where
    go :: Int -> SRep ts' -> RepV ts' -> IO ()
    go _ SRepNil RNil = pure ()
    go i (SRepCons t rest) (RCons v rs) = do
      let arr :: VS.Vector (Complex Double)
          arr = case t of
            SBare {} -> toArray v
            SFrom {} -> toArray v
          nrm = VS.sum $ VS.map (\x -> realPart (x * conjugate x)) arr
      if nrm > 1e-18
        then putStrLn $ show i ++ ": keep=" ++ show (isCupKeep t) ++ " ||v||^2=" ++ show nrm ++ "  " ++ showIrrep t
        else pure ()
      go (i + 1) rest rs
    go _ _ _ = pure ()

    showIrrep :: forall t. SIrrepTree t -> String
    showIrrep (SBare @j) = "L" ++ show (natVal (Proxy @j))
    showIrrep (SFrom @j l r) =
      "N" ++ show (natVal (Proxy @j)) ++ "(" ++ showIrrep l ++ "," ++ showIrrep r ++ ")"

    isCupKeep :: forall t. SIrrepTree t -> Bool
    isCupKeep (SFrom @_ @_ @_ _ r) = case r of
      SFrom @_ @_ @_ mid _ -> case mid of
        SFrom @m _ _ -> natVal (Proxy @m) == 0
        SBare {} -> False
      SBare {} -> False
    isCupKeep _ = False

f22 :: RepV Hom22
f22 =
  RCons @('From 0 '( 'Bare 2, 'Bare 2)) (konst 0.2) $
    RCons @('From 2 '( 'Bare 2, 'Bare 2)) (konst 0.3) $
      RCons @('From 4 '( 'Bare 2, 'Bare 2)) (konst 0.5) RNil

main :: IO ()
main = do
  let domFid = fuseRepTerm @Hom22 @Hom22 f22 (idHomBare @2)
      outerFid = fmoveOuterHom @Bare2 @Bare2 @Bare2 domFid
      cupFid = fmoveInnerHom @Bare2 @Bare2 @Bare2 outerFid
      outFid =
        unitorHom @Bare2 @Bare2
          (cupTensorIdHom @Bare2 @Bare2 @Bare2 cupFid)
      domIdf = fuseRepTerm @Hom22 @Hom22 (idHomBare @2) f22
      outerIdf = fmoveOuterHom @Bare2 @Bare2 @Bare2 domIdf
      cupIdf = fmoveInnerHom @Bare2 @Bare2 @Bare2 outerIdf
      outIdf =
        unitorHom @Bare2 @Bare2
          (cupTensorIdHom @Bare2 @Bare2 @Bare2 cupIdf)
  dumpNZ "outer Fid (Hom-pres)" outerFid
  dumpNZ "cupR Fid" cupFid
  putStrLn $ "outFid = " ++ show (VS.toList (repVToExpandedFlat @Hom22 outFid))
  putStrLn ""
  dumpNZ "outer Idf (Hom-pres)" outerIdf
  dumpNZ "cupR Idf" cupIdf
  putStrLn $ "outIdf = " ++ show (VS.toList (repVToExpandedFlat @Hom22 outIdf))
  putStrLn $ "f22    = " ++ show (VS.toList (repVToExpandedFlat @Hom22 f22))
