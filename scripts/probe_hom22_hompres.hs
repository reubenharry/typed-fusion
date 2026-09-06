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
            SLeaf {} -> toArray v
            SNode {} -> toArray v
          nrm = VS.sum $ VS.map (\x -> realPart (x * conjugate x)) arr
      if nrm > 1e-18
        then putStrLn $ show i ++ ": keep=" ++ show (isCupKeep t) ++ " ||v||^2=" ++ show nrm ++ "  " ++ showIrrep t
        else pure ()
      go (i + 1) rest rs
    go _ _ _ = pure ()

    showIrrep :: forall t. SIrrepTree t -> String
    showIrrep (SLeaf @j) = "L" ++ show (natVal (Proxy @j))
    showIrrep (SNode @j l r) =
      "N" ++ show (natVal (Proxy @j)) ++ "(" ++ showIrrep l ++ "," ++ showIrrep r ++ ")"

    isCupKeep :: forall t. SIrrepTree t -> Bool
    isCupKeep (SNode @_ @_ @_ _ r) = case r of
      SNode @_ @_ @_ mid _ -> case mid of
        SNode @m _ _ -> natVal (Proxy @m) == 0
        SLeaf {} -> False
      SLeaf {} -> False
    isCupKeep _ = False

f22 :: RepV Hom22
f22 =
  RCons @('Node 0 ('Leaf 2) ('Leaf 2)) (konst 0.2) $
    RCons @('Node 2 ('Leaf 2) ('Leaf 2)) (konst 0.3) $
      RCons @('Node 4 ('Leaf 2) ('Leaf 2)) (konst 0.5) RNil

main :: IO ()
main = do
  let domFid = fuseRepTerm @Hom22 @Hom22 f22 idHom22
      outerFid = fmoveOuterHom @Leaf2 @Leaf2 @Leaf2 domFid
      cupFid = fmoveInnerHom @Leaf2 @Leaf2 @Leaf2 outerFid
      outFid =
        unitorHom @Leaf2 @Leaf2
          (cupTensorIdHom @Leaf2 @Leaf2 @Leaf2 cupFid)
      domIdf = fuseRepTerm @Hom22 @Hom22 idHom22 f22
      outerIdf = fmoveOuterHom @Leaf2 @Leaf2 @Leaf2 domIdf
      cupIdf = fmoveInnerHom @Leaf2 @Leaf2 @Leaf2 outerIdf
      outIdf =
        unitorHom @Leaf2 @Leaf2
          (cupTensorIdHom @Leaf2 @Leaf2 @Leaf2 cupIdf)
  dumpNZ "outer Fid (Hom-pres)" outerFid
  dumpNZ "cupR Fid" cupFid
  putStrLn $ "outFid = " ++ show (VS.toList (repVToForgetFlat @Hom22 outFid))
  putStrLn ""
  dumpNZ "outer Idf (Hom-pres)" outerIdf
  dumpNZ "cupR Idf" cupIdf
  putStrLn $ "outIdf = " ++ show (VS.toList (repVToForgetFlat @Hom22 outIdf))
  putStrLn $ "f22    = " ++ show (VS.toList (repVToForgetFlat @Hom22 f22))
