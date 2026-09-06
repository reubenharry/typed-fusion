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
   . KnownTreeRep ts
  => String
  -> TreeV ts
  -> IO ()
dumpNZ label tv = do
  putStrLn $ "=== " ++ label ++ " ==="
  go 0 (treeRepSing @ts) tv
  where
    go :: Int -> STreeRep ts' -> TreeV ts' -> IO ()
    go _ STreeNil TNil = pure ()
    go i (STreeCons t rest) (TCons v rs) = do
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

f22 :: TreeV Hom22
f22 =
  TCons @('Node 0 ('Leaf 2) ('Leaf 2)) (konst 0.2) $
    TCons @('Node 2 ('Leaf 2) ('Leaf 2)) (konst 0.3) $
      TCons @('Node 4 ('Leaf 2) ('Leaf 2)) (konst 0.5) TNil

main :: IO ()
main = do
  let domFid = fuseTreeRepTerm @Hom22 @Hom22 f22 idHom22
      outerFid =
        fmoveOuterLeafHom @2 @2
          @(FuseAssocL Leaf2 Leaf2 Hom22)
          @(FuseAssocR Leaf2 Leaf2 Hom22)
          domFid
      cupFid =
        fuseMapRight
          @Leaf2
          @(FuseAssocR Leaf2 Leaf2 Leaf2)
          @(FuseAssocL Leaf2 Leaf2 Leaf2)
          (fmoveInvTreesLeaves @2 @2 @2)
          outerFid
      outFid = cupComposeTreesLeaf @2 @Leaf2 @Leaf2 cupFid
      domIdf = fuseTreeRepTerm @Hom22 @Hom22 idHom22 f22
      outerIdf =
        fmoveOuterLeafHom @2 @2
          @(FuseAssocL Leaf2 Leaf2 Hom22)
          @(FuseAssocR Leaf2 Leaf2 Hom22)
          domIdf
      cupIdf =
        fuseMapRight
          @Leaf2
          @(FuseAssocR Leaf2 Leaf2 Leaf2)
          @(FuseAssocL Leaf2 Leaf2 Leaf2)
          (fmoveInvTreesLeaves @2 @2 @2)
          outerIdf
      outIdf = cupComposeTreesLeaf @2 @Leaf2 @Leaf2 cupIdf
  dumpNZ "outer Fid (Hom-pres)" outerFid
  dumpNZ "cupR Fid" cupFid
  putStrLn $ "outFid = " ++ show (VS.toList (treeVToForgetFlat @Hom22 outFid))
  putStrLn ""
  dumpNZ "outer Idf (Hom-pres)" outerIdf
  dumpNZ "cupR Idf" cupIdf
  putStrLn $ "outIdf = " ++ show (VS.toList (treeVToForgetFlat @Hom22 outIdf))
  putStrLn $ "f22    = " ++ show (VS.toList (treeVToForgetFlat @Hom22 f22))
