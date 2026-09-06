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

dumpTrees
  :: forall ts
   . KnownTreeRep ts
  => String
  -> TreeV ts
  -> IO ()
dumpTrees label tv = do
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
      when (nrm > 1e-20) $
        putStrLn $
          show i ++ ": keep=" ++ show (isCupKeep t)
            ++ " ||v||^2=" ++ show nrm
            ++ "  " ++ showIrrep t
      go (i + 1) rest rs
    go _ _ _ = pure ()

    when b m = if b then m else pure ()

    showIrrep :: forall t. SIrrepTree t -> String
    showIrrep (SLeaf @j) = "L" ++ show (natVal (Proxy @j))
    showIrrep (SNode @j l r) =
      "N" ++ show (natVal (Proxy @j))
        ++ "(" ++ showIrrep l ++ "," ++ showIrrep r ++ ")"

    isCupKeep :: forall t. SIrrepTree t -> Bool
    isCupKeep (SNode @_ @_ @_ _ r) = case r of
      SNode @_ @_ @_ mid _ -> case mid of
        SNode @m _ _ -> natVal (Proxy @m) == 0
        SLeaf {} -> False
      SLeaf {} -> False
    isCupKeep _ = False

f11 :: TreeV Hom11
f11 =
  TCons @('Node 0 ('Leaf 1) ('Leaf 1)) (konst 0.3) $
    TCons @('Node 2 ('Leaf 1) ('Leaf 1)) (konst 0.7) TNil

main :: IO ()
main = do
  let domFid = fuseTreeRepTerm @Hom11 @Hom11 f11 idHom11
      outerFid = fmoveOuterTrees @Leaf1 @Leaf1 @Hom11 domFid
      cupFid = fmoveComposeTreesLeaf @1 @1 @1 domFid
      outFid = cupComposeTreesLeaf @1 @Leaf1 @Leaf1 cupFid
  dumpTrees @(FuseTreeRep Hom11 Hom11) "Hom11 dom Fid" domFid
  dumpTrees "Hom11 outer Fid" outerFid
  dumpTrees "Hom11 cupR Fid" cupFid
  putStrLn $ "outFid flat = " ++ show (VS.toList (treeVToForgetFlat @Hom11 outFid))
  putStrLn $ "f11 flat    = " ++ show (VS.toList (treeVToForgetFlat @Hom11 f11))
