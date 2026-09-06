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
          desc = showIrrep t
          keep = isCupKeep t
      putStrLn $
        show i ++ ": keep=" ++ show keep
          ++ " ||v||^2=" ++ show nrm
          ++ "  " ++ desc
      go (i + 1) rest rs
    go _ _ _ = pure ()

    showIrrep :: forall t. SIrrepTree t -> String
    showIrrep (SLeaf @j) = "Leaf " ++ show (natVal (Proxy @j))
    showIrrep (SNode @j l r) =
      "Node " ++ show (natVal (Proxy @j))
        ++ " (" ++ showIrrep l ++ ") (" ++ showIrrep r ++ ")"

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
      outerFid = fmoveOuterHom @Leaf2 @Leaf2 @Leaf2 domFid
      cupFid = fmoveInnerHom @Leaf2 @Leaf2 @Leaf2 outerFid
      domIdf = fuseTreeRepTerm @Hom22 @Hom22 idHom22 f22
      outerIdf = fmoveOuterHom @Leaf2 @Leaf2 @Leaf2 domIdf
      cupIdf = fmoveInnerHom @Leaf2 @Leaf2 @Leaf2 outerIdf
  dumpTrees @(FuseTreeRep Hom22 Hom22) "dom Fid (f⊗id)" domFid
  dumpTrees "outer Fid" outerFid
  dumpTrees "cupR Fid (after id⊗F)" cupFid
  putStrLn ""
  dumpTrees @(FuseTreeRep Hom22 Hom22) "dom Idf (id⊗f)" domIdf
  dumpTrees "outer Idf" outerIdf
  dumpTrees "cupR Idf (after id⊗F)" cupIdf
