{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

import Data.Complex
import Experiments.Symbolic.Core
import Experiments.Symbolic.Expr
import Numeric.LinearAlgebra.Static (konst)
import qualified Data.Vector.Storable as VS

flat :: forall ts. KnownTreeRep ts => TreeV ts -> [Complex Double]
flat = VS.toList . treeVToForgetFlat @ts

main :: IO ()
main = do
  let f =
        TCons @('Node 0 ('Leaf 2) ('Leaf 2)) (konst 0.2) $
          TCons @('Node 2 ('Leaf 2) ('Leaf 2)) (konst 0.3) $
            TCons @('Node 4 ('Leaf 2) ('Leaf 2)) (konst 0.5) TNil
      domFid = fuseTreeRepTerm @Hom22 @Hom22 f idHom22
      cupFid = fmoveComposeTreesLeaf @2 @2 @2 domFid
      outFid = cupComposeTreesLeaf @2 @Leaf2 @Leaf2 cupFid
      domIdf = fuseTreeRepTerm @Hom22 @Hom22 idHom22 f
      cupIdf = fmoveComposeTreesLeaf @2 @2 @2 domIdf
      outIdf = cupComposeTreesLeaf @2 @Leaf2 @Leaf2 cupIdf
  putStrLn $ "f        = " ++ show (flat @Hom22 f)
  putStrLn $ "cupFid   = " ++ show (flat cupFid)
  putStrLn $ "outFid   = " ++ show (flat @Hom22 outFid)
  putStrLn $ "cupIdf   = " ++ show (flat cupIdf)
  putStrLn $ "outIdf   = " ++ show (flat @Hom22 outIdf)
  putStrLn $ "mid keep Fid = " ++ show (flat (cupMiddleTreesTerm cupFid))
  putStrLn $ "mid keep Idf = " ++ show (flat (cupMiddleTreesTerm cupIdf))
