{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

import Data.Complex
import Experiments.Symbolic.Core
import Experiments.Symbolic.Expr
import Numeric.LinearAlgebra.Static (konst)
import qualified Data.Vector.Storable as VS

flat :: forall ts. KnownRep ts => RepV ts -> [Complex Double]
flat = VS.toList . repVToExpandedFlat @ts

main :: IO ()
main = do
  let f =
        RCons @('Node 0 ('Leaf 2) ('Leaf 2)) (konst 0.2) $
          RCons @('Node 2 ('Leaf 2) ('Leaf 2)) (konst 0.3) $
            RCons @('Node 4 ('Leaf 2) ('Leaf 2)) (konst 0.5) RNil
      outFid = composeHomTrees @Leaf2 @Leaf2 @Leaf2 f (idHomLeaf @2)
      outIdf = composeHomTrees @Leaf2 @Leaf2 @Leaf2 (idHomLeaf @2) f
  putStrLn $ "f        = " ++ show (flat @Hom22 f)
  putStrLn $ "outFid   = " ++ show (flat @Hom22 outFid)
  putStrLn $ "outIdf   = " ++ show (flat @Hom22 outIdf)
