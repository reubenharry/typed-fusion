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
      outFid = composeHomTrees @Leaf2 @Leaf2 @Leaf2 f idHom22
      outIdf = composeHomTrees @Leaf2 @Leaf2 @Leaf2 idHom22 f
  putStrLn $ "f        = " ++ show (flat @Hom22 f)
  putStrLn $ "outFid   = " ++ show (flat @Hom22 outFid)
  putStrLn $ "outIdf   = " ++ show (flat @Hom22 outIdf)
