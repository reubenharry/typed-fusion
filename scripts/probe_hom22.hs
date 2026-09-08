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
        RCons @('From 0 '( 'Bare 2, 'Bare 2)) (konst 0.2) $
          RCons @('From 2 '( 'Bare 2, 'Bare 2)) (konst 0.3) $
            RCons @('From 4 '( 'Bare 2, 'Bare 2)) (konst 0.5) RNil
      outFid = composeHomTrees @Bare2 @Bare2 @Bare2 f (idHomBare @2)
      outIdf = composeHomTrees @Bare2 @Bare2 @Bare2 (idHomBare @2) f
  putStrLn $ "f        = " ++ show (flat @Hom22 f)
  putStrLn $ "outFid   = " ++ show (flat @Hom22 outFid)
  putStrLn $ "outIdf   = " ++ show (flat @Hom22 outIdf)
