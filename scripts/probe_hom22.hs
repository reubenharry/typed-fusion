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
        RCons @('From 0 '( 'I 2, 'I 2)) (konst 0.2) $
          RCons @('From 2 '( 'I 2, 'I 2)) (konst 0.3) $
            RCons @('From 4 '( 'I 2, 'I 2)) (konst 0.5) RNil
      outFid = composeHomTrees @I2 @I2 @I2 f (idHomI @2)
      outIdf = composeHomTrees @I2 @I2 @I2 (idHomI @2) f
  putStrLn $ "f        = " ++ show (flat @Hom22 f)
  putStrLn $ "outFid   = " ++ show (flat @Hom22 outFid)
  putStrLn $ "outIdf   = " ++ show (flat @Hom22 outIdf)
