{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

import Data.Complex
import Hom.Core
import Hom.Expr
import Numeric.LinearAlgebra.Static (konst)
import qualified Data.Vector.Storable as VS

flat :: forall ts. KnownFTrees ts => RepV ts -> [Complex Double]
flat = VS.toList . repVToExpandedFlat @ts

main :: IO ()
main = do
  let f =
        RCons @('From 0 '( 'I 2, 'I 2)) (konst 0.2) $
          RCons @('From 2 '( 'I 2, 'I 2)) (konst 0.3) $
            RCons @('From 4 '( 'I 2, 'I 2)) (konst 0.5) RNil
      outFid = composeHomTrees @('[ 'I 2]) @('[ 'I 2]) @('[ 'I 2]) f (idHomFTrees @('[ 'I 2]))
      outIdf = composeHomTrees @('[ 'I 2]) @('[ 'I 2]) @('[ 'I 2]) (idHomFTrees @('[ 'I 2])) f
  putStrLn $ "f        = " ++ show (flat @(FuseRep '[ 'I 2] '[ 'I 2]) f)
  putStrLn $ "outFid   = " ++ show (flat @(FuseRep '[ 'I 2] '[ 'I 2]) outFid)
  putStrLn $ "outIdf   = " ++ show (flat @(FuseRep '[ 'I 2] '[ 'I 2]) outIdf)
