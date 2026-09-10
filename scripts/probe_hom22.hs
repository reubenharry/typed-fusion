{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

import Data.Complex
import Hom.Core
import Hom.Expr
import Numeric.LinearAlgebra.Static (konst)
import qualified Data.Vector.Storable as VS

flat :: forall ts. KnownFTrees ts => FTreeV ts -> [Complex Double]
flat = VS.toList . fTreeVToExpandedFlat @ts

main :: IO ()
main = do
  let f =
        FCons @('From 0 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.2) $
          FCons @('From 2 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.3) $
            FCons @('From 4 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.5) FNil
      outFid = composeHomTrees @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) f (idHomFTrees @('[ 'IrrepTree 2]))
      outIdf = composeHomTrees @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) (idHomFTrees @('[ 'IrrepTree 2])) f
  putStrLn $ "f        = " ++ show (flat @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) f)
  putStrLn $ "outFid   = " ++ show (flat @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) outFid)
  putStrLn $ "outIdf   = " ++ show (flat @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) outIdf)
