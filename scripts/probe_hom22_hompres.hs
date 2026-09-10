{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE GADTs #-}

import Data.Complex
import Data.Proxy
import Hom.Core
import Hom.Expr
import Hom.TypeLevel
import GHC.TypeLits (natVal)
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static (konst)
import qualified Data.Vector.Storable as VS

dumpNZ
  :: forall ts
   . KnownFTrees ts
  => String
  -> FTreeV ts
  -> IO ()
dumpNZ label tv = do
  putStrLn $ "=== " ++ label ++ " ==="
  go 0 (fTreesSing @ts) tv
  where
    go :: Int -> SFTrees ts' -> FTreeV ts' -> IO ()
    go _ SFTreesNil FNil = pure ()
    go i (SFTreesCons t rest) (FCons v rs) = do
      let arr :: VS.Vector (Complex Double)
          arr = case t of
            SIrrepTree {} -> toArray v
            SFrom {} -> toArray v
          nrm = VS.sum $ VS.map (\x -> realPart (x * conjugate x)) arr
      if nrm > 1e-18
        then putStrLn $ show i ++ ": keep=" ++ show (isCupKeep t) ++ " ||v||^2=" ++ show nrm ++ "  " ++ showFTree t
        else pure ()
      go (i + 1) rest rs
    go _ _ _ = pure ()

    showFTree :: forall t. SFTree t -> String
    showFTree (SIrrepTree @j) = "L" ++ show (natVal (Proxy @j))
    showFTree (SFrom @j l r) =
      "N" ++ show (natVal (Proxy @j)) ++ "(" ++ showFTree l ++ "," ++ showFTree r ++ ")"

    isCupKeep :: forall t. SFTree t -> Bool
    isCupKeep (SFrom @_ @_ @_ _ r) = case r of
      SFrom @_ @_ @_ mid _ -> case mid of
        SFrom @m _ _ -> natVal (Proxy @m) == 0
        SIrrepTree {} -> False
      SIrrepTree {} -> False
    isCupKeep _ = False

f22 :: FTreeV (FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2])
f22 =
  FCons @('From 0 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.2) $
    FCons @('From 2 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.3) $
      FCons @('From 4 '( 'IrrepTree 2, 'IrrepTree 2)) (konst 0.5) FNil

main :: IO ()
main = do
  let domFid = fuseFTreesTerm @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) f22 (idHomFTrees @('[ 'IrrepTree 2]))
      outerFid = fmoveOuterHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) domFid
      cupFid = fmoveInnerHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) outerFid
      outFid =
        unitorHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2])
          (cupTensorIdHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) cupFid)
      domIdf = fuseFTreesTerm @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) (idHomFTrees @('[ 'IrrepTree 2])) f22
      outerIdf = fmoveOuterHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) domIdf
      cupIdf = fmoveInnerHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) outerIdf
      outIdf =
        unitorHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2])
          (cupTensorIdHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) cupIdf)
  dumpNZ "outer Fid (Hom-pres)" outerFid
  dumpNZ "cupR Fid" cupFid
  putStrLn $ "outFid = " ++ show (VS.toList (fTreeVToExpandedFlat @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) outFid))
  putStrLn ""
  dumpNZ "outer Idf (Hom-pres)" outerIdf
  dumpNZ "cupR Idf" cupIdf
  putStrLn $ "outIdf = " ++ show (VS.toList (fTreeVToExpandedFlat @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) outIdf))
  putStrLn $ "f22    = " ++ show (VS.toList (fTreeVToExpandedFlat @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) f22))
