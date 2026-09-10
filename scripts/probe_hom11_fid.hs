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

dumpTrees
  :: forall ts
   . KnownFTrees ts
  => String
  -> FTreeV ts
  -> IO ()
dumpTrees label tv = do
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
      when (nrm > 1e-20) $
        putStrLn $
          show i ++ ": keep=" ++ show (isCupKeep t)
            ++ " ||v||^2=" ++ show nrm
            ++ "  " ++ showFTree t
      go (i + 1) rest rs
    go _ _ _ = pure ()

    when b m = if b then m else pure ()

    showFTree :: forall t. SFTree t -> String
    showFTree (SIrrepTree @j) = "L" ++ show (natVal (Proxy @j))
    showFTree (SFrom @j l r) =
      "N" ++ show (natVal (Proxy @j))
        ++ "(" ++ showFTree l ++ "," ++ showFTree r ++ ")"

    isCupKeep :: forall t. SFTree t -> Bool
    isCupKeep (SFrom @_ @_ @_ _ r) = case r of
      SFrom @_ @_ @_ mid _ -> case mid of
        SFrom @m _ _ -> natVal (Proxy @m) == 0
        SIrrepTree {} -> False
      SIrrepTree {} -> False
    isCupKeep _ = False

f11 :: FTreeV (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])
f11 =
  FCons @('From 0 '( 'IrrepTree 1, 'IrrepTree 1)) (konst 0.3) $
    FCons @('From 2 '( 'IrrepTree 1, 'IrrepTree 1)) (konst 0.7) FNil

main :: IO ()
main = do
  let domFid = fuseFTreesTerm @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) f11 (idHomFTrees @('[ 'IrrepTree 1]))
      outerFid = fmoveOuterHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) domFid
      cupFid = fmoveInnerHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) outerFid
      outFid =
        unitorHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1])
          (cupTensorIdHom @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) @('[ 'IrrepTree 1]) cupFid)
  dumpTrees @(FuseFTrees (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) (FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1])) "Hom11 dom Fid" domFid
  dumpTrees "Hom11 outer Fid" outerFid
  dumpTrees "Hom11 cupR Fid" cupFid
  putStrLn $ "outFid flat = " ++ show (VS.toList (fTreeVToExpandedFlat @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) outFid))
  putStrLn $ "f11 flat    = " ++ show (VS.toList (fTreeVToExpandedFlat @(FuseFTrees '[ 'IrrepTree 1] '[ 'IrrepTree 1]) f11))
