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
  -> RepV ts
  -> IO ()
dumpTrees label tv = do
  putStrLn $ "=== " ++ label ++ " ==="
  go 0 (fTreesSing @ts) tv
  where
    go :: Int -> SFTrees ts' -> RepV ts' -> IO ()
    go _ SFTreesNil RNil = pure ()
    go i (SFTreesCons t rest) (RCons v rs) = do
      let arr :: VS.Vector (Complex Double)
          arr = case t of
            SI {} -> toArray v
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
    showFTree (SI @j) = "L" ++ show (natVal (Proxy @j))
    showFTree (SFrom @j l r) =
      "N" ++ show (natVal (Proxy @j))
        ++ "(" ++ showFTree l ++ "," ++ showFTree r ++ ")"

    isCupKeep :: forall t. SFTree t -> Bool
    isCupKeep (SFrom @_ @_ @_ _ r) = case r of
      SFrom @_ @_ @_ mid _ -> case mid of
        SFrom @m _ _ -> natVal (Proxy @m) == 0
        SI {} -> False
      SI {} -> False
    isCupKeep _ = False

f11 :: RepV (FuseRep '[ 'I 1] '[ 'I 1])
f11 =
  RCons @('From 0 '( 'I 1, 'I 1)) (konst 0.3) $
    RCons @('From 2 '( 'I 1, 'I 1)) (konst 0.7) RNil

main :: IO ()
main = do
  let domFid = fuseRepTerm @(FuseRep '[ 'I 1] '[ 'I 1]) @(FuseRep '[ 'I 1] '[ 'I 1]) f11 (idHomFTrees @('[ 'I 1]))
      outerFid = fmoveOuterHom @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) domFid
      cupFid = fmoveInnerHom @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) outerFid
      outFid =
        unitorHom @('[ 'I 1]) @('[ 'I 1])
          (cupTensorIdHom @('[ 'I 1]) @('[ 'I 1]) @('[ 'I 1]) cupFid)
  dumpTrees @(FuseRep (FuseRep '[ 'I 1] '[ 'I 1]) (FuseRep '[ 'I 1] '[ 'I 1])) "Hom11 dom Fid" domFid
  dumpTrees "Hom11 outer Fid" outerFid
  dumpTrees "Hom11 cupR Fid" cupFid
  putStrLn $ "outFid flat = " ++ show (VS.toList (repVToExpandedFlat @(FuseRep '[ 'I 1] '[ 'I 1]) outFid))
  putStrLn $ "f11 flat    = " ++ show (VS.toList (repVToExpandedFlat @(FuseRep '[ 'I 1] '[ 'I 1]) f11))
