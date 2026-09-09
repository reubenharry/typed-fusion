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
  -> RepV ts
  -> IO ()
dumpNZ label tv = do
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
      if nrm > 1e-18
        then putStrLn $ show i ++ ": keep=" ++ show (isCupKeep t) ++ " ||v||^2=" ++ show nrm ++ "  " ++ showFTree t
        else pure ()
      go (i + 1) rest rs
    go _ _ _ = pure ()

    showFTree :: forall t. SFTree t -> String
    showFTree (SI @j) = "L" ++ show (natVal (Proxy @j))
    showFTree (SFrom @j l r) =
      "N" ++ show (natVal (Proxy @j)) ++ "(" ++ showFTree l ++ "," ++ showFTree r ++ ")"

    isCupKeep :: forall t. SFTree t -> Bool
    isCupKeep (SFrom @_ @_ @_ _ r) = case r of
      SFrom @_ @_ @_ mid _ -> case mid of
        SFrom @m _ _ -> natVal (Proxy @m) == 0
        SI {} -> False
      SI {} -> False
    isCupKeep _ = False

f22 :: RepV Hom22
f22 =
  RCons @('From 0 '( 'I 2, 'I 2)) (konst 0.2) $
    RCons @('From 2 '( 'I 2, 'I 2)) (konst 0.3) $
      RCons @('From 4 '( 'I 2, 'I 2)) (konst 0.5) RNil

main :: IO ()
main = do
  let domFid = fuseRepTerm @Hom22 @Hom22 f22 (idHomI @2)
      outerFid = fmoveOuterHom @I2 @I2 @I2 domFid
      cupFid = fmoveInnerHom @I2 @I2 @I2 outerFid
      outFid =
        unitorHom @I2 @I2
          (cupTensorIdHom @I2 @I2 @I2 cupFid)
      domIdf = fuseRepTerm @Hom22 @Hom22 (idHomI @2) f22
      outerIdf = fmoveOuterHom @I2 @I2 @I2 domIdf
      cupIdf = fmoveInnerHom @I2 @I2 @I2 outerIdf
      outIdf =
        unitorHom @I2 @I2
          (cupTensorIdHom @I2 @I2 @I2 cupIdf)
  dumpNZ "outer Fid (Hom-pres)" outerFid
  dumpNZ "cupR Fid" cupFid
  putStrLn $ "outFid = " ++ show (VS.toList (repVToExpandedFlat @Hom22 outFid))
  putStrLn ""
  dumpNZ "outer Idf (Hom-pres)" outerIdf
  dumpNZ "cupR Idf" cupIdf
  putStrLn $ "outIdf = " ++ show (VS.toList (repVToExpandedFlat @Hom22 outIdf))
  putStrLn $ "f22    = " ++ show (VS.toList (repVToExpandedFlat @Hom22 f22))
