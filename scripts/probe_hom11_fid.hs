{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE GADTs #-}

import Data.Complex
import Data.Proxy
import Experiments.Symbolic.Core
import Experiments.Symbolic.Expr
import Experiments.Symbolic.TypeLevel
import GHC.TypeLits (natVal)
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static (konst)
import qualified Data.Vector.Storable as VS

dumpTrees
  :: forall ts
   . KnownRep ts
  => String
  -> RepV ts
  -> IO ()
dumpTrees label tv = do
  putStrLn $ "=== " ++ label ++ " ==="
  go 0 (repSing @ts) tv
  where
    go :: Int -> SRep ts' -> RepV ts' -> IO ()
    go _ SRepNil RNil = pure ()
    go i (SRepCons t rest) (RCons v rs) = do
      let arr :: VS.Vector (Complex Double)
          arr = case t of
            SI {} -> toArray v
            SFrom {} -> toArray v
          nrm = VS.sum $ VS.map (\x -> realPart (x * conjugate x)) arr
      when (nrm > 1e-20) $
        putStrLn $
          show i ++ ": keep=" ++ show (isCupKeep t)
            ++ " ||v||^2=" ++ show nrm
            ++ "  " ++ showIrrep t
      go (i + 1) rest rs
    go _ _ _ = pure ()

    when b m = if b then m else pure ()

    showIrrep :: forall t. SIrrepTree t -> String
    showIrrep (SI @j) = "L" ++ show (natVal (Proxy @j))
    showIrrep (SFrom @j l r) =
      "N" ++ show (natVal (Proxy @j))
        ++ "(" ++ showIrrep l ++ "," ++ showIrrep r ++ ")"

    isCupKeep :: forall t. SIrrepTree t -> Bool
    isCupKeep (SFrom @_ @_ @_ _ r) = case r of
      SFrom @_ @_ @_ mid _ -> case mid of
        SFrom @m _ _ -> natVal (Proxy @m) == 0
        SI {} -> False
      SI {} -> False
    isCupKeep _ = False

f11 :: RepV Hom11
f11 =
  RCons @('From 0 '( 'I 1, 'I 1)) (konst 0.3) $
    RCons @('From 2 '( 'I 1, 'I 1)) (konst 0.7) RNil

main :: IO ()
main = do
  let domFid = fuseRepTerm @Hom11 @Hom11 f11 (idHomI @1)
      outerFid = fmoveOuterHom @I1 @I1 @I1 domFid
      cupFid = fmoveInnerHom @I1 @I1 @I1 outerFid
      outFid =
        unitorHom @I1 @I1
          (cupTensorIdHom @I1 @I1 @I1 cupFid)
  dumpTrees @(FuseRep Hom11 Hom11) "Hom11 dom Fid" domFid
  dumpTrees "Hom11 outer Fid" outerFid
  dumpTrees "Hom11 cupR Fid" cupFid
  putStrLn $ "outFid flat = " ++ show (VS.toList (repVToExpandedFlat @Hom11 outFid))
  putStrLn $ "f11 flat    = " ++ show (VS.toList (repVToExpandedFlat @Hom11 f11))
