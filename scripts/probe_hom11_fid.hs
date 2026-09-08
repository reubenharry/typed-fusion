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
            SBare {} -> toArray v
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
    showIrrep (SBare @j) = "L" ++ show (natVal (Proxy @j))
    showIrrep (SFrom @j l r) =
      "N" ++ show (natVal (Proxy @j))
        ++ "(" ++ showIrrep l ++ "," ++ showIrrep r ++ ")"

    isCupKeep :: forall t. SIrrepTree t -> Bool
    isCupKeep (SFrom @_ @_ @_ _ r) = case r of
      SFrom @_ @_ @_ mid _ -> case mid of
        SFrom @m _ _ -> natVal (Proxy @m) == 0
        SBare {} -> False
      SBare {} -> False
    isCupKeep _ = False

f11 :: RepV Hom11
f11 =
  RCons @('From 0 '( 'Bare 1, 'Bare 1)) (konst 0.3) $
    RCons @('From 2 '( 'Bare 1, 'Bare 1)) (konst 0.7) RNil

main :: IO ()
main = do
  let domFid = fuseRepTerm @Hom11 @Hom11 f11 (idHomBare @1)
      outerFid = fmoveOuterHom @Bare1 @Bare1 @Bare1 domFid
      cupFid = fmoveInnerHom @Bare1 @Bare1 @Bare1 outerFid
      outFid =
        unitorHom @Bare1 @Bare1
          (cupTensorIdHom @Bare1 @Bare1 @Bare1 cupFid)
  dumpTrees @(FuseRep Hom11 Hom11) "Hom11 dom Fid" domFid
  dumpTrees "Hom11 outer Fid" outerFid
  dumpTrees "Hom11 cupR Fid" cupFid
  putStrLn $ "outFid flat = " ++ show (VS.toList (repVToExpandedFlat @Hom11 outFid))
  putStrLn $ "f11 flat    = " ++ show (VS.toList (repVToExpandedFlat @Hom11 f11))
