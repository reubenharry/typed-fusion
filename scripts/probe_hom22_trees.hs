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
          desc = showFTree t
          keep = isCupKeep t
      putStrLn $
        show i ++ ": keep=" ++ show keep
          ++ " ||v||^2=" ++ show nrm
          ++ "  " ++ desc
      go (i + 1) rest rs
    go _ _ _ = pure ()

    showFTree :: forall t. SFTree t -> String
    showFTree (SIrrepTree @j) = "Leaf " ++ show (natVal (Proxy @j))
    showFTree (SFrom @j l r) =
      "Node " ++ show (natVal (Proxy @j))
        ++ " (" ++ showFTree l ++ ") (" ++ showFTree r ++ ")"

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
      domIdf = fuseFTreesTerm @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) @(FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) (idHomFTrees @('[ 'IrrepTree 2])) f22
      outerIdf = fmoveOuterHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) domIdf
      cupIdf = fmoveInnerHom @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) @('[ 'IrrepTree 2]) outerIdf
  dumpTrees @(FuseFTrees (FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) (FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2])) "dom Fid (f⊗id)" domFid
  dumpTrees "outer Fid" outerFid
  dumpTrees "cupR Fid (after id⊗F)" cupFid
  putStrLn ""
  dumpTrees @(FuseFTrees (FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2]) (FuseFTrees '[ 'IrrepTree 2] '[ 'IrrepTree 2])) "dom Idf (id⊗f)" domIdf
  dumpTrees "outer Idf" outerIdf
  dumpTrees "cupR Idf (after id⊗F)" cupIdf
