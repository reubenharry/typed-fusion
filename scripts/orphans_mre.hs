{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Minimal examples of suspected linearmap-hmatrix (C / R orphans) bugs.
-- No MPS / quantum network code — only library primitives.
--
-- Run:  cabal exec -- runghc scripts/orphans_mre.hs
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Data.Complex (Complex ((:+)), realPart)
import Data.VectorSpace ((^-^), InnerSpace ((<.>)))
import Numeric.LinearAlgebra.Static (C, M, R, L, Sized (fromList, extract))
import Math.LinearMap.Category
  ( type (+>), type (-+>), type (⊗), (⊗)
  , LinearMap (LinearMap)
  , TensorSpace (transposeTensor), (-+$>)
  , tensorOfMaps
  , FiniteDimensional (entireBasis, recomposeSB)
  , SubBasis
  )
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static.Orphans ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Control.Exception (evaluate, try, SomeException)

e0c, e1c :: C 2
e0c = fromList [1, 0]
e1c = fromList [0, 1]

e0r, e1r :: R 2
e0r = fromList [1, 0]
e1r = fromList [0, 1]

fC :: C 2 +> C 2
fC = LinearMap (fromList [1, 2, 3, 4] :: M 2 2)

fR :: R 2 +> R 2
fR = LinearMap (fromList [1, 2, 3, 4] :: L 2 2)

idC2 :: C 2 +> C 2
idC2 = arr (Cat.id :: C 2 -+> C 2)

idR2 :: R 2 +> R 2
idR2 = arr (Cat.id :: R 2 -+> R 2)

diffC :: (C 2 ⊗ C 2) -> (C 2 ⊗ C 2) -> Double
diffC a b = sqrt (realPart ((a ^-^ b) <.> (a ^-^ b)))

diffR :: (R 2 ⊗ R 2) -> (R 2 ⊗ R 2) -> Double
diffR a b = sqrt ((a ^-^ b) <.> (a ^-^ b))

diffV :: C 2 -> C 2 -> Double
diffV a b = sqrt (realPart ((a ^-^ b) <.> (a ^-^ b)))

ok :: Bool -> String
ok True = "OK"
ok False = "FAIL"

section :: String -> IO ()
section s = putStrLn ("\n==== " ++ s ++ " ====")

bug1 :: IO ()
bug1 = do
  section "1. tensorOfMaps law: (f ⊗^ id)(x⊗y) = (f x) ⊗ y"
  let lhsC = ((tensorOfMaps -+$> fC) -+$> idC2) $ (e0c ⊗ e1c)
      rhsC = (fC $ e0c) ⊗ e1c
      errC = diffC lhsC rhsC
  putStrLn $ "  complex err = " ++ show errC ++ "  " ++ ok (errC < 1e-12)
  let lhsR = ((tensorOfMaps -+$> fR) -+$> idR2) $ (e0r ⊗ e1r)
      rhsR = (fR $ e0r) ⊗ e1r
      errR = diffR lhsR rhsR
  putStrLn $ "  real err    = " ++ show errR ++ "  " ++ ok (errR < 1e-12)

bug2 :: IO ()
bug2 = do
  section "2. composition vs application on tensor-domain maps"
  let k = LinearMap (fromList [1, 2, 3, 4, 5, 6, 7, 8] :: M 4 2) :: (C 2 ⊗ C 2) +> C 2
      g = LinearMap (fromList [0, 1 :+ 1, 1, 0] :: M 2 2) :: C 2 +> C 2
      t = e0c ⊗ e0c
      err = diffV ((g . k) $ t) (g $ (k $ t))
  putStrLn $ "  (g.k) vs g(k t) err = " ++ show err ++ "  " ++ ok (err < 1e-12)
  let idT = arr (Cat.id :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2)) :: (C 2 ⊗ C 2) +> (C 2 ⊗ C 2)
      errId = diffV ((k . idT) $ t) (k $ t)
  putStrLn $ "  (k.id) vs k err     = " ++ show errId ++ "  " ++ ok (errId < 1e-12)

bug3 :: IO ()
bug3 = do
  section "3. arr vs function: transposeTensor / id"
  let mT = arr (transposeTensor :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2))
            :: (C 2 ⊗ C 2) +> (C 2 ⊗ C 2)
      idT = arr (Cat.id :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2))
            :: (C 2 ⊗ C 2) +> (C 2 ⊗ C 2)
      t = e0c ⊗ e1c
      errTr = diffC (mT $ t) (transposeTensor -+$> t)
      errId = diffC (idT $ t) t
  putStrLn $ "  ||arr tr t - tr t|| = " ++ show errTr ++ "  " ++ ok (errTr < 1e-12)
  putStrLn $ "  ||arr id t - t||    = " ++ show errId ++ "  " ++ ok (errId < 1e-12)

bug4 :: IO ()
bug4 = do
  section "4. recomposeSB on (C2⊗C2)+>C2"
  outcome <- try (evaluate $
    let (site, _) =
          recomposeSB (entireBasis :: SubBasis ((C 2 ⊗ C 2) +> C 2))
                      [1, 2, 3, 4, 5, 6, 7, 8 :: Complex Double]
    in extract (site $ (e0c ⊗ e0c)))
  case outcome of
    Left (ex :: SomeException) ->
      putStrLn $ "  CRASH: " ++ show ex
    Right v ->
      putStrLn $ "  OK, site (e0⊗e0) = " ++ show v

sanity :: IO ()
sanity = do
  section "sanity"
  let g = LinearMap (fromList [0, 1 :+ 1, 1, 0] :: M 2 2) :: C 2 +> C 2
      x = fromList [1, 2 :+ 1] :: C 2
      err = diffV ((g . fC) $ x) (g $ (fC $ x))
  putStrLn $ "  plain C→C compose err = " ++ show err ++ "  " ++ ok (err < 1e-12)
  putStrLn $ "  transpose as function err = "
    ++ show (diffC (transposeTensor -+$> (e0c ⊗ e1c)) (e1c ⊗ e0c))
    ++ "  " ++ ok (diffC (transposeTensor -+$> (e0c ⊗ e1c)) (e1c ⊗ e0c) < 1e-12)

main :: IO ()
main = do
  putStrLn "linearmap-hmatrix orphans MREs (no MPS code)"
  sanity
  bug1
  bug2
  bug3
  bug4
  putStrLn ""
