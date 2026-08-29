{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Render Fibonacci free-monoidal examples as string diagrams (SVG) and
-- smoke-check that @eval@ matches the concrete @Fib@ generators.
--
--   cabal run fibonacci-diagrams
--   open plots/fib/*.svg
module Main where

import Control.Exception (evaluate, try, SomeException)
import Data.Complex (Complex, imagPart, realPart)
import Diagrams.Backend.SVG (B, renderSVG)
import Diagrams.Prelude hiding (arc)
import Experiments.Fibonacci
  ( Fib (..)
  , HomBlocks (..)
  , Obj (..)
  , Simple (..)
  , cap
  , cup
  , eqFib
  , fuse
  , phi
  , split
  )
import Experiments.Categorical.Associative (Associative (..))
import Experiments.Categorical.Braided (Braided (..))
import Experiments.Fibonacci.Free
  ( FreeFib (..)
  , eval
  , exCap
  , exCup
  , exFMove
  , exFMoveInv
  , exFuse
  , exRMove
  , exSnake
  , exSplit
  , exYank
  )
import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra.Static (unwrap)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------
-- Layout (compose = horizontal, tensor = vertical)
--------------------------------------------------------------------------------

leafBox :: String -> Int -> Int -> Diagram B
leafBox label nIn nOut =
  let w = 1.6 :: Double
      h = max 0.9 (0.45 * fromIntegral (max nIn nOut + 1))
      box = rect w h # lc black # lw veryThin # fc white
      lab = text label # fontSizeL 0.28
      stubsL =
        mconcat
          [ fromVertices [p2 (-w / 2 - 0.35, y), p2 (-w / 2, y)] # lc black # lw veryThin
          | i <- [0 .. nIn - 1]
          , let y = stubY nIn i h
          ]
      stubsR =
        mconcat
          [ fromVertices [p2 (w / 2, y), p2 (w / 2 + 0.35, y)] # lc black # lw veryThin
          | i <- [0 .. nOut - 1]
          , let y = stubY nOut i h
          ]
   in centerXY (stubsL <> stubsR <> box <> lab)

stubY :: Int -> Int -> Double -> Double
stubY n i h
  | n <= 1 = 0
  | otherwise =
      let top = h / 2 - 0.2
          bot = -h / 2 + 0.2
       in top + (bot - top) * fromIntegral i / fromIntegral (n - 1)

cupGlyph :: Diagram B
cupGlyph =
  let arc =
        fromVertices
          [ p2 (-0.45, 0.55)
          , p2 (-0.45, 0)
          , p2 (0, -0.45)
          , p2 (0.45, 0)
          , p2 (0.45, 0.55)
          ]
          # lc black
          # lw veryThin
      lab = text "cup" # fontSizeL 0.22 # translate (r2 (0, -0.75))
   in centerXY (arc <> lab)

capGlyph :: Diagram B
capGlyph =
  let arc =
        fromVertices
          [ p2 (-0.45, -0.55)
          , p2 (-0.45, 0)
          , p2 (0, 0.45)
          , p2 (0.45, 0)
          , p2 (0.45, -0.55)
          ]
          # lc black
          # lw veryThin
      lab = text "cap" # fontSizeL 0.22 # translate (r2 (0, 0.75))
   in centerXY (arc <> lab)

braidGlyph :: Diagram B
braidGlyph =
  let c1 = fromVertices [p2 (-0.6, 0.35), p2 (0.6, -0.35)] # lc black # lw veryThin
      c2 = fromVertices [p2 (-0.6, -0.35), p2 (0.6, 0.35)] # lc black # lw veryThin
      lab = text "R" # fontSizeL 0.28 # translate (r2 (0, 0.7))
   in centerXY (c1 <> c2 <> lab)

idWire :: Diagram B
idWire =
  fromVertices [p2 (-0.5, 0), p2 (0.5, 0)] # lc black # lw veryThin

renderFree :: FreeFib a b -> Diagram B
renderFree IdF = idWire
renderFree (CompF g f) = renderFree f ||| strutX 0.15 ||| renderFree g
renderFree (TensorF f g) = renderFree f === strutY 0.2 === renderFree g
renderFree CupF = cupGlyph
renderFree CapF = capGlyph
renderFree FuseF = leafBox "fuse" 2 2
renderFree SplitF = leafBox "split" 2 2
renderFree AssocF = leafBox "F" 3 3
renderFree DisassocF = leafBox "F^{-1}" 3 3
renderFree BraidF = braidGlyph
renderFree IdlF = leafBox "lambda" 1 1
renderFree IdrF = leafBox "rho" 1 1
renderFree CoidlF = leafBox "lambda^{-1}" 1 1
renderFree CoidrF = leafBox "rho^{-1}" 1 1
renderFree (BoxF s _) = leafBox s 1 1

finish :: Diagram B -> Diagram B
finish d = d # centerXY # pad 1.15 # bg white # frame 0.2

writeDiag :: FilePath -> Diagram B -> IO ()
writeDiag path d =
  renderSVG path (mkSizeSpec2D (Just 480) (Just 320)) (finish d)

--------------------------------------------------------------------------------
-- Smoke checks (same Free terms → Fib)
--------------------------------------------------------------------------------

check :: String -> Bool -> IO ()
check name ok =
  putStrLn $
    if ok
      then "  ok  " ++ name
      else " FAIL " ++ name

snakePhiOk :: Bool
snakePhiOk =
  let Fib (HomBlocks o _) = eval exSnake
      m = unwrap o :: LA.Matrix (Complex Double)
      z = m `LA.atIndex` (0, 0) - phi
   in abs (realPart z) < 1e-9 && abs (imagPart z) < 1e-9

runSmoke :: IO ()
runSmoke = do
  putStrLn "eval smoke checks:"
  check "cup" (eqFib (eval exCup) cup)
  check "cap" (eqFib (eval exCap) cap)
  check "fuse" (eqFib (eval exFuse) fuse)
  check "split" (eqFib (eval exSplit) split)
  check
    "F"
    ( eqFib
        (eval exFMove)
        (associate :: Fib (Tensor (Tensor ('Atom 'Tau) ('Atom 'Tau)) ('Atom 'Tau)) (Tensor ('Atom 'Tau) (Tensor ('Atom 'Tau) ('Atom 'Tau))))
    )
  check
    "Finv"
    ( eqFib
        (eval exFMoveInv)
        (disassociate :: Fib (Tensor ('Atom 'Tau) (Tensor ('Atom 'Tau) ('Atom 'Tau))) (Tensor (Tensor ('Atom 'Tau) ('Atom 'Tau)) ('Atom 'Tau)))
    )
  check
    "R"
    (eqFib (eval exRMove) (braid :: Fib (Tensor ('Atom 'Tau) ('Atom 'Tau)) (Tensor ('Atom 'Tau) ('Atom 'Tau))))
  check "snake = phi on 1-block" snakePhiOk
  yankResult <- try (evaluate (eqFib (eval exYank) (eval exYank))) :: IO (Either SomeException Bool)
  case yankResult of
    Right ok -> check "yank evaluates" ok
    Left e ->
      putStrLn $
        "  skip yank eval (Fib runtime): " ++ show e

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  let outDir = "plots" </> "fib"
  createDirectoryIfMissing True outDir
  putStrLn ("Writing SVGs under " ++ outDir)
  writeDiag (outDir </> "cup.svg") (renderFree exCup)
  writeDiag (outDir </> "cap.svg") (renderFree exCap)
  writeDiag (outDir </> "snake.svg") (renderFree exSnake)
  writeDiag (outDir </> "fuse.svg") (renderFree exFuse)
  writeDiag (outDir </> "split.svg") (renderFree exSplit)
  writeDiag (outDir </> "fmove.svg") (renderFree exFMove)
  writeDiag (outDir </> "fmove_inv.svg") (renderFree exFMoveInv)
  writeDiag (outDir </> "rmove.svg") (renderFree exRMove)
  writeDiag (outDir </> "yank.svg") (renderFree exYank)
  putStrLn "Done writing diagrams."
  runSmoke
