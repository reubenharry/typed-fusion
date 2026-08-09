{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
-- | Run single-site zipper DMRG on an N-site TFIM and plot energy after
-- each local site update (not just per sweep).
--
--   cabal run tfim-dmrg-plot
--   open plots/tfim_nsite_energy.svg
--
-- History length per full sweep (L→R then R→L) is @2·N − 1@ site updates
-- for @N = q + 2@ physical sites (@q@ bulk).
module Main where

import Data.Proxy (Proxy (..))
import GHC.TypeNats (natVal)
import TensorNetwork.DMRG.Fixed
  ( DmrgResult (..)
  , dmrg
  , energy
  , productMPS
  , tfimMPO
  )
import TensorNetwork.MPS.General (hermitianNorm)

-- | Bulk length @q@. Physical sites @N = q + 2@.
type BulkSites = 6  -- → 8 physical sites

main :: IO ()
main = do
  let j = 1.0
      h = 0.7
      q = fromIntegral (natVal (Proxy @BulkSites)) :: Int
      nSites = q + 2
      maxSweeps = 6
      tol = 1e-8
      mpo = tfimMPO @BulkSites j h
      psi0 = productMPS @BulkSites
      nb = hermitianNorm
      np = hermitianNorm
      e0 = energy nb np mpo psi0
      updatesPerSweep = 2 * nSites - 1
  putStrLn $
    unlines
      [ "TFIM zipper DMRG"
      , "  physical sites N = " ++ show nSites ++ " (bulk q = " ++ show q ++ ")"
      , "  bond χ = 3, physical p = 2"
      , "  site updates / full sweep (L→R then R→L) = " ++ show updatesPerSweep
      , "  J = " ++ show j ++ ", h = " ++ show h
      , "  initial ⟨H⟩ = " ++ show e0
      , "Running..."
      ]
  let DmrgResult
        { dmrgSweepEnergies = hist
        , dmrgFinalEnergy = finalE
        } = dmrg @3 @2 @BulkSites maxSweeps tol mpo psi0
      energies = e0 : hist
  putStrLn $
    unlines
      [ "  site updates recorded: " ++ show (length hist)
      , "  final ⟨H⟩ = " ++ show finalE
      , "  Δ from initial = " ++ show (finalE - e0)
      ]
  mapM_
    (\(i, e) ->
        putStrLn $
          "  u" ++ show i ++ ": " ++ show e
            ++ sweepMarker updatesPerSweep i)
    (zip [0 :: Int ..] energies)
  let svgPath = "plots/tfim_nsite_energy.svg"
  writeEnergyPlot svgPath j h nSites updatesPerSweep energies
  putStrLn ("Wrote " ++ svgPath)

sweepMarker :: Int -> Int -> String
sweepMarker ups i
  | i == 0 = "  (initial)"
  | (i - 1) `mod` ups == ups - 1 = "  ← end of sweep " ++ show (((i - 1) `div` ups) + 1)
  | otherwise = ""

--------------------------------------------------------------------------------
-- SVG
--------------------------------------------------------------------------------

writeEnergyPlot :: FilePath -> Double -> Double -> Int -> Int -> [Double] -> IO ()
writeEnergyPlot path j h nSites ups energies =
  writeFile path (renderEnergySvg j h nSites ups energies)

renderEnergySvg :: Double -> Double -> Int -> Int -> [Double] -> String
renderEnergySvg _ _ _ _ [] = error "renderEnergySvg: no data"
renderEnergySvg j h nSites ups energies =
  let width = 960 :: Int
      height = 540
      margin = 70
      plotW = width - 2 * margin
      plotH = height - 2 * margin
      n = length energies
      eMin = minimum energies
      eMax = maximum energies
      pad = max 1e-12 ((eMax - eMin) * 0.08)
      lo = eMin - pad
      hi = eMax + pad
      xrange = max 1 (n - 1)
      xOf i =
        fromIntegral margin
          + fromIntegral plotW * fromIntegral i / fromIntegral xrange
      yOf e =
        fromIntegral margin + fromIntegral plotH * (hi - e) / (hi - lo)
      pts =
        unwords
          [ show (xOf i) ++ "," ++ show (yOf e)
          | (i, e) <- zip [0 :: Int ..] energies
          ]
      -- Vertical lines at end of each full sweep (after the last site update).
      sweepEnds =
        [ i
        | i <- [ups, 2 * ups .. n - 1]
        ]
      yTicks = 5
      yTickVals =
        [ lo + (hi - lo) * fromIntegral k / fromIntegral yTicks | k <- [0 .. yTicks] ]
      title =
        "TFIM single-site DMRG ("
          ++ show nSites
          ++ " sites, χ=3, J="
          ++ show j
          ++ ", h="
          ++ show h
          ++ ") — energy after each site update"
  in unlines
       [ "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
       , "<svg xmlns=\"http://www.w3.org/2000/svg\""
       , "     width=\"" ++ show width ++ "\" height=\"" ++ show height ++ "\""
       , "     viewBox=\"0 0 " ++ show width ++ " " ++ show height ++ "\">"
       , "<rect width=\"100%\" height=\"100%\" fill=\"#fafafa\"/>"
       , "<text x=\"" ++ show (width `div` 2) ++ "\" y=\"28\""
       , "      text-anchor=\"middle\" font-family=\"sans-serif\" font-size=\"16\">"
       , title
       , "</text>"
       , axis margin (height - margin) (width - margin) margin
       , gridLines margin plotW plotH yTickVals lo hi
       , sweepMarkers margin plotW plotH sweepEnds xrange
       , "<polyline fill=\"none\" stroke=\"#2563eb\" stroke-width=\"2\""
       , "          points=\"" ++ pts ++ "\"/>"
       , pointDots energies xOf yOf
       , yAxisLabels margin plotH yTickVals lo hi
       , xAxisLabels margin plotW plotH n
       , "<text x=\"" ++ show (width `div` 2) ++ "\" y=\"" ++ show (height - 18) ++ "\""
       , "      text-anchor=\"middle\" font-family=\"sans-serif\" font-size=\"14\">"
       , "site update index (0 = initial; dashed = end of L→R+R→L sweep)"
       , "</text>"
       , "<text x=\"18\" y=\"" ++ show (height `div` 2) ++ "\""
       , "      transform=\"rotate(-90 18 " ++ show (height `div` 2) ++ ")\""
       , "      text-anchor=\"middle\" font-family=\"sans-serif\" font-size=\"14\">"
       , "Energy  ⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩"
       , "</text>"
       , "</svg>"
       ]

axis :: Int -> Int -> Int -> Int -> String
axis x0 y0 x1 y1 =
  unlines
    [ "<line x1=\"" ++ show x0 ++ "\" y1=\"" ++ show y0 ++ "\""
    , "      x2=\"" ++ show x1 ++ "\" y2=\"" ++ show y1 ++ "\""
    , "      stroke=\"#333\" stroke-width=\"1.5\"/>"
    , "<line x1=\"" ++ show x0 ++ "\" y1=\"" ++ show y0 ++ "\""
    , "      x2=\"" ++ show x0 ++ "\" y2=\"" ++ show y1 ++ "\""
    , "      stroke=\"#333\" stroke-width=\"1.5\"/>"
    ]

gridLines :: Int -> Int -> Int -> [Double] -> Double -> Double -> String
gridLines margin plotW plotH ticks lo hi =
  unlines
    [ "<line x1=\"" ++ show margin ++ "\" y1=\"" ++ show y ++ "\""
        ++ " x2=\"" ++ show (margin + plotW) ++ "\" y2=\"" ++ show y ++ "\""
        ++ " stroke=\"#ddd\" stroke-width=\"1\"/>"
    | e <- ticks
    , let y = fromIntegral margin + fromIntegral plotH * (hi - e) / (hi - lo)
    ]

sweepMarkers :: Int -> Int -> Int -> [Int] -> Int -> String
sweepMarkers margin plotW plotH ends xrange =
  unlines
    [ "<line x1=\"" ++ show x ++ "\" y1=\"" ++ show margin ++ "\""
        ++ " x2=\"" ++ show x ++ "\" y2=\"" ++ show (margin + plotH) ++ "\""
        ++ " stroke=\"#94a3b8\" stroke-width=\"1\" stroke-dasharray=\"4,4\"/>"
    | i <- ends
    , let x =
            fromIntegral margin
              + fromIntegral plotW * fromIntegral i / fromIntegral (max 1 xrange)
    ]

yAxisLabels :: Int -> Int -> [Double] -> Double -> Double -> String
yAxisLabels margin plotH ticks lo hi =
  unlines
    [ "<text x=\"" ++ show (margin - 10) ++ "\" y=\"" ++ show y ++ "\""
        ++ " text-anchor=\"end\" dominant-baseline=\"middle\""
        ++ " font-family=\"sans-serif\" font-size=\"12\">"
        ++ showRounded 4 e ++ "</text>"
    | e <- ticks
    , let y = fromIntegral margin + fromIntegral plotH * (hi - e) / (hi - lo)
    ]

xAxisLabels :: Int -> Int -> Int -> Int -> String
xAxisLabels margin plotW plotH n
  | n <= 0 = ""
  | otherwise =
      let lastIdx = n - 1
          step = max 1 (lastIdx `div` 10)
          indices = takeWhile (<= lastIdx) (0 : iterate (+ step) step)
      in unlines
           [ "<text x=\"" ++ show x ++ "\" y=\"" ++ show (margin + plotH + 22) ++ "\""
               ++ " text-anchor=\"middle\" font-family=\"sans-serif\" font-size=\"12\">"
               ++ show i ++ "</text>"
           | i <- indices
           , let x =
                   fromIntegral margin
                     + fromIntegral plotW * fromIntegral i / fromIntegral (max 1 lastIdx)
           ]

pointDots :: [Double] -> (Int -> Double) -> (Double -> Double) -> String
pointDots energies xOf yOf =
  unlines
    [ "<circle cx=\"" ++ show (xOf i) ++ "\" cy=\"" ++ show (yOf e) ++ "\""
        ++ " r=\"2.5\" fill=\"#1d4ed8\"/>"
    | (i, e) <- zip [0 :: Int ..] energies
    ]

showRounded :: Int -> Double -> String
showRounded n x =
  let factor = 10 ^ n
  in show (fromIntegral (round (x * factor) :: Integer) / factor :: Double)
