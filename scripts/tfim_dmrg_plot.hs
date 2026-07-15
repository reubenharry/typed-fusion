{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
-- | Run DMRG on the 8-site TFIM and write an SVG energy-vs-sweep plot.
--
--   cabal run tfim-dmrg-plot
--   open plots/tfim8_energy.svg
module Main where

import Control.Monad.Identity (runIdentity)
import TensorNetwork.DMRG.Fixed
  ( DmrgResult (..)
  , denseGroundEnergyChain
  , dmrg
  , energy
  , sweep
  , solveCenterAt
  , seededMPSChain
  , tfimMPOChain
  )

type BulkSites = 6  -- bulk sites → 8 sites total

main :: IO ()
main = do
  let j = 1.0
      h = 0.7
      nSites = 8
      maxSweeps = 15
      tol = 1e-10
      mpo = tfimMPOChain @BulkSites j h
      psi0 = seededMPSChain @2 @BulkSites 42
  putStrLn "Computing exact ground energy..."
  let eGround = denseGroundEnergyChain mpo
  putStrLn "Computing initial energy..."
  let eInitial = energy mpo psi0
  putStrLn "Running DMRG on 8-site TFIM..."
  let DmrgResult { dmrgSweepEnergies = sweepEs, dmrgFinalEnergy = finalE } =
        runIdentity $
          dmrg maxSweeps tol mpo (sweep solveCenterAt) psi0
      energies = eInitial : sweepEs
  putStrLn $
    unlines
      [ "TFIM 8-site DMRG (J=" ++ show j ++ ", h=" ++ show h ++ ")"
      , "Exact ground energy: " ++ show eGround
      , "Initial energy: " ++ show eInitial
      , "Sweeps completed: " ++ show (length sweepEs)
      , "Final energy: " ++ show finalE
      , "Energy trace:"
      ]
  mapM_ (\(i, e) -> putStrLn ("  sweep " ++ show i ++ ": " ++ show e))
    (zip [0 :: Int ..] energies)
  let svgPath = "plots/tfim8_energy.svg"
  writeEnergyPlot svgPath j h nSites eGround energies
  putStrLn ("Wrote " ++ svgPath)

-- | Minimal line chart as SVG (no extra plotting dependencies).
writeEnergyPlot :: FilePath -> Double -> Double -> Int -> Double -> [Double] -> IO ()
writeEnergyPlot path j h nSites eGround energies =
  writeFile path (renderEnergySvg j h nSites eGround energies)

renderEnergySvg :: Double -> Double -> Int -> Double -> [Double] -> String
renderEnergySvg _j _h _nSites _eGround [] = error "renderEnergySvg: no data points"
renderEnergySvg j h nSites eGround energies =
  let width = 900 :: Int
      height = 520
      margin = 70
      plotW = width - 2 * margin
      plotH = height - 2 * margin
      n = length energies
      eMin = minimum (eGround : energies)
      eMax = maximum (eGround : energies)
      pad = max 1e-12 ((eMax - eMin) * 0.08)
      lo = eMin - pad
      hi = eMax + pad
      xrange = max 1 (n - 1)
      xOf i =
        fromIntegral margin + fromIntegral plotW * fromIntegral i / fromIntegral xrange
      yOf e =
        fromIntegral margin + fromIntegral plotH * (hi - e) / (hi - lo)
      pts =
        unwords
          [ show (xOf i) ++ "," ++ show (yOf e)
          | (i, e) <- zip [0 :: Int ..] energies
          ]
      yGround = yOf eGround
      yTicks = 5
      yTickVals =
        [ lo + (hi - lo) * fromIntegral k / fromIntegral yTicks | k <- [0 .. yTicks] ]
      xLabel = "DMRG sweep (0 = initial)"
      yLabel = "Energy  ⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩"
      title =
        "TFIM ground-state search ("
          ++ show nSites
          ++ " sites, J="
          ++ show j
          ++ ", h="
          ++ show h
          ++ ")"
      groundLabel =
        "E₀ = " ++ showRounded 6 eGround
  in unlines
       [ "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
       , "<svg xmlns=\"http://www.w3.org/2000/svg\""
       , "     width=\"" ++ show width ++ "\" height=\"" ++ show height ++ "\""
       , "     viewBox=\"0 0 " ++ show width ++ " " ++ show height ++ "\">"
       , "<rect width=\"100%\" height=\"100%\" fill=\"#fafafa\"/>"
       , "<text x=\"" ++ show (width `div` 2) ++ "\" y=\"28\""
       , "      text-anchor=\"middle\" font-family=\"sans-serif\" font-size=\"18\">"
       , title
       , "</text>"
       , axis margin (height - margin) (width - margin) (height - margin)
       , gridLines margin plotW plotH yTickVals lo hi
       , "<line x1=\"" ++ show margin ++ "\" y1=\"" ++ show yGround ++ "\""
       , "      x2=\"" ++ show (margin + plotW) ++ "\" y2=\"" ++ show yGround ++ "\""
       , "      stroke=\"#dc2626\" stroke-width=\"1.5\" stroke-dasharray=\"8,5\"/>"
       , "<text x=\"" ++ show (margin + plotW - 8) ++ "\" y=\"" ++ show (yGround - 8) ++ "\""
       , "      text-anchor=\"end\" font-family=\"sans-serif\" font-size=\"12\" fill=\"#dc2626\">"
       , groundLabel
       , "</text>"
       , "<polyline fill=\"none\" stroke=\"#2563eb\" stroke-width=\"2.5\""
       , "          points=\"" ++ pts ++ "\"/>"
       , pointDots energies xOf yOf
       , yAxisLabels margin plotH yTickVals lo hi
       , xAxisLabels margin plotW plotH n
       , "<text x=\"" ++ show (width `div` 2) ++ "\" y=\"" ++ show (height - 18) ++ "\""
       , "      text-anchor=\"middle\" font-family=\"sans-serif\" font-size=\"14\">"
       , xLabel
       , "</text>"
       , "<text x=\"18\" y=\"" ++ show (height `div` 2) ++ "\""
       , "      transform=\"rotate(-90 18 " ++ show (height `div` 2) ++ ")\""
       , "      text-anchor=\"middle\" font-family=\"sans-serif\" font-size=\"14\">"
       , yLabel
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

yAxisLabels :: Int -> Int -> [Double] -> Double -> Double -> String
yAxisLabels margin plotH ticks lo hi =
  unlines
    [ "<text x=\"" ++ show (margin - 10) ++ "\" y=\"" ++ show y ++ "\""
        ++ " text-anchor=\"end\" dominant-baseline=\"middle\""
        ++ " font-family=\"sans-serif\" font-size=\"12\">"
        ++ showTick e ++ "</text>"
    | e <- ticks
    , let y = fromIntegral margin + fromIntegral plotH * (hi - e) / (hi - lo)
    ]

xAxisLabels :: Int -> Int -> Int -> Int -> String
xAxisLabels margin plotW plotH n
  | n <= 0 = ""
  | otherwise =
      let lastIdx = n - 1
          step = max 1 (lastIdx `div` 8)
          indices = takeWhile (<= lastIdx) (0 : iterate (+ step) step)
      in unlines
           [ "<text x=\"" ++ show x ++ "\" y=\"" ++ show (margin + plotH + 22) ++ "\""
               ++ " text-anchor=\"middle\" font-family=\"sans-serif\" font-size=\"12\">"
               ++ show i ++ "</text>"
           | i <- indices
           , let x = fromIntegral margin + fromIntegral plotW * fromIntegral i / fromIntegral (max 1 lastIdx)
           ]

pointDots :: [Double] -> (Int -> Double) -> (Double -> Double) -> String
pointDots energies xOf yOf =
  unlines
    [ "<circle cx=\"" ++ show (xOf i) ++ "\" cy=\"" ++ show (yOf e) ++ "\""
        ++ " r=\"3.5\" fill=\"#1d4ed8\"/>"
    | (i, e) <- zip [0 :: Int ..] energies
    ]

showTick :: Double -> String
showTick x
  | abs x >= 100 || abs x < 1e-3 = show x
  | otherwise = showRounded 4 x

showRounded :: Int -> Double -> String
showRounded n x =
  let factor = 10 ^ n
  in show (fromIntegral (round (x * factor) :: Integer) / factor :: Double)
