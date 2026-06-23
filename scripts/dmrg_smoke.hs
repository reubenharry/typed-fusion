{-# LANGUAGE DataKinds #-}
import Control.Monad.Identity
import System.CPUTime
import TensorNetwork.DMRG.Fixed3

main = do
  t0 <- getCPUTime
  let DmrgResult { dmrgFinalEnergy = e, dmrgSweepEnergies = es } =
        runIdentity $
          dmrg 15 1e-10 (tfimMPO 1 0.7) (sweep solveCenterAt) (seededMPS222 42)
  t1 <- getCPUTime
  putStrLn $ "done in " ++ show ((fromIntegral (t1 - t0) :: Double) / 1e12) ++ "s"
  putStrLn $ "energy=" ++ show e ++ " sweeps=" ++ show (length es)
  mapM_ print es
