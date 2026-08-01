{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

-- | Probe: does groundState write-back of left/right sites still poison envs?
--
--   cabal run boundary-solve-probe
import Control.Exception (SomeException, evaluate, try)
import Control.Lens ((^.))
import System.Exit (exitFailure, exitSuccess)
import TensorNetwork.DMRG.Env (leftEnvAfterLeft, rightEnvAfterRight)
import TensorNetwork.DMRG.Fixed
  ( energy, productMPS, solveLeft, solveRight, tfimMPO )
import TensorNetwork.MPS.General
  ( hermitianNorm, mixedCanonicalCentre3, mpsLeft, mpsRight )

report :: Show a => String -> IO a -> IO (Maybe a)
report label action = do
  putStrLn ("== " ++ label ++ " ==")
  r <- try (action >>= evaluate)
  case r of
    Left (ex :: SomeException) -> do
      putStrLn ("  CRASH: " ++ show ex)
      pure Nothing
    Right a -> do
      putStrLn ("  OK: " ++ show a)
      pure (Just a)

-- main :: IO ()
-- main = do
--   let nb = hermitianNorm
--       np = hermitianNorm
--       mpo = tfimMPO @1 1 0.7
--       psi0 = mixedCanonicalCentre3 (productMPS @1)

--   mE0 <- report "energy(psi0)" $
--     pure (energy nb np mpo psi0)

--   mLeft <- report "solveLeft write-back + energy" $ do
--     let (_e, psiL) = solveLeft @3 @2 @1 nb np mpo psi0
--         eL = energy nb np mpo psiL
--         !_ = leftEnvAfterLeft nb np psiL mpo
--         !_ = rightEnvAfterRight nb np psiL mpo
--         !_ = psiL ^. mpsLeft
--     pure eL

  -- mRight <- report "solveRight write-back + energy" $ do
  --   let (_e, psiR) = solveRight @3 @2 @1 nb np mpo psi0
  --       eR = energy nb np mpo psiR
  --       !_ = leftEnvAfterLeft nb np psiR mpo
  --       !_ = rightEnvAfterRight nb np psiR mpo
  --       !_ = psiR ^. mpsRight
  --   pure eR

  -- mBoth <- report "solveLeft then solveRight + energy" $ do
  --   let (_, psiL) = solveLeft @3 @2 @1 nb np mpo psi0
  --       (_, psiLR) = solveRight @3 @2 @1 nb np mpo psiL
  --   pure (energy nb np mpo psiLR)

  -- putStrLn ""
  -- putStrLn "Summary:"
  -- putStrLn ("  E0          = " ++ show mE0)
  -- putStrLn ("  after left  = " ++ show mLeft)
  -- putStrLn ("  after right = " ++ show mRight)
  -- putStrLn ("  after both  = " ++ show mBoth)

  -- case (mE0, mLeft, mRight, mBoth) of
  --   (Just e0, Just eL, Just eR, Just eLR) -> do
  --     putStrLn ("  Δ left  = " ++ show (eL - e0))
  --     putStrLn ("  Δ right = " ++ show (eR - e0))
  --     putStrLn ("  Δ both  = " ++ show (eLR - e0))
  --     putStrLn "Boundary write-back did not crash; envs rebuild."
  --     exitSuccess
  --   _ -> do
  --     putStrLn "Boundary write-back still obstructed (crash)."
  --     exitFailure
