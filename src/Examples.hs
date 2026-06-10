-- printSeededMPSInner :: IO ()
-- printSeededMPSInner = do
--   let psi = unGen genMPS222 (mkQCGen 42) 30
--   let mpo = unGen genMPO222 (mkQCGen 42) 30
--   putStrLn ("<MPS | MPS> = " ++ show (mpsInner psi psi))
--   putStrLn ("<MPS | MPO | MPS> = " ++ show (mpsInner psi (mpoApplyMPS mpo psi)))

--great example of types!