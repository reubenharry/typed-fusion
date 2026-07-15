{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
import TensorNetwork.MPS.FinSupp

main :: IO ()
main = do
  mapM_ (\(s1,s2,s3) -> do
    let m = productMPSAtIndices @2 s1 s2 s3
        flat = mpsToFlat m
    putStrLn $ show (s1,s2,s3) ++ " -> " ++ show flat
    ) [(s1,s2,s3) | s1<-[0,1], s2<-[0,1], s3<-[0,1]]
