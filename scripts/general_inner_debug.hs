{-# LANGUAGE TypeApplications #-}
import Control.Exception (evaluate)
import TensorNetwork.MPS.Fixed3General
  ( exampleMPSC22, mpsInner, withMPS3, BulkSite (..) )
import TensorNetwork.Dagger (siteDagger)
import TensorNetwork.MPS.Fixed3.Internal (basis)

main :: IO ()
main = do
  putStrLn "siteDagger bulk..."
  withMPS3 exampleMPSC22 $ \_ (BulkSite b) _ -> do
    let d = siteDagger (bulkLin b)
    evaluate (d $ basis @2 0) >>= print
  putStrLn "full inner..."
  z <- evaluate (mpsInner exampleMPSC22 exampleMPSC22)
  print z
