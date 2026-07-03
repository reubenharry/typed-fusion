import TensorNetwork.MPS.Fixed3General (diagnoseExampleMPSInnerC22, exampleMPSInnerC22)

main :: IO ()
main = do
  diagnoseExampleMPSInnerC22
  putStrLn $ "⟨ψ|ψ⟩ = " ++ show exampleMPSInnerC22
