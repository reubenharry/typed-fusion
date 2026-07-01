{-# LANGUAGE DataKinds #-}
import Test.QuickCheck (quickCheckWith, stdArgs, maxSuccess)
import TensorNetwork.Categorical.Props
  ( prop_tensorOfMapsActsFactorwise
  , prop_tensorOfMapsActsFactorwiseSiteDomain
  , prop_tensorOfMapsActsFactorwiseLeftFactored
  , prop_tensorOfMapsBasisImages
  , prop_tensorOfMapsRecomposeRoundtrip
  )
import TensorNetwork.MPS.Fixed3
  ( prop_lTensorIdMatchesManual
  , prop_leftTransferMatchesApplySite
  , prop_bulkTransferMatchesApplySite
  , prop_leftBulkTransferMatchesApplySite
  , prop_mpsChainMapMatchesAmplitude
  , prop_mpsChainCloseFlatMatchesReference
  , prop_mpsToFlatMatchesReference
  , prop_innerMatchesReference
  )

devArgs = stdArgs { maxSuccess = 20 }

main :: IO ()
main = do
  putStrLn "tensorOfMaps recompose roundtrip..."
  quickCheckWith devArgs prop_tensorOfMapsRecomposeRoundtrip >>= print . ("tensorRoundtrip",)
  putStrLn "tensorOfMaps basis images..."
  quickCheckWith devArgs prop_tensorOfMapsBasisImages >>= print . ("tensorBasis",)
  putStrLn "tensorOfMaps atomic..."
  quickCheckWith devArgs prop_tensorOfMapsActsFactorwise >>= print . ("tensorAtomic",)
  putStrLn "tensorOfMaps site domain..."
  quickCheckWith devArgs prop_tensorOfMapsActsFactorwiseSiteDomain >>= print . ("tensorSite",)
  putStrLn "tensorOfMaps left-factored..."
  quickCheckWith devArgs prop_tensorOfMapsActsFactorwiseLeftFactored >>= print . ("tensorLeft",)
  mapM_ (\(n, p) -> quickCheckWith devArgs p >>= print . (n,)) $
    [ ("left", prop_leftTransferMatchesApplySite)
    , ("bulk", prop_bulkTransferMatchesApplySite)
    , ("lTensorId", prop_lTensorIdMatchesManual)
    , ("leftBulk", prop_leftBulkTransferMatchesApplySite)
    , ("chainMap", prop_mpsChainMapMatchesAmplitude)
    , ("chainClose", prop_mpsChainCloseFlatMatchesReference)
    , ("mpsToFlat", prop_mpsToFlatMatchesReference)
    , ("inner", prop_innerMatchesReference)
    ]
