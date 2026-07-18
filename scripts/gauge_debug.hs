{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

-- | Isolate which step of 'mixedCanonicalCentre3' breaks the flat tensor.
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Control.Lens ((^.), (&), (.~), _1)
import Data.Complex (Complex, realPart)
import Data.VectorSpace (InnerSpace ((<.>)), (^-^))
import Numeric.LinearAlgebra.Static (C, extract, Sized (fromList))
import Math.LinearMap.Category (getLinearMap, type (+>), (⊗), Tensor (getTensorProduct))
import qualified Numeric.LinearAlgebra as HM

import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
import TensorNetwork.Categorical ((⊗^))

flat :: MPS (C 3) (C 2) 1 -> C 8
flat psi = physical3ToFlat @2 $ toPhysicalMPS hermitianNorm psi

diff :: C 8 -> C 8 -> Double
diff a b = sqrt (realPart ((a ^-^ b) <.> (a ^-^ b)))

main :: IO ()
main = do
  let psi0@(MPS l bulk r) = unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      (mL, lIso) = polarLeftSite l
      (rIso, mR) = polarRightSite r
      f0 = flat psi0

  -- factorization checks at matrix level
  putStrLn $ "‖l − mL∘lIso‖  = " ++ show (HM.norm_2 (HM.flatten (extract (getLinearMap (l ^-^ (mL . lIso))))))
  putStrLn $ "‖r − rIso∘mR‖  = " ++ show (HM.norm_2 (HM.flatten (extract (getLinearMap (r ^-^ (rIso . mR))))))

  -- absorb left factor only
  let centreL = (bulk ^. _1) . (mL ⊗^ Cat.id)
      psiL = MPS lIso (bulk & _1 .~ centreL) r
  putStrLn $ "flat diff after left absorption only  = " ++ show (diff f0 (flat psiL))

  -- absorb right factor only
  let centreR = mR . (bulk ^. _1)
      psiR = MPS l (bulk & _1 .~ centreR) rIso
  putStrLn $ "flat diff after right absorption only = " ++ show (diff f0 (flat psiR))

  -- gauge-move identity in isolation: bulk ∘ (id ⊗^ id) should be a no-op
  let centreId = (bulk ^. _1) . ((Cat.id :: C 3 +> C 3) ⊗^ (Cat.id :: C 2 +> C 2))
      psiId = MPS l (bulk & _1 .~ centreId) r
  putStrLn $ "flat diff with bulk∘(id⊗id)           = " ++ show (diff f0 (flat psiId))

  -- pure gauge move with m = mL: MPS (m∘lIso) bulk r  vs  MPS lIso (bulk∘(m⊗id)) r
  -- (the first equals psi0 since mL∘lIso = l); tested above as psiL

  -- same move but with m on the *left* leg fed to the left site instead:
  let psiAlt = MPS (mL . lIso) bulk r
  putStrLn $ "flat diff MPS(mL∘lIso) vs psi0        = " ++ show (diff f0 (flat psiAlt))

  -- right absorption identity: mR = id check
  let centreIdR = (Cat.id :: C 3 +> C 3) . (bulk ^. _1)
      psiIdR = MPS l (bulk & _1 .~ centreIdR) r
  putStrLn $ "flat diff with id∘bulk                = " ++ show (diff f0 (flat psiIdR))

  -- pointwise sanity: composition and ⊗^ on the centre's operand shapes
  let v = (fromList [1, 2 HM.:+ 1, -3] :: C 3)
      w = (fromList [0.5, 2] :: C 2)
      vw = v ⊗ w
      d3 x y = HM.norm_2 (extract (x ^-^ y) :: HM.Vector (Complex Double))
      composed = (mR . (bulk ^. _1)) $ vw
      stepwise = mR $ ((bulk ^. _1) $ vw)
  putStrLn $ "pointwise ‖(mR∘bulk)x − mR(bulk x)‖   = " ++ show (d3 composed stepwise)
  let lhsT = (bulk ^. _1) . (mL ⊗^ (Cat.id :: C 2 +> C 2)) $ vw
      rhsT = (bulk ^. _1) $ ((mL $ v) ⊗ w)
  putStrLn $ "pointwise ‖bulk((mL⊗id)x) − bulk(mLv⊗w)‖ = " ++ show (d3 lhsT rhsT)

  -- ground truth: bulk = LinearMap (konst 1); on v⊗w it should give
  -- (Σᵢ vᵢ)(Σⱼ wⱼ) in every output slot regardless of index convention.
  putStrLn $ "bulk(v⊗w) direct app     = " ++ show (extract ((bulk ^. _1) $ vw))
  putStrLn $ "  expected all-slots val = " ++ show (HM.sumElements (extract v) * HM.sumElements (extract w))
  -- is (mL ⊗^ id) itself correct pointwise?
  let tApp = (mL ⊗^ (Cat.id :: C 2 +> C 2)) $ vw
      tRef = (mL $ v) ⊗ w
      dT x y = HM.norm_2 (HM.flatten (extract (getTensorProduct (x ^-^ y))))
  putStrLn $ "‖(mL⊗^id)(v⊗w) − (mLv)⊗w‖ = " ++ show (dT tApp tRef)
  -- apply the *composed* map bulk∘(mL⊗^id) to v⊗w and compare to stepwise
  let compApp = ((bulk ^. _1) . (mL ⊗^ (Cat.id :: C 2 +> C 2))) $ vw
      stepApp = (bulk ^. _1) $ tRef
  putStrLn $ "‖(bulk∘(mL⊗id))(v⊗w) − bulk((mLv)⊗w)‖ = " ++ show (d3 compApp stepApp)
  putStrLn $ "composed app  = " ++ show (extract compApp)
  putStrLn $ "stepwise app  = " ++ show (extract stepApp)
  -- and for the right absorption
  putStrLn $ "mR(bulk(v⊗w)) = " ++ show (extract (mR $ ((bulk ^. _1) $ vw)))
  putStrLn $ "(mR∘bulk)(v⊗w)= " ++ show (extract ((mR . (bulk ^. _1)) $ vw))
