{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | Growable-bond three-site MPS/MPO (transfer orientation, 'FinSuppSeq' bulk bonds).
--
-- Module layout mirrors 'TensorNetwork.MPS.Fixed3':
--
--   * 'TensorNetwork.MPS.FinSupp3.Internal' — core types
--   * 'TensorNetwork.MPS.FinSupp3.Bond' — bond support / padding helpers
--   * 'TensorNetwork.MPS.FinSupp3.VectorSpace' — state addition
--   * 'TensorNetwork.MPS.FinSupp3.Physical' — flatten / encode / 'HasBasis'
--   * 'TensorNetwork.MPS.FinSupp3.Reference' — coefficient oracles
--   * 'TensorNetwork.MPS.FinSupp3.MPO' — operators, 'composeMPO', 'mpoApplyMPS'
--   * 'TensorNetwork.MPS.FinSupp3.Properties' — QuickCheck
module TensorNetwork.MPS.FinSupp3
  ( module TensorNetwork.MPS.FinSupp3.Internal
  , module TensorNetwork.MPS.FinSupp3.Bond
  , module TensorNetwork.MPS.FinSupp3.VectorSpace
  , module TensorNetwork.MPS.FinSupp3.Physical
  , module TensorNetwork.MPS.FinSupp3.Reference
  , module TensorNetwork.MPS.FinSupp3.MPO
  , module TensorNetwork.MPS.FinSupp3.Properties
  ) where

import TensorNetwork.MPS.FinSupp3.InnerSpace ()
import TensorNetwork.MPS.FinSupp3.Internal
import TensorNetwork.MPS.FinSupp3.Bond
import TensorNetwork.MPS.FinSupp3.VectorSpace
import TensorNetwork.MPS.FinSupp3.Physical
import TensorNetwork.MPS.FinSupp3.Reference
import TensorNetwork.MPS.FinSupp3.MPO
import TensorNetwork.MPS.FinSupp3.Properties
