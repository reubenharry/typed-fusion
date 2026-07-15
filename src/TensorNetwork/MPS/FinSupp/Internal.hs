{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | Core types for growable-bond three-site MPS/MPO chains.
--
-- Bulk bonds are 'FinSuppSeq'. Left/right sites use the same transfer /
-- contraction *roles* as 'TensorNetwork.MPS.Fixed', stored in the
-- linearmap-friendly shapes that support growable bonds:
--
--   * left  — @C p +> Bond@       (≅ @(C 1 ⊗ C p) +> Bond@ via the left unitor)
--   * bulk  — @Bond +> (C p ⊗ Bond)@
--   * right — @Bond +> C p@       (≅ @(Bond ⊗ C p) +> C 1@)
module TensorNetwork.MPS.FinSupp.Internal where