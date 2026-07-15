{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Hilbert-space adjoint (†) for finite-dimensional complex spaces.
--
-- @dagger f@ is the conjugate transpose: 'conjugateMap' composed with
-- 'transposeMap' (categorical adjoint on self-dual spaces).
--
-- 'siteDagger' is the MPS-site bra pullback in transfer orientation. The
-- categorical definition flattens the tensor domain to a self-dual
-- 'ApplicationFlat' space (resolving @DualVector (bl ⊗ phys) ≠ bl ⊗ phys@ at
-- the type level), applies 'dagger', then unflattens:
--
-- @siteDagger f = isoInv ∘ dagger (f ∘ isoInv)@
--
-- The only type-specific hook is 'ApplicationTensorIso'.
module TensorNetwork.Dagger where