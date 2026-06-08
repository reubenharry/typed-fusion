{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | A runtime singleton for a representation spine @[(Z, Nat)]@ — a list of
-- @(charge, multiplicity)@ sectors. This is the value that the charge-keyed
-- recursions (composition, application) walk to drive type-family reduction.
--
-- We deliberately avoid @singletons-base@ (and its @Sing@ instances for lists\/
-- tuples); this bespoke spine carries exactly what the recursions need — the
-- charge singleton and a @KnownNat@ multiplicity witness per sector — and
-- nothing else.
module RepSingleton
  ( SRep(..)
  , KnownRep(..)
  ) where

import GHC.TypeLits (Nat, KnownNat)
import Data.Singletons (Sing, SingI, sing)
import Utils (Z)
import ChargeEq ()  -- SingI instances for the charge kind Z

-- | The singleton for a rep spine: one 'Sing' charge and a 'KnownNat'
-- multiplicity per sector.
data SRep (r :: [(Z, Nat)]) where
  SRepNil  :: SRep '[]
  SRepCons :: forall z m rs. KnownNat m => Sing z -> SRep rs -> SRep ('(z, m) ': rs)

-- | Materialize the 'SRep' singleton for a statically-known rep.
class KnownRep (r :: [(Z, Nat)]) where
  repSing :: SRep r

instance KnownRep '[] where
  repSing = SRepNil

instance (SingI z, KnownNat m, KnownRep rs) => KnownRep ('(z, m) ': rs) where
  repSing = SRepCons (sing @z) (repSing @rs)
