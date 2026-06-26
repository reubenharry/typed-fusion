{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | A runtime singleton for a representation spine @'Rep g'@ — a list of
-- @(irrep label, multiplicity)@ sectors. This is the value that label-keyed
-- recursions (composition, application) walk to drive type-family reduction.
--
-- We deliberately avoid @singletons-base@ (and its @Sing@ instances for lists\/
-- tuples); this bespoke spine carries exactly what the recursions need — the
-- irrep singleton and a @KnownNat@ multiplicity witness per sector — and
-- nothing else.
module Symmetry.RepSingleton
  ( SRep(..)
  , KnownRep(..)
  ) where

import GHC.TypeLits (KnownNat)
import Data.Singletons (Sing, SingI, sing)
import Symmetry.Group (Group (..), Rep)
import Symmetry.ChargeEq ()  -- SingI instances for the U(1) charge kind Z

-- | The singleton for a rep spine: one 'Sing' irrep label and a 'KnownNat'
-- multiplicity per sector. Constructors are indexed by @g@ so @'Rep g'@ reduces
-- under pattern matching.
data SRep (g :: Group) (r :: Rep g) where
  SRepNilU1   :: SRep U1 '[]
  SRepNilSU2  :: SRep SU2 '[]
  SRepCons    :: forall z m rs. KnownNat m => Sing z -> SRep U1 rs -> SRep U1 ('(z, m) ': rs)
  SRepConsSU2 :: forall j m rs. (KnownNat j, KnownNat m) => Sing j -> SRep SU2 rs -> SRep SU2 ('(j, m) ': rs)

-- | Materialize the 'SRep' singleton for a statically-known rep.
class KnownRep (g :: Group) (r :: Rep g) where
  repSing :: SRep g r

instance KnownRep U1 '[] where
  repSing = SRepNilU1

instance (SingI z, KnownNat m, KnownRep U1 rs) => KnownRep U1 ('(z, m) ': rs) where
  repSing = SRepCons (sing @z) (repSing @U1 @rs)

instance KnownRep SU2 '[] where
  repSing = SRepNilSU2

instance (SingI j, KnownNat j, KnownNat m, KnownRep SU2 rs) => KnownRep SU2 ('(j, m) ': rs) where
  repSing = SRepConsSU2 (sing @j) (repSing @SU2 @rs)
