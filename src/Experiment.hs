
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}

module Experiment where

import Data.Kind (Type)
import GHC.TypeLits

import Data.Kind

import GHC.TypeLits
import Data.Kind
import Data.Data (Proxy(..))


-- {-# LANGUAGE DataKinds, GADTs, PolyKinds, TypeOperators, TypeFamilies #-}
-- {-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
-- {-# LANGUAGE ScopedTypeVariables, UndecidableInstances, AllowAmbiguousTypes #-}
-- {-# LANGUAGE TypeApplications, StandaloneDeriving #-}

import GHC.TypeLits
import Data.Proxy
import Data.Type.Equality (type (==))

data Ix = Ix Symbol Nat

data Fin (n :: Nat) where
  Fin :: Int -> Fin n

deriving instance Show (Fin n)

data Assignment (xs :: [Ix]) where
  ANil  :: Assignment '[]
  ACons :: Fin n -> Assignment xs -> Assignment ('Ix name n ': xs)

infixr 5 `ACons`

deriving instance Show (Assignment xs)

newtype AutoTensorFun (xs :: [Ix]) a =
  AutoTensorFun { runAutoTensorFun :: Assignment xs -> a }

-- newtype AutoTensorArr (xs :: [Ix]) a =
--   AutoTensorArr { runAutoTensorArr :: Assignment xs -> a }

type family If (b :: Bool) (t :: k) (f :: k) :: k where
  If 'True  t f = t
  If 'False t f = f

type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

type family ElemName (name :: Symbol) (xs :: [Ix]) :: Bool where
  ElemName name '[] = 'False
  ElemName name ('Ix name n ': xs) = 'True
  ElemName name (_ ': xs) = ElemName name xs

type family Difference (xs :: [Ix]) (ys :: [Ix]) :: [Ix] where
  Difference '[] ys = '[]
  Difference ('Ix name n ': xs) ys =
    If (ElemName name ys)
       (Difference xs ys)
       ('Ix name n ': Difference xs ys)

type family Intersection (xs :: [Ix]) (ys :: [Ix]) :: [Ix] where
  Intersection '[] ys = '[]
  Intersection ('Ix name n ': xs) ys =
    If (ElemName name ys)
       ('Ix name n ': Intersection xs ys)
       (Intersection xs ys)

type family Contracted (xs :: [Ix]) (ys :: [Ix]) :: [Ix] where
  Contracted xs ys =
    Difference xs ys ++ Difference ys xs

class AllAssignments (xs :: [Ix]) where
  allAssignments :: [Assignment xs]

instance AllAssignments '[] where
  allAssignments = [ANil]

instance
  (KnownNat n, AllAssignments xs)
  => AllAssignments ('Ix name n ': xs) where
  allAssignments =
    [ Fin i `ACons` rest
    | i <- [0 .. fromIntegral (natVal (Proxy @n)) - 1]
    , rest <- allAssignments @xs
    ]

class Lookup (name :: Symbol) (n :: Nat) (xs :: [Ix]) where
  lookupIx :: Assignment xs -> Fin n

instance
  LookupCons (name == other) name n other m xs
  => Lookup name n ('Ix other m ': xs) where
  lookupIx =
    lookupCons @(name == other) @name @n @other @m @xs

class LookupCons
  (matches :: Bool)
  (name    :: Symbol)
  (n       :: Nat)
  (other   :: Symbol)
  (m       :: Nat)
  (xs      :: [Ix]) where
  lookupCons :: Assignment ('Ix other m ': xs) -> Fin n

instance LookupCons 'True name n name n xs where
  lookupCons (x `ACons` _) = x

instance
  Lookup name n xs
  => LookupCons 'False name n other m xs where
  lookupCons (_ `ACons` xs) =
    lookupIx @name @n xs

class Build (target :: [Ix]) (out :: [Ix]) (shared :: [Ix]) where
  build :: Assignment out -> Assignment shared -> Assignment target

instance Build '[] out shared where
  build _ _ = ANil

instance
  BuildCons (ElemName name out) name n xs out shared
  => Build ('Ix name n ': xs) out shared where
  build = buildCons @(ElemName name out) @name @n @xs @out @shared

class BuildCons
  (inOut :: Bool)
  (name :: Symbol)
  (n :: Nat)
  (xs :: [Ix])
  (out :: [Ix])
  (shared :: [Ix]) where
  buildCons :: Assignment out -> Assignment shared -> Assignment ('Ix name n ': xs)

instance
  (Lookup name n out, Build xs out shared)
  => BuildCons 'True name n xs out shared where
  buildCons out shared =
    ACons (lookupIx @name @n out) (build @xs out shared)

instance
  (Lookup name n shared, Build xs out shared)
  => BuildCons 'False name n xs out shared where
  buildCons out shared =
    ACons (lookupIx @name @n shared) (build @xs out shared)

(@), contract
  :: forall xs ys.
     ( AllAssignments (Intersection xs ys)
     , Build xs (Contracted xs ys) (Intersection xs ys)
     , Build ys (Contracted xs ys) (Intersection xs ys)
     , NoDups xs
     , NoDups ys
     )
  => AutoTensorFun xs Double
  -> AutoTensorFun ys Double
  -> AutoTensorFun (Contracted xs ys) Double
contract (AutoTensorFun f) (AutoTensorFun g) =
  AutoTensorFun $ \out ->
    sum
      [ f (build @xs out shared)
      * g (build @ys out shared)
      | shared <- allAssignments @(Intersection xs ys)
      ]

class ShowAssignment (xs :: [Ix]) where
  showAssignment :: Assignment xs -> [Int]

instance ShowAssignment '[] where
  showAssignment ANil = []

instance ShowAssignment xs
  => ShowAssignment ('Ix name n ': xs) where

  showAssignment (Fin i `ACons` xs) =
    i : showAssignment xs

tensorToList
  :: forall xs a.
     (AllAssignments xs, ShowAssignment xs)
  => AutoTensorFun xs a
  -> [([Int], a)]

tensorToList (AutoTensorFun f) =
  [ (showAssignment asgn, f asgn)
  | asgn <- allAssignments @xs
  ]

class TensorShape (xs :: [Ix]) where
  tensorShape :: [Int]

instance TensorShape '[] where
  tensorShape = []

instance
  ( KnownNat n
  , TensorShape xs
  ) => TensorShape ('Ix name n ': xs) where

  tensorShape =
    fromIntegral (natVal (Proxy @n))
      : tensorShape @xs

showAutoTensorFun
  :: forall xs.
     ( AllAssignments xs
     , ShowAssignment xs
     , TensorShape xs
     )
  => AutoTensorFun xs Double
  -> String

showAutoTensorFun t =
  unlines
    [ show ix ++ " -> " ++ show val
    | (ix, val) <- tensorToList t
    ]

type family Assert (b :: Bool) (msg :: ErrorMessage) :: Constraint where
  Assert 'True  msg = ()
  Assert 'False msg = TypeError msg

type family NoDups (xs :: [Ix]) :: Constraint where
  NoDups '[] = ()
  NoDups ('Ix name n ': xs) =
    ( Assert
        (Not (ElemName name xs))
        ('Text "Duplicate AutotensorFun index: " ':<>: 'Text name)
    , NoDups xs
    )

type family Not (b :: Bool) :: Bool where
  Not 'True  = 'False
  Not 'False = 'True

mkAutoTensorFun
  :: NoDups xs
  => (Assignment xs -> a)
  -> AutoTensorFun xs a
mkAutoTensorFun = AutoTensorFun


-- bondDim :: Nat 
-- bondDim = 2

-- MPS ket
a1 :: AutoTensorFun '[ 'Ix "p1" 3, 'Ix "b1" 2] Double
a1 = mkAutoTensorFun $ \_ -> 1.0  
a2 :: AutoTensorFun '[ 'Ix "b1" 2, 'Ix "p2" 3, 'Ix "b2" 2] Double
a2 = mkAutoTensorFun $ \_ -> 2.0
a3 :: AutoTensorFun '[ 'Ix "b2" 2, 'Ix "p3" 3] Double
a3 = mkAutoTensorFun $ \_ -> 3.0

a1' :: AutoTensorFun '[ 'Ix "p1" 3, 'Ix "b1'" 2] Double
a1' = mkAutoTensorFun $ \_ -> 1.0  
a2' :: AutoTensorFun '[ 'Ix "b1'" 2, 'Ix "p2" 3, 'Ix "b2'" 2] Double
a2' = mkAutoTensorFun $ \_ -> 2.0
a3' :: AutoTensorFun '[ 'Ix "b2'" 2, 'Ix "p3" 3] Double
a3' = mkAutoTensorFun $ \_ -> 3.0

-- -- MPS bra, with primed physical/bond legs
-- A1' :: AutoTensorFun '[Ix "s1" p', B1'] Double
-- A2' :: AutoTensorFun '[B1', S2', B2'] Double
-- A3' :: AutoTensorFun '[B2', S3'] Double

-- MPO
-- w1 :: AutoTensorFun '[Ix "s1'" p, Ix "s1'" p, W1] Double

-- w2 :: AutoTensorFun '[W1, S2', S2, W2] Double
-- w3 :: AutoTensorFun '[W2, S3', S3] Double

(@) = contract

experiment = a3' @ a3 @ a2' @ a2 @ a1 @ a1'


type I = 'Ix "i" 2
type J = 'Ix "j" 3
type K = 'Ix "k" 4

-- a :: AutoTensorFun '[I, J] Double
-- a = mkAutoTensorFun $ \_ -> 1.0

b :: AutoTensorFun '[J, I,K] Double
b = mkAutoTensorFun $ \_ -> 2.0

a :: AutoTensorFun '[I, J] Double
a = AutoTensorFun $ \(Fin i `ACons` Fin j `ACons` ANil) ->
  fromIntegral (10*i + j)

-- c :: AutoTensorFun '[I, 'Ix "l" 5, K] Double
-- c :: AutoTensorFun ['Ix "i" 2, 'Ix "l" 5, 'Ix "k" 4] Double
c = contract a b








---------------------------------------------------------------
-- Representation descriptions
--------------------------------------------------------------------------------

-- type Irrep = Nat

-- data Representation (r :: [(Irrep, Nat)])

-- --------------------------------------------------------------------------------
-- -- Your statically sized matrix type
-- --------------------------------------------------------------------------------

-- -- data M (n :: Nat) (m :: Nat)

-- -- deriving instance Show (M n m)

-- --------------------------------------------------------------------------------
-- -- One intertwiner block
-- --------------------------------------------------------------------------------

-- -- irrep i
-- -- m copies in domain
-- -- n copies in codomain
-- --
-- -- Matrix shape:
-- --   n x m
-- --
-- newtype Block
--   (i :: Irrep)
--   (m :: Nat)
--   (n :: Nat)
--   = Block (M n m)

-- deriving instance Show (M n m) => Show (Block i m n)

-- --------------------------------------------------------------------------------
-- -- HList
-- --------------------------------------------------------------------------------

-- data HList (xs :: [Type]) where
--   HNil :: HList '[]
--   (:&) :: x -> HList xs -> HList (x ': xs)

-- infixr 5 :&

-- deriving instance Show (HList '[])

-- deriving instance
--   (Show x, Show (HList xs))
--   => Show (HList (x ': xs))

-- --------------------------------------------------------------------------------
-- -- Type-level lookup
-- --------------------------------------------------------------------------------

-- type family Lookup
--   (i :: Irrep)
--   (r :: [(Irrep, Nat)])
--   :: Maybe Nat where

--   Lookup i '[] =
--     'Nothing

--   Lookup i ('(i, n) ': rs) =
--     'Just n

--   Lookup i ('(j, n) ': rs) =
--     Lookup i rs

-- --------------------------------------------------------------------------------
-- -- Conditionally add a block
-- --------------------------------------------------------------------------------

-- type family AddBlock
--   (i :: Irrep)
--   (m :: Nat)
--   (found :: Maybe Nat)
--   (rest :: [Type])
--   :: [Type] where

--   AddBlock i m 'Nothing rest =
--     rest

--   AddBlock i m ('Just n) rest =
--     Block i m n ': rest

-- --------------------------------------------------------------------------------
-- -- Compute all intertwiner blocks
-- --------------------------------------------------------------------------------

-- type family ToMapList
--   (r :: [(Irrep, Nat)])
--   (q :: [(Irrep, Nat)])
--   :: [Type] where

--   ToMapList '[] q =
--     '[]

--   ToMapList ('(i, m) ': rs) q =
--     AddBlock
--       i
--       m
--       (Lookup i q)
--       (ToMapList rs q)

-- --------------------------------------------------------------------------------
-- -- Concrete intertwiner type
-- --------------------------------------------------------------------------------

-- newtype Intertwiner
--   (r :: [(Irrep, Nat)])
--   (q :: [(Irrep, Nat)])
--   =
--   Intertwiner
--     (HList (ToMapList r q))

-- deriving instance
--   Show (HList (ToMapList r q))
--   => Show (Intertwiner r q)


-- type S =
--   '[ '(1,1)
--    , '(2,2)
--    ]

-- type Q =
--   '[ '(1,1)
--    , '(2,1)
--    ]

-- f :: Intertwiner S Q
-- f = undefined
-- --   Intertwiner
-- --     ( Block undefined
-- --    :& Block undefined
-- --    :& HNil
-- --     )