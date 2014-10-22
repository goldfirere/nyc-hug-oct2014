{- Example of singleton natural numbers, with a proof that addition is
   associative.

   Copyright (c) 2014 Richard Eisenberg
  -}

{-# LANGUAGE DataKinds, KindSignatures, GADTs,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

module Nats where

import Data.Type.Equality
import GHC.TypeLits ( type (-) )
import GHC.Exts     ( Constraint )

-- Regular unary natural numbers.
data Nat = Zero
         | Succ Nat

-- Singleton natural numbers.
data SNat :: Nat -> * where
  SZero :: SNat Zero
  SSucc :: SNat n -> SNat (Succ n)

-- Type level addition
type family n + m where
  Zero      + m = m
  (Succ n') + m = Succ (n' + m)

-- Singleton addition
(%+) :: SNat n -> SNat m -> SNat (n + m)
SZero    %+ m = m
SSucc n' %+ m = SSucc (n' %+ m)
infixl %+

-- Type-level greater-than constraint
type family a > b :: Constraint where
  Zero   > n      = False ~ True
  Succ n > Zero   = ()
  Succ n > Succ m = n > m

-- Implicit singleton naturals
class SNatI (n :: Nat) where
  sNat :: SNat n

instance SNatI Zero where
  sNat = SZero
instance SNatI n => SNatI (Succ n) where
  sNat = SSucc sNat

fromSNat :: SNat n -> Integer
fromSNat SZero     = 0
fromSNat (SSucc n) = succ $ fromSNat n

-- A proof that addition is associative.
plus_assoc :: SNat n -> SNat m -> SNat p -> (n + m) + p :~: n + (m + p)
plus_assoc SZero _ _ = Refl
plus_assoc (SSucc n') m p
  = case plus_assoc n' m p of
      Refl -> Refl

-- Convert TypeLits notation into unary numbers, for convenience
type family U n where
  U 0 = Zero
  U n = Succ (U (n-1))
