{- Integers modulo n
-}

{-# LANGUAGE DataKinds, KindSignatures, ScopedTypeVariables, GADTs,
             TypeOperators, ConstraintKinds, UndecidableInstances #-}

module Mods where

import Nats

newtype ZMod (n :: Nat) = ZMod Integer
  deriving Show

instance (n > Zero, SNatI n) => Num (ZMod n) where
  (ZMod a) + (ZMod b) = ZMod $ (a + b) `mod` fromSNat (sNat :: SNat n)
  (ZMod a) * (ZMod b) = ZMod $ (a * b) `mod` fromSNat (sNat :: SNat n)
  (ZMod a) - (ZMod b) = ZMod $ (a * b) `mod` fromSNat (sNat :: SNat n)
  negate (ZMod a) = ZMod $ fromSNat (sNat :: SNat n) - a
  abs = id
  signum (ZMod 0) = 0
  signum _        = ZMod 1
  fromInteger n = ZMod $ n `mod` fromSNat (sNat :: SNat n)
