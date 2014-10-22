{- Integers modulo n, with TypeLits
-}

{-# LANGUAGE KindSignatures, DataKinds, ScopedTypeVariables, TypeOperators,
             TypeFamilies #-}

module Mods2 where

import GHC.TypeLits
import Data.Proxy

newtype ZMod (n :: Nat) = ZMod Integer
  deriving Show

instance (1 <= n, KnownNat n) => Num (ZMod n) where
  (ZMod a) + (ZMod b) = ZMod $ (a + b) `mod` natVal (Proxy :: Proxy n)
  (ZMod a) * (ZMod b) = ZMod $ (a * b) `mod` natVal (Proxy :: Proxy n)
  (ZMod a) - (ZMod b) = ZMod $ (a * b) `mod` natVal (Proxy :: Proxy n)
  negate (ZMod a) = ZMod $ natVal (Proxy :: Proxy n) - a
  abs = id
  signum (ZMod 0) = 0
  signum _        = ZMod 1
  fromInteger n = ZMod $ n `mod` natVal (Proxy :: Proxy n)
