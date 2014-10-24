{- Integers modulo n, dynamically
-}

module Mods0 ( ZMod(..) ) where

type Modulus = Integer

data ZMod = ZMod Integer Modulus
  deriving Show

instance Num ZMod where
  ZMod a m1 + ZMod b m2 | m1 == m2  = ZMod ((a + b) `mod` m1) m1
                        | otherwise = badMods m1 m2
  ZMod a m1 * ZMod b m2 | m1 == m2  = ZMod ((a * b) `mod` m1) m1
                        | otherwise = badMods m1 m2
  ZMod a m1 - ZMod b m2 | m1 == m2  = ZMod ((a * b) `mod` m1) m1
                        | otherwise = badMods m1 m2
  negate (ZMod a m) = ZMod (m - a) m
  abs               = id
  signum (ZMod 0 m) = ZMod 0 m
  signum (ZMod _ m) = ZMod 1 m
  fromInteger n     = ZMod (n `mod` defaultModulus) defaultModulus

badMods :: Modulus -> Modulus -> a
badMods m1 m2 = error $ "Different moduli used: " ++
                        show m1 ++ " and " ++ show m2

defaultModulus :: Modulus
defaultModulus = 10
