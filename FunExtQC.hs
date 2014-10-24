{- Functional extensionality for QuickCheck: compare two functions with
   an arbitrary number of parameters for equality.

   Copyright (c) 2014 Richard Eisenberg
  -}

{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies, GADTs,
             MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
             ConstraintKinds #-}

module FunExtQC where

import Test.QuickCheck
import GHC.Exts        ( Constraint )

-- Need natural numbers again, to count function arguments
data Nat = Zero | Succ Nat

-- Count the number of arguments from a function type
type family CountArgs fun where
  CountArgs (a -> b) = Succ (CountArgs b)
  CountArgs b        = Zero

-- convenient syntax for stating that we know how many args
-- `fun` has:
type FunExt fun = FunExtC (CountArgs fun) fun

-- Use a class so that the number of args can be inferred
class CountArgs fun ~ numArgs => FunExtC numArgs fun where
  eq :: fun -> fun -> Property
instance (CountArgs fun ~ Zero, Eq fun) => FunExtC Zero fun where
  eq f g = property (f == g)
instance (CountArgs y ~ n, FunExtC n y, Arbitrary x, Show x)
           => FunExtC (Succ n) (x -> y) where
  eq f g = property $ do
    x <- arbitrary
    return $ counterexample (show x) $ f x `eq` g x

(=->=) :: FunExt fun => fun -> fun -> Property
(=->=) = eq



-- convenient functions for testing
splotch :: Int -> Bool -> Char -> String
splotch x y z = show x ++ show y ++ show z

splotch2 :: Int -> Bool -> Char -> String
splotch2 x y z
  | x > 10  = ""
  | otherwise = show x ++ show y ++ show z


