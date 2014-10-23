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
type KnownArgs fun = NumArgsC (CountArgs fun) fun

-- A GADT tracking the number of arguments a function type has
data NumArgsG :: * -> * where
  NoArgs   :: Eq x => NumArgsG x    -- Eq x, because the result must be in Eq
  SomeArgs :: KnownArgs y => NumArgsG (x -> y)

-- Use a class so that the number of args can be inferred
class CountArgs fun ~ num => NumArgsC num fun where
  numArgs :: fun -> NumArgsG fun
instance (CountArgs fun ~ Zero, Eq fun) => NumArgsC Zero fun where
  numArgs _ = NoArgs
instance (CountArgs y ~ n, NumArgsC n y) => NumArgsC (Succ n) (x -> y) where
  numArgs _ = SomeArgs

-- Map a class constraint over the args to a function
type family MapClassArgs cls fun_ty :: Constraint where
  MapClassArgs cls (a -> b) = (cls a, MapClassArgs cls b)
  MapClassArgs cls b        = ()

-- Functional extensionality for QuickCheck
(~=~) :: ( KnownArgs fun
         , MapClassArgs Arbitrary fun
         , MapClassArgs Show fun )
      => fun -> fun -> Property
f ~=~ g = case numArgs f of
  NoArgs -> property (f == g)         -- base case
  SomeArgs -> property $ do           -- recursive case
    x <- arbitrary
    return (counterexample (show x) $
            f x ~=~ g x)
infix 4 ~=~


-- convenient functions for testing
splotch :: Int -> Bool -> Char -> String
splotch x y z = show x ++ show y ++ show z

splotch2 :: Int -> Bool -> Char -> String
splotch2 x y z
  | x > 10  = ""
  | otherwise = show x ++ show y ++ show z


