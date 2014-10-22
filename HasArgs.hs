{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell, DataKinds,
             PolyKinds, GADTs, RankNTypes, MultiParamTypeClasses,
             FlexibleInstances, UndecidableInstances,
             FunctionalDependencies, StandaloneDeriving,
             TypeOperators, ScopedTypeVariables, NoMonomorphismRestriction,
             MonadComprehensions, DeriveGeneric, FlexibleContexts,
             GeneralizedNewtypeDeriving, ConstraintKinds,
             LambdaCase, ViewPatterns, -- AllowAmbiguousTypes,
             DefaultSignatures, --  ImpredicativeTypes, 
             ImplicitParams, MagicHash, UnboxedTuples,
             ExtendedDefaultRules
 #-}

module Scratch where

import Test.QuickCheck
import GHC.Exts

data Nat = Zero | Succ Nat

type family CountArgs fun where
  CountArgs (a -> b) = Succ (CountArgs b)
  CountArgs b        = Zero

data NumArgs :: * -> * where
  NoArgs :: (Eq x) => NumArgs x
  SomeArgs :: (HasArgs (CountArgs y) y) => NumArgs (x -> y)

class CountArgs fun ~ num => HasArgs num fun where
  hasArgs :: fun -> NumArgs fun

instance (CountArgs fun ~ Zero, Eq fun) => HasArgs Zero fun where
  hasArgs _ = NoArgs

instance (CountArgs y ~ n, HasArgs n y) => HasArgs (Succ n) (x -> y) where
  hasArgs _ = SomeArgs

type family Arbs fun where
  Arbs (x -> y) = (Arbitrary x, Arbs y)
  Arbs y        = (() :: Constraint)

(~=~) :: (HasArgs (CountArgs fun) fun, Arbs fun) => fun -> fun -> Property
f ~=~ g = case hasArgs f of
  NoArgs -> property (f == g)
  SomeArgs -> property $ do
    x <- arbitrary
    return (f x ~=~ g x)

splotch :: Int -> Bool -> Char -> String
splotch x y z = show x ++ show y ++ show z

splotch2 :: Int -> Bool -> Char -> String
splotch2 x y z
  | z == 'A'  = ""
  | otherwise = show x ++ show y ++ show z


