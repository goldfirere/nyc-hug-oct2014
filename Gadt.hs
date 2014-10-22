{- Basic GADT Example
   Copyright (c) 2014 Richard Eisenberg
-}

{-# LANGUAGE GADTs, TypeFamilies #-}

module Gadt where

-- Pattern-matching on a constructor of `G a` tells us what `a` is!
data G a where
  MkGInt  :: G Int
  MkGBool :: G Bool

match :: G a -> a
match MkGInt  = 5
match MkGBool = False

-- Type families allow us to write functions in types.
type family Frob a where
  Frob Int  = Char
  Frob Bool = ()

frob :: G a -> Frob a
frob MkGInt  = 'x'
frob MkGBool = ()

