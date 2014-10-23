{- An example of how we can use :~: to track types at runtime.
   Copyright (c) 2014 Richard Eisenberg
  -}

{-# LANGUAGE GADTs, TypeOperators #-}

module TyRep where

import Data.Type.Equality

-- Indexed type representation
data TyRep a where
  TyInt    :: TyRep Int
  TyBool   :: TyRep Bool
  TyString :: TyRep String
  TyList   :: TyRep a -> TyRep [a]
  TyArrow  :: TyRep a -> TyRep b -> TyRep (a -> b)

-- Compute equality on types
eq :: TyRep a -> TyRep b -> Maybe (a :~: b)
eq TyInt           TyInt           = return Refl
eq TyBool          TyBool          = return Refl
eq TyString        TyString        = return Refl
eq (TyList t1)     (TyList t2)     = do Refl <- eq t1 t2
                                        return Refl
eq (TyArrow a1 r1) (TyArrow a2 r2) = do Refl <- eq a1 a2
                                        Refl <- eq r1 r2
                                        return Refl
eq _               _               = Nothing

-- Dynamic is a dynamically-typed datum, stored with its type
data Dynamic where
  Dyn :: TyRep a -> a -> Dynamic

-- Apply a dynamically-typed function to an argument, in a type-safe manner
dynApply :: Dynamic -> Dynamic -> Maybe Dynamic
dynApply (Dyn (TyArrow targ tres) a) (Dyn tb b) = do
  Refl <- eq targ tb
  return $ Dyn tres (a b)
dynApply _ _ = Nothing
