{-# LANGUAGE DependentTypes, StandaloneDeriving #-}

module Tomorrow where

import Prelude hiding ( replicate )

data Vec :: U -> Integer -> U where
  Nil   :: Vec a 0
  (:::) :: a -> Vec a n -> Vec a (1 + n)
infixr 5 :::
deriving instance Show a => Show (Vec a n)

replicate :: pi n. forall a. a -> Vec a n
replicate @0 _ = Nil
replicate    x = x ::: replicate x

x3 :: Vec Char 3
x3 = replicate 'x'

data FList :: (k -> U) -> [k] -> U where
  FNil  :: FList f '[]
  FCons :: f h -> FList f t -> FList f (h ': t)

vappend :: Vec a m -> Vec a n -> Vec a (m '+ n)
vappend Nil       v = v
vappend (h ::: t) v = h ::: (t `vappend` v)

vconcat :: FList (Vec a) ns -> Vec a ('foldr '(+) 0 ns)
vconcat VLNil         = Nil
vconcat (VLCons v vs) = v `vappend` vconcat vs
