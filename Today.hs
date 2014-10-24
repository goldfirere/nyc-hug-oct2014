{-# LANGUAGE TypeFamilies, GADTs, PolyKinds, DataKinds,
             ScopedTypeVariables, StandaloneDeriving,
             TemplateHaskell, TypeOperators,
             UndecidableInstances #-}

module Today where

import Prelude            hiding ( replicate )
import Data.Singletons.TH
import GHC.TypeLits       ( type (-) )

$(singletons [d|
  data Nat = Zero | Succ Nat
  |])

type family U n where
  U 0 = Zero
  U n = Succ (U (n-1))

data Vec :: * -> Nat -> * where
  Nil   :: Vec a Zero
  (:::) :: a -> Vec a n -> Vec a (Succ n)
infixr 5 :::
deriving instance Show a => Show (Vec a n)

replicate :: forall a n. SingI n => a -> Vec a n
replicate a = case (sing :: Sing n) of
  SZero    -> Nil
  SSucc n' -> a ::: withSingI n' (replicate a)

x3 :: Vec Char (Succ (Succ (Succ Zero)))
x3 = replicate 'x'

$(promote [d|
  foldr :: (a -> b -> b) -> b -> [a] -> b
  foldr _ z []     = z
  foldr f z (x:xs) = f x (foldr f z xs)

  plus :: Nat -> Nat -> Nat
  plus Zero     n = n
  plus (Succ m) n = Succ (m `plus` n)
  |])

data FList :: (k -> *) -> [k] -> * where
  FNil  :: FList f '[]
  FCons :: f h -> FList f t -> FList f (h ': t)

vappend :: Vec a m -> Vec a n -> Vec a (m `Plus` n)
vappend Nil       v = v
vappend (h ::: t) v = h ::: (t `vappend` v)

vconcat :: FList (Vec a) ns -> Vec a (Foldr PlusSym0 Zero ns)
vconcat FNil         = Nil
vconcat (FCons v vs) = v `vappend` vconcat vs
