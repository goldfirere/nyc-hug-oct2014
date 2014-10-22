-- A type of a list that is statically known to be in non-decreasing order.

{-# LANGUAGE PolyKinds, DataKinds, TypeOperators, TypeFamilies, GADTs,
             TemplateHaskell, ScopedTypeVariables, UndecidableInstances,
             FlexibleContexts, ConstraintKinds, EmptyCase,
             StandaloneDeriving #-}

module OrdList where

import Data.Singletons.TH          hiding ( POrd(..) )
import Data.Singletons.Prelude     hiding ( POrd(..), SOrd(..)
                                          , MinSym0, MinSym1, MinSym2 )
import Data.Singletons.TypeLits

import Test.QuickCheck
import Control.Applicative

import GHC.TypeLits
import Unsafe.Coerce

------------------------------------------------------
-- Comparison
------------------------------------------------------

-- Type-level comparison:
type family Compare (a :: k) (b :: k) :: Ordering

-- Singleton comparison:
class (kproxy ~ 'KProxy, SEq kproxy) => SOrd (kproxy :: KProxy k) where
  -- comparison operation
  sCompare :: forall (a :: k) (b :: k).
              Sing a -> Sing b -> Sing (Compare a b)

  -- If the comparison returns equal, then the comparees are really equal
  compare_eq :: forall (a :: k) (b :: k).
                Compare a b ~ EQ => Sing a -> Sing b -> a :~: b

  -- We must know transitivity.
  compare_trans_lt :: forall (a :: k) (b :: k) (c :: k).
                      (Compare a b ~ LT, Compare b c ~ LT)
                   => Sing a -> Sing b -> Sing c
                   -> Compare a c :~: LT

  compare_trans_gt :: forall (a :: k) (b :: k) (c :: k).
                      (Compare a b ~ GT, Compare b c ~ GT)
                   => Sing a -> Sing b -> Sing c
                   -> Compare a c :~: GT

  -- Comparison can be reorderd sanely
  compare_anti_lt :: forall (a :: k) (b :: k).
                     Compare a b ~ LT => Sing a -> Sing b -> Compare b a :~: GT

  compare_anti_gt :: forall (a :: k) (b :: k).
                     Compare a b ~ GT => Sing a -> Sing b -> Compare b a :~: LT

-- convenient notation:
type a < b = (Compare a b ~ LT)
type a :<: b = (Compare a b :~: LT)
       
-- take the minimum of two type-level values
type Min a b = IfLT (Compare a b) a b

type family IfLT ord x y where
  IfLT LT x y = x
  IfLT z  x y = y

$(genDefunSymbols [''Min])

sMin :: forall (a :: k) (b :: k).
        SOrd ('KProxy :: KProxy k)
     => Sing a -> Sing b -> Sing (Min a b)
sMin a b = case sCompare a b of
  SLT -> a
  SEQ -> b
  SGT -> b

-- Proof that if a < b and a < c, then a < Min b c
le_min :: (SOrd (KindOf a), a < b, a < c)
       => Sing a -> Sing b -> Sing c -> a :<: Min b c
le_min _ b c = case sCompare b c of
  SLT -> Refl
  SEQ -> Refl
  SGT -> Refl

------------------------------------------------------
-- Unary natural numbers
------------------------------------------------------
       
$(singletons [d|
  -- unary natural numbers
  data Nat1 = Zero | Succ Nat1
    deriving (Eq)
  |])

-- Convenient notation
type family U (n :: Nat) :: Nat1 where
  U 0 = Zero
  U n = Succ (U (n-1))

-- Comparison for unary Nats
type instance Compare Zero     Zero     = EQ
type instance Compare (Succ n) Zero     = GT
type instance Compare Zero     (Succ n) = LT
type instance Compare (Succ n) (Succ m) = Compare n m

instance SOrd ('KProxy :: KProxy Nat1) where
  sCompare SZero     SZero     = SEQ
  sCompare (SSucc _) SZero     = SGT
  sCompare SZero     (SSucc _) = SLT
  sCompare (SSucc n) (SSucc m) = sCompare n m

  compare_eq SZero     SZero = Refl
  compare_eq (SSucc n) (SSucc m) = case compare_eq n m of Refl -> Refl
  -- compare_eq (SSucc _) SZero = bugInGHC
  -- compare_eq SZero (SSucc _) = bugInGHC
  compare_eq _         _         = bugInGHC

  compare_trans_lt SZero     _         (SSucc _) = Refl
  compare_trans_lt (SSucc a) (SSucc b) (SSucc c)
    = case compare_trans_lt a b c of Refl -> Refl
  compare_trans_lt _ _ _ = bugInGHC

  compare_trans_gt (SSucc _) _         SZero     = Refl
  compare_trans_gt (SSucc a) (SSucc b) (SSucc c)
    = case compare_trans_gt a b c of Refl -> Refl
  compare_trans_gt _ _ _ = bugInGHC

  compare_anti_lt SZero (SSucc _) = Refl
  compare_anti_lt (SSucc n) (SSucc m)
    = case compare_anti_lt n m of Refl -> Refl
  compare_anti_lt _ _ = bugInGHC

  compare_anti_gt (SSucc _) SZero = Refl
  compare_anti_gt (SSucc n) (SSucc m)
    = case compare_anti_gt n m of Refl -> Refl
  -- compare_anti_gt SZero SZero = bugInGHC
  -- compare_anti_gt SZero (SSucc _) = bugInGHC
  compare_anti_gt SZero _ = bugInGHC

fromNat1 :: Nat1 -> Integer
fromNat1 Zero     = 0
fromNat1 (Succ n) = succ (fromNat1 n)

toNat1 :: Integer -> Nat1
toNat1 n = case compare n 0 of
  LT -> error "No negative naturals!"
  EQ -> Zero
  GT -> Succ (toNat1 (n-1))
               
instance Show Nat1 where
  show = show . fromNat1

-- Use the derived instance for Ord
deriving instance Ord Nat1

instance Arbitrary Nat1 where
  arbitrary = toNat1 . getNonNegative <$> arbitrary
  shrink    = map (toNat1 . getNonNegative) . shrink . NonNegative . fromNat1

------------------------------------------------------
-- TypeLit Nats
------------------------------------------------------

type instance Compare a b = CmpNat a b

assumption :: a :~: b
assumption = unsafeCoerce Refl

instance SOrd ('KProxy :: KProxy Nat) where
  sCompare a b = case compare (fromSing a) (fromSing b) of
    LT -> unsafeCoerce SLT
    EQ -> unsafeCoerce SEQ
    GT -> unsafeCoerce SGT

  compare_eq      _ _    = assumption
  compare_trans_lt _ _ _ = assumption
  compare_trans_gt _ _ _ = assumption
  compare_anti_lt _ _    = assumption
  compare_anti_gt _ _    = assumption

------------------------------------------------------
-- Adding a Top value of a type, greater than all others
------------------------------------------------------
 
$(singletons [d|
  data WithTop a = Value a | Top
    deriving (Eq)
  |])

-- type-level comparison of WithTop
type instance Compare (Value a) (Value b) = Compare a b
type instance Compare (Value a) Top       = LT
type instance Compare Top       (Value b) = GT
type instance Compare Top       Top       = EQ

-- singletons comparison of WithTop
instance SOrd ('KProxy :: KProxy k)
               => SOrd ('KProxy :: KProxy (WithTop k)) where
  sCompare (SValue a) (SValue b) = sCompare a b
  sCompare (SValue _) STop       = SLT
  sCompare STop       (SValue _) = SGT
  sCompare STop       STop       = SEQ

  compare_eq (SValue a) (SValue b) = case compare_eq a b of Refl -> Refl
  compare_eq STop       STop       = Refl
  -- compare_eq (SValue _) STop       = bugInGHC
  -- compare_eq STop       (SValue _) = bugInGHC
  compare_eq _          _          = bugInGHC

  compare_trans_lt (SValue _) _          STop       = Refl
  compare_trans_lt (SValue a) (SValue b) (SValue c)
    = case compare_trans_lt a b c of Refl -> Refl
  compare_trans_lt _ _ _ = bugInGHC

  compare_trans_gt STop       _          (SValue _) = Refl
  compare_trans_gt (SValue a) (SValue b) (SValue c)
    = case compare_trans_gt a b c of Refl -> Refl
  compare_trans_gt _ _ _ = bugInGHC

  compare_anti_lt (SValue _) STop       = Refl
  compare_anti_lt (SValue a) (SValue b)
    = case compare_anti_lt a b of Refl -> Refl
  compare_anti_lt _ _ = bugInGHC

  compare_anti_gt (SValue a) (SValue b)
    = case compare_anti_gt a b of Refl -> Refl
  compare_anti_gt STop       (SValue _) = Refl
  -- compare_anti_gt (SValue _) STop       = bugInGHC
  -- compare_anti_gt STop       STop       = bugInGHC
  compare_anti_gt _          _          = bugInGHC

------------------------------------------------------
-- An ordered list
------------------------------------------------------

-- An OrdList is indexed by its first element, which is necessarily
-- its minimum element. Anything consed onto the list must then be
-- smaller.
data OrdList :: WithTop k -> * where
  Nil   :: OrdList Top
  (:::) :: (Value e1 < e2) => Sing e1 -> OrdList e2 -> OrdList (Value e1)
infixr 5 :::

sZero  = sing :: Sing (U 0)
sOne   = sing :: Sing (U 1)
sTwo   = sing :: Sing (U 2)
sThree = sing :: Sing (U 3)

ol = sZero ::: sThree ::: Nil
-- bad_ol = sOne ::: sZero ::: Nil

-- Retrieve a singleton representing the lower bound of an OrdList
singBound :: OrdList a -> Sing a
singBound Nil       = sing        -- or, equivalently, STop
singBound (a ::: _) = SValue a

------------------------------------------------------
-- Dependently-typed merge sort
------------------------------------------------------

-- Merge two OrdLists.
merge :: forall (a_top :: WithTop k)
                (b_top :: WithTop k).
         SOrd ('KProxy :: KProxy k)
      => OrdList a_top -> OrdList b_top -> OrdList (Min a_top b_top)
merge Nil        Nil        = Nil
merge Nil        (b ::: bs) = b ::: bs
merge (a ::: as) Nil        = a ::: as
merge (a ::: as) (b ::: bs) =
  case sCompare a b of
     -- here, we have to show that (a < bound as) and (a < b) implies
     -- that (a < bound (merge as (b ::: bs))). le_min does the job.
    SLT -> case le_min (SValue a) (singBound as) (SValue b) of
             Refl -> a ::: merge as (b ::: bs)
     -- here, we first need to show that a ~ b. Then, we can learn
     -- that (a < bound bs), and use that fact, along with (a < bound as)
     -- to show that (a < bound (merge as bs)).
    SEQ -> case compare_eq a b of
             Refl -> case le_min (SValue a) (singBound as) (singBound bs) of
               Refl -> a ::: merge as bs
     -- we know that (a > b). But everything is phrased in terms of (<),
     -- so we use compare_anti_gt to get (b < a) from (a > b), and then
     -- proceed like the SLT case.
    SGT -> case compare_anti_gt a b of
             Refl -> case le_min (SValue b) (SValue a) (singBound bs) of
               Refl -> b ::: merge (a ::: as) bs

-- Some basic functions we'll need on singletons
$(singletons [d|
  -- like Data.List's 'minimum', but it can handle the empty list
  minimum :: Ord a => a -> [a] -> a
  minimum a [] = a
  minimum a (b:bs) = min a (minimum b bs)

  -- Like the 'minimum' function, but returns Top for the empty list
  -- This uses the Minimum function from the Data.Promotion.Prelude.List module
  minimumWithTop :: Ord a => [a] -> WithTop a
  minimumWithTop []     = Top
  minimumWithTop (a:as) = Value (minimum a as)
              
  split :: [a] -> ([a], [a])
  split [] = ([], [])
  split [a] = ([a], [])
  split (a:b:rest) =
    let (as, bs) = split rest in
    (a:as, b:bs)
  |])

-- Some lemmas needed for toOrdList:

-- `min` is associative
min_assoc :: forall (a :: k) (b :: k) (c :: k).
             SOrd ('KProxy :: KProxy k)
          => Sing a -> Sing b -> Sing c -> Min (Min a b) c :~: Min a (Min b c)
min_assoc a b c
  = case (sCompare a b, sCompare a c, sCompare b c) of
      (SLT, SLT, SLT) -> Refl
      (SLT, SLT, SEQ) -> Refl
      (SLT, SLT, SGT) -> Refl
      (SLT, SEQ, SLT) -> case compare_eq a c of Refl -> Refl
      (SLT, SEQ, SEQ) -> Refl
      (SLT, SEQ, SGT) -> Refl
      (SLT, SGT, SLT) -> case compare_trans_lt a b c of {}
      (SLT, SGT, SEQ) -> Refl
      (SLT, SGT, SGT) -> Refl
      (SEQ, SLT, SLT) -> Refl
      (SEQ, SLT, SEQ) -> case compare_eq a b of {}
      (SEQ, SLT, SGT) -> case compare_eq a b of {}
      (SEQ, SEQ, SLT) -> Refl
      (SEQ, SEQ, SEQ) -> Refl
      (SEQ, SEQ, SGT) -> Refl
      (SEQ, SGT, SLT) -> Refl
      (SEQ, SGT, SEQ) -> Refl
      (SEQ, SGT, SGT) -> Refl
      (SGT, SLT, SLT) -> Refl
      (SGT, SLT, SEQ) -> case compare_eq b c of {} 
      (SGT, SLT, SGT) -> case compare_trans_gt a b c of {}
      (SGT, SEQ, SLT) -> Refl
      (SGT, SEQ, SEQ) -> Refl
      (SGT, SEQ, SGT) -> Refl
      (SGT, SGT, SLT) -> Refl
      (SGT, SGT, SEQ) -> Refl
      (SGT, SGT, SGT) -> Refl

-- `min` is commutative
min_comm :: forall (a :: k) (b :: k).
            SOrd ('KProxy :: KProxy k)
         => Sing a -> Sing b -> Min a b :~: Min b a
min_comm a b
  = case (sCompare a b, sCompare b a) of
      (SLT, SLT) -> case compare_anti_lt a b of {}
      (SLT, SEQ) -> Refl
      (SLT, SGT) -> Refl
      (SEQ, SLT) -> Refl
      (SEQ, SEQ) -> case compare_eq a b of Refl -> Refl
      (SEQ, SGT) -> case compare_eq a b of {}
      (SGT, SLT) -> Refl
      (SGT, SEQ) -> case compare_eq b a of {}
      (SGT, SGT) -> case compare_anti_gt a b of {}

-- minimum of values is the value of the minimum
min_value_swap :: forall (a :: k) (b :: k).
                  SOrd ('KProxy :: KProxy k)
               => Sing a -> Sing b
               -> Min (Value a) (Value b) :~: Value (Min a b)
min_value_swap a b = case sCompare a b of
  SLT -> Refl
  SEQ -> Refl
  SGT -> Refl

-- splitting preserves minima
split_min :: forall (elts :: [k]) (bs :: [k]) (cs :: [k]).
             ( SOrd ('KProxy :: KProxy k)
             , '(bs, cs) ~ Split elts )
          => Sing elts
          -> Min (MinimumWithTop bs) (MinimumWithTop cs) :~: MinimumWithTop elts
split_min SNil = Refl
split_min (_ `SCons` SNil) = Refl
split_min (a `SCons` (b `SCons` rest))
  = case sSplit rest of
      STuple2 xs ys ->
        case ( split_min rest
             , min_value_swap (sMinimum a xs) (sMinimum b ys) ) of
          (Refl, Refl) -> case (xs, ys, rest) of
            (SNil, SNil, SNil) -> Refl
            -- (SNil, SNil, SCons _ _) -> Refl
            -- (_, SCons _ _, SNil) -> Refl
            (SNil, SCons _ _, SCons _ _) -> Refl
            -- (SCons _ _, _, SNil) -> Refl
            (SCons _ _, SNil, SCons r rs) ->
              case ( min_assoc a (sMinimum r rs) b
                   , min_comm b (sMinimum r rs) ) of
                (Refl, Refl) -> Refl
            (SCons x1 x1s, SCons y1 y1s, SCons _ _) ->
              case ( min_value_swap (sMinimum x1 x1s) (sMinimum y1 y1s)
                   , min_assoc a (sMinimum x1 x1s) (sMin b (sMinimum y1 y1s))
                   , min_assoc (sMinimum x1 x1s) b (sMinimum y1 y1s)
                   , min_comm b (sMinimum x1 x1s)
                   , min_assoc b (sMinimum x1 x1s) (sMinimum y1 y1s) ) of
                (Refl, Refl, Refl, Refl, Refl) -> Refl
            _ -> bugInGHC

-- Now, we can convert an ordinary singleton list into an ordered one.
-- This is the heart of mergesort.
toOrdList :: forall (elts :: [k]).
             SOrd ('KProxy :: KProxy k)
          => SList elts -> OrdList (MinimumWithTop elts)
toOrdList SNil = Nil
toOrdList (a `SCons` SNil) = a ::: Nil
toOrdList as = case sSplit as of
  STuple2 bs cs -> case split_min as of
    Refl -> merge (toOrdList bs) (toOrdList cs)

-- Convert an OrdList into an ordinary, non-singleton list.
-- The SingKind class provides the key fromSing function, used below.
fromOrdList :: forall (e :: WithTop k).
               (SingKind ('KProxy :: KProxy k))
            => OrdList e -> [DemoteRep ('KProxy :: KProxy k)]
fromOrdList Nil        = []
fromOrdList (a ::: as) = fromSing a : fromOrdList as

-- Interface to mergeSort. Because we don't have kind families, we
-- must explicitly name the promoted version of the type we're working
-- with.
mergeSort :: forall proxy_a a.
             ( proxy_a ~ ('KProxy :: KProxy a_pro)
             , SingKind proxy_a
             , a ~ DemoteRep proxy_a
             , SOrd proxy_a ) =>
             Proxy proxy_a -> [a] -> [a]
mergeSort _ ls = case toSing ls :: SomeSing ('KProxy :: KProxy [a_pro]) of
  SomeSing sls -> fromOrdList (toOrdList sls)

-- Convenient specializations
mergeSortIntegers :: [Integer] -> [Integer]
mergeSortIntegers = mergeSort (Proxy :: Proxy ('KProxy :: KProxy Nat))

mergeSortNats :: [Nat1] -> [Nat1]
mergeSortNats = mergeSort (Proxy :: Proxy ('KProxy :: KProxy Nat1))

