module Pratybos.Prat10

import Data.Nat 
import Data.List.Views
import Data.List
import Data.Stream

%default total

everyOther : Stream a -> Stream a
everyOther (x :: y) = x :: everyOther (skipOne y)
  where
    skipOne : Stream a -> Stream a
    skipOne (z :: w) = w

sqrt : (n : Double) -> (a : Double) -> Stream Double
sqrt n a = iterate (\x => (x + a / x) / 2) n
-- sqrt n a = let a' = (n + (a / n)) / 2 in a' :: sqrt a' a

boundedSqrt : (n : Nat) -> (delta : Double) -> (x : Double) -> Double
boundedSqrt 0 delta x = x
boundedSqrt (S k) delta x = findRoot x delta k (sqrt 1 x)
  where
    findRoot : Double -> Double -> Nat -> Stream Double -> Double
    findRoot a _ 0 (x :: y) = x
    findRoot a delta (S k) (x :: y) = case abs (x*x - a) < delta of
                                        False => findRoot a delta k y
                                        True => x

data TrapList : Type -> Type where
  Nil : TrapList a
  (::) : (elem : a) -> Inf (TrapList a) -> TrapList a

countTrap : (x : Nat) -> (n : Nat) -> TrapList Nat
countTrap x n = case isGT x n of
                     (Yes prf) => infiniteList x
                     (No contra) => toN x n
  where
    infiniteList : Nat -> TrapList Nat
    infiniteList k = k :: infiniteList (S k)

    toN : Nat -> Nat -> TrapList Nat
    toN k j = case isLTE k j of
                   (Yes prf) => k :: toN (S k) j
                   (No contra) => Nil

takeFromTrap : (n : Nat) -> (TrapList a) -> List a
takeFromTrap 0 _ = []
takeFromTrap _ [] = []
takeFromTrap (S k) (elem :: elems) = elem :: (takeFromTrap k elems)

