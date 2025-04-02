module Pratybos.Prat9

import Data.Nat 
import Data.List.Views
import Data.List

%default total

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | (SplitRecOne x) = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lefts rights lrec rrec) = 
    merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

data TakeN : List a -> Type where
  Fewer : (xs : List a) -> TakeN xs
  Exact : (n_xs : List a) -> (rest : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN 0 xs = (Exact [] xs)
takeN (S k) [] = Fewer []
takeN (S k) (x :: xs) with (takeN k xs)
  takeN (S k) (x :: xs) | (Fewer xs) = Fewer (x :: xs)
  takeN (S k) (x :: (n_xs ++ rest)) | (Exact n_xs rest) = Exact (x :: n_xs) rest

covering
groupBy: (n : Nat) -> (xs : List a) -> (List (List a))
groupBy n xs with (takeN n xs)
  groupBy n xs | (Fewer xs) = [xs]
  groupBy n (n_xs ++ rest) | (Exact n_xs rest) = n_xs :: groupBy n rest

data TakeNRec : List a -> Type where
  FewerRec : (xs : List a) -> TakeNRec xs
  ExactRec : (n_xs : List a) -> (rest : List a) -> TakeNRec rest -> TakeNRec (n_xs ++ rest)

takeNRec' : (n : Nat) -> (xs : List a) -> TakeNRec xs
takeNRec' 0 xs = (ExactRec [] xs (FewerRec xs))
takeNRec' (S k) [] = FewerRec []
takeNRec' (S k) (x :: xs) with (takeNRec' k xs)
  takeNRec' (S k) (x :: xs) | (FewerRec xs) = FewerRec (x :: xs)
  takeNRec' (S k) (x :: (n_xs ++ rest)) | (ExactRec n_xs rest y) =
    (ExactRec (x :: n_xs) rest (FewerRec rest))

groupBy': (n : Nat) -> (xs : List a) -> (List (List a))
groupBy' n xs with (takeNRec' n xs)
  groupBy' n xs | (FewerRec xs) = [xs]
  groupBy' n (n_xs ++ rest) | (ExactRec n_xs rest x) =
    n_xs :: (groupBy' n rest | x)






