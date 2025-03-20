module Pratybos.Prat7

import Data.Nat 

%default total

-- 1
data Even : Nat -> Type where
    EvenZero : Even 0
    EvenNext : {x : Nat} -> Even x -> Even (S (S x))

-- Would be better to define as a function.
data Odd : Nat -> Type where
    OddOne : Odd 1
    OddNext : {x : Nat} -> Odd x -> Odd (S (S x))

oddToEven : { x : Nat } -> Odd x -> Even (S x)
oddToEven OddOne = EvenNext EvenZero
oddToEven (OddNext x) = EvenNext (oddToEven x)

-- 2 
oddToEven' : Odd (S x) -> Even x
oddToEven' OddOne = EvenZero
oddToEven' (OddNext OddOne) = EvenNext EvenZero
oddToEven' (OddNext (OddNext y)) = EvenNext (oddToEven' (OddNext y))

-- 3
allEvenOrOdd : ( x : Nat ) -> Either (Even x) (Odd x)
allEvenOrOdd 0 = Left EvenZero
allEvenOrOdd (S 0) = Right OddOne
allEvenOrOdd (S (S k)) = case allEvenOrOdd k of
                              (Left x) => Left (EvenNext x)
                              (Right x) => Right (OddNext x)

h : (x : Nat) -> LTE (S x) (S (S x))
h 0 = LTESucc LTEZero
h (S k) = LTESucc (h k)

-- 4 ∀x∈N(even x => ∃y∈N(y > x ∧ even y))
existsGreaterEven : { x : Nat } -> Even x -> (y ** (GT y x, Even y))
existsGreaterEven y = (S (S x) ** (h x, EvenNext y))

-- 5 ∃x(P(x) ∧ Q(x)) => (∃y.P(y)) ∧ (∃z.Q(z))
existAnd :
    { x, y, z : Type } ->
    { p, q : x -> Type } ->
    (x ** (p x, q x)) ->
    ((y ** p y), (z ** q z))
existAnd ((fst ** (y, z))) = ((fst ** y), (fst ** z))

-- 6 ∀ a,b ∈ N, ∃m∈N, m = max a b
data Max : Nat -> Nat -> Type where
    MaxFst : { a, b : Nat } -> GTE a b -> Max a b
    MaxSnd : { a, b : Nat } -> LT a b -> Max a b
    
lemma1 : (a : Nat )-> (b : Nat) -> Either (GTE a b) (LT a b)
lemma1 0 0 = Left LTEZero
lemma1 0 (S k) = Right (LTESucc LTEZero)
lemma1 (S k) 0 = Left LTEZero
lemma1 (S k) (S j) = case lemma1 k j of
                          (Left x) => Left (LTESucc x)
                          (Right x) => Right (LTESucc x)

existsMax : (a : Nat) -> (b : Nat) -> (m : Nat ** Max a b)
existsMax a b = case lemma1 a b of
                     (Left x) => (b ** MaxFst x)
                     (Right x) => (b ** MaxSnd x)
