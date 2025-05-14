module Pratybos.Prat13

import Data.Nat 
import Data.List.Views
import Data.List
import Data.Stream

%default total

-- app_assoc      : ∀ (lst1 lst2 lst3 : list),
--                  app (app lst1 lst2) lst3 = app lst1 (app lst2 lst3)
app_assoc : (l1, l2, l3 : List a) -> (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
app_assoc [] l2 l3 = Refl
app_assoc (x :: xs) l2 l3 = rewrite app_assoc xs l2 l3 in Refl

-- app_length     : ∀ (lst1 lst2 : list),
--                  length (app lst1 lst2) = length lst1 + length lst2
app_length : (l1, l2 : List a) -> length (l1 ++ l2) = (length l1) + (length l2)
app_length [] l2 = Refl
app_length (x :: xs) l2 = rewrite app_length xs l2 in Refl

rev : List a -> List a
rev [] = []
rev (x :: xs) = rev xs ++ [x]

-- rev_length     : ∀ (lst : list),
--                  length (rev lst) = length lst
rev_length : (l1 : List a) -> length (rev l1) = length l1
rev_length [] = Refl
rev_length (x :: xs) = rewrite sym (rev_length xs) in
                       rewrite app_length (rev xs) [x] in
                       rewrite plusCommutative (length (rev xs)) 1 in Refl

tl : List a -> List a
tl [] = []
tl (x :: xs) = xs

-- tl_length_pred : ∀ (lst : list),
--                  pred (length lst) = length (tl lst)
tl_length_pred : (l1 : List a) -> pred (length l1) = length (tl l1)
tl_length_pred [] = Refl
tl_length_pred (x :: xs) = Refl

