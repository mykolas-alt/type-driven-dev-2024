module Pratybos.Prat4

import Data.Vect
import Data.String
import System.REPL

%default total

-- 1
same_cons : (xs : List a) -> (ys : List a) -> xs = ys -> x :: xs = x :: ys
same_cons xs xs Refl = Refl

-- 2
same_lists : (xs : List a) -> (ys : List a) -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists xs xs Refl Refl = Refl

append_nil : Vect m a -> Vect (plus m 0) a
append_nil xs = rewrite plusCommutative m 0 in xs

appendXs : Vect (S (plus m len)) a -> Vect (plus m (S len)) a
appendXs xs = rewrite sym $ plusSuccRightSucc m len in xs

-- 3
append' : Vect n a -> Vect m a -> Vect (m + n) a
append' [] ys = append_nil ys
append' (x :: xs) ys = appendXs $ x :: append' xs ys
