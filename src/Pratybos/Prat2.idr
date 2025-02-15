module Pratybos.Prat2

import Data.Vect
import Data.String
import System.REPL

%default total

alllength : Vect l String -> Vect l Nat
alllength [] = []
alllength (x :: xs) = length x :: alllength xs
-- alllength [] = []
-- alllength (x :: xs) = length x :: alllength xs

insertion : Ord el => el -> Vect len el -> Vect (S len) el
insertion x [] = [x]
insertion x (y :: xs) = case x < y of
                             False => y :: insertion x xs
                             True => x :: (y :: xs)

m1 : Vect 2 (Vect 3 Int)
m1 = [[1, 2, 3], [4, 5, 6]]

m2 : Vect 2 (Vect 3 Int)
m2 = [[6, 5, 4], [3, 2, 1]]

addMatrix : Num e => Vect r (Vect c e) -> Vect r (Vect c e) -> Vect r (Vect c e)
addMatrix [] _ = []
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys


insSort : Ord e => Vect n e -> Vect n e
insSort [] = []
insSort (x :: xs) = let sorted = insSort xs in insertion x sorted

data BSTree : Type -> Type where
    BSEmpty : Ord a => BSTree a
    BSNode : Ord a => (left: BSTree a) -> a -> (right: BSTree a) -> BSTree a

insert : e -> BSTree e -> BSTree e
insert x BSEmpty = BSNode BSEmpty x BSEmpty
insert x tree@(BSNode left y right) = case compare x y of
                                      LT => BSNode (insert x left) y right
                                      EQ => tree
                                      GT => BSNode left y (insert x right)

data Vec : Nat -> Type -> Type where
    Nil : Vec 0 a
    (::) : a -> Vec n a -> Vec (S n) a

data DataStore : Type where
    MkData : (size : Nat) -> (items : Vect size String) -> DataStore

printall : DataStore -> String
printall (MkData size items) = show items

addToTail : Vect size_0 String -> String -> Vect (S size_0) String
addToTail [] str = [str]
addToTail (x :: xs) str = x :: addToTail xs str

add : DataStore -> String -> DataStore
add (MkData size items) str = MkData (S size) (addToTail items str)

proccessInput : DataStore -> String -> Maybe (String, DataStore)
proccessInput x "printall" = Just (printall x ++ "\n", x) 
proccessInput x cmd = case words cmd of
                           ("add" :: xs) => let arg = unwords xs in Just ("Added " ++ arg ++ "\n", add x arg)
                           _ => Nothing

covering
main : IO ()
main = replWith (MkData _ ["test", "medis", "tipai jega"]) ">>>" proccessInput
