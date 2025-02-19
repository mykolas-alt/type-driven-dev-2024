module Pratybos.Prat3

import Data.Vect
import Data.String
import System.REPL

%default total

data Format = Number Format
            | Str Format
            | Lit Char Format
            | End

-- Str (Lit " = " (Number End))

PrintfType : Format -> Type
PrintfType (Number x) = (i : Int) -> PrintfType x
PrintfType (Str x) = (s : String) -> PrintfType x
PrintfType (Lit str x) = PrintfType x
PrintfType End = String

printFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printFmt (Number x) acc = \i => printFmt x (acc ++ show i)
printFmt (Str x) acc = \s => printFmt x (acc ++ s)
printFmt (Lit str x) acc = printFmt x (acc ++ pack [str])
printFmt End acc = acc


toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
toFormat (x :: xs) = Lit x (toFormat xs)

printf : (fmt : String) -> PrintfType (toFormat $ unpack fmt)
printf fmt = printFmt (toFormat $ unpack fmt) ""

data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType ((.+.) x y) = (SchemaType x, SchemaType y)

data DataStore : Type where
    MkData : (size : Nat) -> (schema : Schema) -> (items : Vect size (SchemaType schema)) -> DataStore


size : DataStore -> Nat
size (MkData k _ _) = k

schema : DataStore -> Schema
schema (MkData size x items) = x

items : (store : DataStore) -> Vect (size store) (SchemaType (schema store))
items (MkData size _ xs) = xs

addToTail : Vect size_0 a -> a -> Vect (S size_0) a
addToTail [] str = [str]
addToTail (x :: xs) str = x :: addToTail xs str

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData size x items) str = MkData (S size) x (addToTail items str)

getByIndex : (store : DataStore) -> Fin (size store) -> SchemaType (schema store)
getByIndex (MkData size _ items) x = index x items

AdderType : (numargs : Nat) -> Type 
AdderType 0 = Int
AdderType (S k) = Int -> AdderType k

adder : (numargs : Nat) -> (acc : Int) -> AdderType numargs
adder 0 acc = acc
adder (S k) acc = \arg => adder k (acc + arg)

