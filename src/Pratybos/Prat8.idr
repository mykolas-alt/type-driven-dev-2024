module Pratybos.Prat8

import Data.Nat 

%default total

data ListProj : {a, b : Type} -> List a -> (a -> b) -> List b -> Type where
  ListProjEmpty : (ListProj [] _ [])
  ListProjSucc : 
    {op : a -> b} -> 
    ListProj as op bs ->
    (a' : a) ->
    (ListProj (a' :: as) op (op a' :: bs))

listProj : (la : List a) -> (op : a -> b) -> (lb : List b ** ListProj la op lb)
listProj [] op = ([] ** ListProjEmpty)
listProj (x :: xs) op = let (lst ** prf) = listProj xs op in
                            (op x :: lst ** ListProjSucc prf x)

sameAsMap : {la : List a} ->
            {op : a -> b} ->
            {lb : List b} ->
            ListProj la op lb -> lb = map op la
sameAsMap ListProjEmpty = Refl
sameAsMap (ListProjSucc x a') = case sameAsMap x of
                                     Refl => Refl
-- sameAsMap (ListProjSucc x a') = rewrite sameAsMap x in Refl

lbIsLc : {la : List a} ->
         {op : a -> b} ->
         (ListProj la op lb) ->
         (ListProj la op lc) ->
         lb = lc
lbIsLc ListProjEmpty ListProjEmpty = Refl
lbIsLc (ListProjSucc x a') (ListProjSucc y a') = case (lbIsLc x y) of
                                                      Refl => Refl

