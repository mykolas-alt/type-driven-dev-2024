module Pratybos.Prat12

import Data.Nat 
import Data.List.Views
import Data.List
import Data.Stream

%default total

data Binop = Plus | Times


data Exp : Type where
    Const : Nat -> Exp
    Op : Binop -> Exp -> Exp -> Exp

-- binopDenote : Binop → ℕ → ℕ → ℕ
binopDenote : Binop -> Nat -> Nat -> Nat
binopDenote Plus k j = k + j
binopDenote Times k j = k * j

-- expDenote : Exp → ℕ
expDenote : Exp -> Nat
expDenote (Const k) = k
expDenote (Op x y z) = binopDenote x (expDenote y) (expDenote z)


-- e-test₁ : expDenote (Op Plus (Const 1) (Const 2)) ≡ 3

eTest : (expDenote (Op Plus (Const 1) (Const 2))) = 3
eTest = Refl


data Instr : Type where
    IConst : Nat -> Instr
    IOp : Binop -> Instr

Prog = List Instr
Stack = List Nat

instrDenote : Instr -> Stack -> Maybe Stack
instrDenote (IConst x) s = Just (x :: s) 
instrDenote (IOp x) (x₁ :: x₂ :: s) =  Just (binopDenote x x₁ x₂ :: s)
instrDenote (IOp x) _ = Nothing

progDenote : Prog -> Stack -> Maybe Stack
progDenote [] ks = Just ks
progDenote (x :: xs) ks with ((instrDenote x ks))
  progDenote (x :: xs) ks | Nothing = Nothing
  progDenote (x :: xs) ks | (Just y) = (progDenote xs y)

compile : Exp -> Prog
compile (Const x) = [ IConst x ]
compile (Op x e₁ e₂) = (compile e₂) ++ (compile e₁) ++ [ IOp x ]

compileCorrect : 
    (e : Exp) ->
    (p : Prog) ->
    (s : Stack) ->
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)
compileCorrect (Const k) p s = Refl
compileCorrect (Op x e1 e2) p s =
  rewrite sym $ appendAssociative (compile e2) (compile e1 ++ IOp x :: []) p in
  rewrite compileCorrect e2 ((compile e1 ++ IOp x :: []) ++ p) s in
  rewrite sym $ appendAssociative (compile e1) (IOp x :: []) p in
  rewrite compileCorrect e1 (IOp x :: [] ++ p) (expDenote e2 :: s) in
  Refl
