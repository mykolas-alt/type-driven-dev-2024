module Pratybos.Prat11

import Data.Nat 
import Data.List.Views
import Data.List
import Data.Stream

%default total

data Matter = Solid | Liquid | Gas

data MatterCmd : Matter -> Matter -> Type where
  Melt : MatterCmd Solid Liquid
  Condence : MatterCmd Gas Liquid
  Freeze : MatterCmd Liquid Solid
  Boil : MatterCmd Liquid Gas
  (>>) :
      MatterCmd s1 s2 ->
      MatterCmd s2 s3 ->
      MatterCmd s1 s3

prog1 : MatterCmd Solid Gas
prog1 =
  do Melt
     Boil

prog2 : MatterCmd Gas Solid
prog2 =
  do Condence
     Freeze

failing
  prog3 : MatterCmd Solid Gas
  prog3 =
    do Melt
       Melt

{-
- Solid -> Gas
- melt
- boil
-
- Gas -> Solid
- condence
- freeze
-
- neturi veikti
- Solid -> Gas
- melt
-}

namespace Stacking
  data StackState = StackRunning Nat | StackEnd | StackFailed
  data StackFinal : StackState -> Type where
    FinalSuccess : StackFinal (StackRunning n)
    FinalFailed : StackFinal StackFailed
  data PushRes = Ok | Failed

  data StackCmd : (res : Type) -> StackState -> (res -> StackState) -> Type where
  Push : Integer -> StackCmd PushRes (StackRunning height) (\x => case x of
                                                                       Ok => StackRunning (S height)
                                                                       Failed => StackFailed)
  Pop : StackCmd Integer (StackRunning (S height)) (const $ StackRunning height)
  Top : StackCmd Integer (StackRunning (S height)) (const $ StackRunning (S height))
  Pure : a -> StackCmd a (StackRunning 0) (const $ StackRunning 0)
  Final : StackFinal fin -> StackCmd () fin (const StackEnd)
  (>>=) : 
    StackCmd a s1 sf2 ->
    ((res: a) -> StackCmd b (sf2 res) s3) ->
    StackCmd b s1 s3
  (>>) : 
    StackCmd a s1 (\_ => s2) ->
    StackCmd b s2 s3 ->
    StackCmd b s1 s3

  add : StackCmd () (StackRunning 0) (const StackEnd)
  add = do
       Ok <- Push 10 | Failed => Final FinalFailed
       Ok <- Push 22 | Failed => Final FinalFailed
       x <- Pop
       y <- Pop
       Ok <- Push (x + y) | Failed => Final FinalFailed
       Final FinalSuccess

  mul : StackCmd () (StackRunning 0) (const StackEnd)
  mul = do
       Ok <- Push 10 | Failed => Final FinalFailed
       Ok <- Push 22 | Failed => Final FinalFailed
       x <- Pop
       y <- Pop
       Ok <- Push (x * y) | Failed => Final FinalFailed
       Final FinalSuccess

