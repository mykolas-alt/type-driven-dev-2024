module Pratybos.Prat6

import Data.Vect
import Data.String
import System.REPL
import Decidable.Equality

%default total

-- A => B => (-A or B)
impl_simpl : a -> b -> Either (Not a) b
impl_simpl x y = Right y

-- P /\ Q => P \/ Q

f : (p, q) -> Either p q
f (x, y) = Right y

-- (P /\ Q) \/ R => (P \/ R) /\ (Q \/ R)
g : Either (p, q) r -> (Either p r, Either q r)
g (Left (x, y)) = (Left x, Left y)
g (Right x) = (Right x, Right x)

-- P => --P
f' : p -> Not (Not p)
f' x f = f x

-- (P => -P) => -P
f'' : (p -> (p -> Void)) -> (p -> Void)
f'' f x = f x x

-- -(P /\ Q) => (P => Q)
f''' : ((p, q) -> Void) -> (p -> (q -> Void))
f''' f x y = f (x, y)

-- (P => Q) => (-Q => -P)
g' : (p -> q) -> (q -> Void) -> (p -> Void)
g' h j k = j $ h k





