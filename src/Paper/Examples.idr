module Paper.Examples

import Decidable.Equality

%default total

namespace StandardNats

  -- Standartinis natūraliųjų skaičiu apibrėžimas naudojant indukciją
  -- Zero ∈ ℕ, jei x ∈ ℕ -> Succ x ∈ ℕ
  data Peano = Zero | Succ Peano

  -- Galima patogiai apibrėžti funkcijas naudojant pattern matching
  -- power(x, n) = xⁿ, x ∈ ℝ, n ∈ ℕ
  power : Double -> Peano -> Double
  power x Zero = 1
  power x (Succ n) = x * power x n

  -- Bėda: taip konstruojant skaičius neefektyviai išnaudojam resursus.
  -- Kiekvienas konstruktorius turi būti "matomas", negalime panaudoti duomenų abstrakcijos.

















namespace ViewIntoNats

  -- Norimo view tipas, naudojam built in Int abstrakciją sveikiesiems skaičiams
  data NatView = Zero | Succ Int

  -- Kadangi ℕ ⊂ ℤ, negalime apibrėžti totalios funkcijos iš viewed tipo į viewing tipą, kuri būtų izomorfiška abiejų aibių atžvilgiu
  viewIn' : Int -> NatView
  viewIn' i = case (compare i 0) of
               EQ => Zero
               GT => Succ (i - 1)
               LT => ?in'_rhs_0

  -- Galime apibrėžti f-ją, kuri atvaizduos natūraliųjų skaičių poaibį sveikųjų skaičių aibėje i viewing tipą
  viewIn : Int -> Maybe NatView
  viewIn i = case (compare i 0) of
               EQ => Just Zero
               GT => Just (Succ (i - 1))
               LT => Nothing

  partial
  viewIn'' : Int -> NatView
  viewIn'' i = case (compare i 0) of
               EQ => Zero
               GT => (Succ (i - 1))

  viewOut : NatView -> Int
  viewOut Zero = 0
  viewOut (Succ n) = n + 1

  -- Konstruktoriai su funkcijomis "in" ir "out" sudaro rinkinį, kuris nurodo izomorfizmą tarp viewed tipo (Int) ir viewing tipo (NatView)
  -- t.y. ∀x ∈ ℤ (x >= 0) ⇒ (viewOut (viewIn x) = x)

  export
  partial
  fib : Int -> Int
  fib m = case viewIn'' m of
               Zero => viewOut Zero
               (Succ m') => case viewIn'' m' of
                                 Zero => viewOut (Succ (viewOut Zero))
                                 (Succ n) => fib n + fib (viewOut (Succ n))
  -- Viewing tipas naudojamas tik f-jos viduje

  -- Naudojant idris2 with sintakse
  export
  partial
  fib' : Int -> Int
  fib' m with (viewIn'' m)
    fib' m | Zero = viewOut Zero
    fib' m | (Succ m') with (viewIn'' m')
      fib' m | (Succ m') | Zero = viewOut (Succ (viewOut Zero))
      fib' m | (Succ m') | (Succ n) = fib' n + fib' (viewOut (Succ n))


















namespace AnotherViewOfIntegers
  data ParityView = Zero | Even Int | Odd Int

  partial
  viewIn : Int -> ParityView
  viewIn n = case compare n 0 of
                  EQ => Zero
                  GT => case compare (n `mod` 2) 0 of
                             EQ => Even (n `div` 2)
                             GT => Odd ((n - 1) `div` 2)

  viewOut : ParityView -> Int
  viewOut Zero = 0
  viewOut (Even n) = 2 * n
  viewOut (Odd n) = (2 * n) + 1

  -- panaudojant sukurtą view galime keliomis eilutėmis aprašyti efektyvų divide-and-conquer algoritmą
  export
  partial
  power : Int -> Int -> Int
  power x y with (viewIn y)
    power x y | Zero = 1
    power x y | (Even n) = power (x * x) n
    power x y | (Odd n) = x * power (x * x) n

















namespace ComplexNumbers
  -- Tarkime laikome kompleksinius skaičius trigonometrinėje formoje
  -- Pole r θ, čia r ∈ ℝ - vektoriaus ilgis, θ ∈ [0; 2π] - kampas tarp vektoriaus ir Ox ašies
  data PolarComplex = Pole Double Double

  -- Kartais patogu funkcijose panaudoti algebrinę formą
  -- Cart x y, x,y ∈ ℝ
  data CartesianComplex = Cart Double Double

  partial
  viewIn : PolarComplex -> CartesianComplex
  viewIn (Pole r t) = case (r > 0 && 0 <= t && t < (2 * pi)) || (r == 0 && t == 0) of
                           True => Cart (r * cos t) (r * sin t)

  viewOut : CartesianComplex -> PolarComplex
  viewOut (Cart x y) = Pole (sqrt (x * x + y * y)) (atan (y / x))

  partial
  add : PolarComplex -> PolarComplex -> PolarComplex
  add c1 c2 = case viewIn c1 of
                   (Cart x1 y1) => case viewIn c2 of
                                        (Cart x2 y2) => viewOut (Cart (x1 + x2) (y1 + y2))

  -- Jei laikytume kompleksinius skaičius jų algebrinėje formoje
  -- galime pasinaudoti faktu, kad duotos funkcijos sudaro bijekciją
  -- ir apibrėžiant sandaugos funkciją naudotume view į trigonometrinę formą

  partial
  mult : CartesianComplex -> CartesianComplex -> CartesianComplex
  mult c1 c2 = case viewOut c1 of
                    (Pole r1 t1) => case viewOut c2 of
                                         (Pole r2 t2) => viewIn (Pole (r1 * r2) (t1 + t2))

  -- Norėdami susigražinti abstrakcijos pranašumus galime apibrėžti wrapper ADT
  data Complex = Polar PolarComplex | Cartesian CartesianComplex

  -- arba
  -- data Complex = Pole Double Double | Cart Double Double
  -- ir sukurti view tarp Complex aibės poaibių






























namespace ViewingAListBackwards

  data SnocList' a = Nil | Snoc (List a) a

  viewIn : List a -> SnocList' a
  viewIn Nil = Nil
  viewIn (x :: xs) with (viewIn xs)
    viewIn (x :: _) | [] = Snoc Nil x
    viewIn (x :: _) | (Snoc xs x') = Snoc (x :: xs) x'

  viewOut : SnocList' a -> List a
  viewOut Nil = Nil
  viewOut (Snoc Nil x) = x :: Nil
  viewOut (Snoc (x :: xs) x') = x :: viewOut (Snoc xs x')

  export
  last : List a -> Maybe a
  last xs with (viewIn xs)
    last xs | [] = Nothing
    last xs | (Snoc ys x) = Just x

  export
  rotleft : List a -> List a
  rotleft [] = []
  rotleft (x :: xs) = viewOut (Snoc xs x)

  export
  rotright : List a -> List a
  rotright xs with (viewIn xs)
    rotright _ | [] = []
    rotright _ | (Snoc xs x) = x :: xs


















namespace JoinLists

  data JoinList a = Nil | Unit a | Join (JoinList a) (JoinList a)

  data List' a = Nil' | Cons a (JoinList a)

  covering
  viewIn : JoinList a -> List' a
  viewIn Nil = Nil'
  viewIn (Unit x) = Cons x Nil
  viewIn (Join [] xs) = viewIn xs
  viewIn (Join (Unit x) xs) = Cons x xs
  viewIn (Join (Join xs ys) zs) = viewIn (Join xs (Join ys zs))

  viewOut : List' a -> JoinList a
  viewOut Nil' = Nil
  viewOut (Cons x xs) = Join (Unit x) xs

  viewIn' : JoinList a -> List a
  viewIn' [] = []
  viewIn' (Unit x) = [x]
  viewIn' (Join x y) = viewIn' x ++ viewIn' y

  viewOut' : List a -> JoinList a
  viewOut' [] = Nil
  viewOut' (x :: xs) = Join (Unit x) (viewOut' xs)

