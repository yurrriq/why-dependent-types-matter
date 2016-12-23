---
author: Jan Stolarek <jan.stolarek@p.lodz.pl>
license: Public Domain
---

= Why Dependent Types Matter

> ||| Why Dependent Types Matter
> module Data.YDTM

This module contains an Idris implementation of the code presented in *Why
Dependent Types Matter* by Thorsten Altenkirch, Conor McBride and James McKinna.
The original code in the paper was written in Epigram. Previously I rewrote that
code to Agda and now I made another rewrite in Idris. With the Idris
implementation, I decided to use many of the built-in features. This made some
things (like proofs) a lot simpler. Also, at the moment, Idris's totality
checker does a better job than Agda's (remember that `idris-mode` does not
highlight partial functions - you need to enable totality checking via the
command line option, "total" annotation or in the REPL using the `:total`
command).

This file is a rewrite of the Agda implementation. I decided to remove all
original comments from the `.agda` file and comment only the things that are
different in Idris. This allows you to focus easily on the new stuff, but it
also assumes that you've read Agda implementation.

This code was written and tested in Idris 0.9.10. YMMV

In case of Idris, we don't need to reinvent the wheel. We have `Nat`, `Bool`,
`List`s and tuples (`Pair`s) already at hand in the standard `prelude`, which is
imported by default into every Idris module. Starting with Idris 0.9.16, vectors
are in the `Data.Vect` module and are not available by default in `prelude`, so
we need to import them.

> import Data.Vect
>
> %default total

== Introduction

```idris
||| Proofs that `n` is less than or equal to `m`
||| @ n the smaller number
||| @ m the larger number
data LTE  : (n, m : Nat) -> Type where
  ||| Zero is the smallest Nat
  LTEZero : LTE Z    right
  ||| If n <= m, then n + 1 <= m + 1
  LTESucc : LTE left right -> LTE (S left) (S right)


Uninhabited (LTE (S n) Z) where
  uninhabited LTEZero impossible
```

> deal : List a -> (List a, List a)
> deal []        = ([] , [])
> deal (x :: []) = (x :: [] , [])
> deal (y :: (z :: xs)) with (deal xs)
>   | (ys , zs) = (y :: ys , z :: zs)

Problems we had with termination checking of merge function in Agda are gone in
Idris - let's celebrate that by annotating merge with `total`.

There's a small issue of name clash between our `merge` and `sort` functions and
the same functions defined in `prelude`. Let's just rename our functions to
`mergeL` and `sortL` (`L` indicates that they work on lists).

> mergeL : List Nat -> List Nat -> List Nat
> mergeL []        ys             = ys
> mergeL xs        []             = xs
> mergeL (x :: xs) (y :: ys) with (isLTE x y)
>   | Yes prf   = x :: mergeL xs (y :: ys)
>   | No contra = y :: mergeL (x :: xs) ys

Still, `sortL` is not recognized as total.

> partial
> sortL : List Nat -> List Nat
> sortL xs with (deal xs)
>   | (ys, []) = ys
>   | (ys, zs) = mergeL (sortL ys) (sortL zs)

<!-- Section 3.1 : Totality is Good for more than the Soul -->

== Totality is Good for more than the Soul

I'll use the `Refl` provide by Idris.

<!-- Section 3.2 : Defusing General Recursion -->

== Defusing General Recursion

> data Parity : Type where
>      P0 : Parity
>      P1 : Parity
>
> data DealT : a -> Type where
>      EmpT  : DealT a
>      LeafT : a -> DealT a
>      NodeT : Parity -> DealT a -> DealT a -> DealT a
>
> insertT : a -> DealT a -> DealT a
> insertT x EmpT           = LeafT x
> insertT x (LeafT y)      = NodeT P0 (LeafT y) (LeafT x)
> insertT x (NodeT P0 l r) = NodeT P1 (insertT x l) r
> insertT x (NodeT P1 l r) = NodeT P0 l (insertT x r)
>
> dealT : List a -> DealT a
> dealT []        = EmpT
> dealT (x :: xs) = insertT x (dealT xs)
>
> mergeT : DealT Nat -> List Nat
> mergeT EmpT          = []
> mergeT (LeafT x)     = x :: []
> mergeT (NodeT p l r) = merge (mergeT l) (mergeT r)
>
> sortT : List Nat -> List Nat
> sortT xs = mergeT (dealT xs)

<!-- Section 4 -->
== Maintaining Invariants by Static Indexing

I'm using Idris Vectors, which are defined as:

```idris
data Vect : Nat -> Type -> Type
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a
```

This is slightly different than Agda's definition: the index comes first and the
type parameter comes second. Note that prior to Idris 0.9.9, the type parameter
was first and the index was second.

```idris
||| All but the first element of the vector
tail : Vect (S len) elem -> Vect len elem
tail (x::xs) = xs
```

From now on I will avoid implicit arguments in type signatures, unless they will
be pattern-matched in the definition.

As a reminder, here'e the definition of addition:

```idris
||| Add two natural numbers.
||| @ n the number to case-split on
||| @ m the other number
total plus : (n, m : Nat) -> Nat
plus Z right        = right
plus (S left) right = S (plus left right)
```

And here's definition of appending two Vectors:

```idris
||| Append two vectors
(++) : (xs : Vect m elem) -> (ys : Vect n elem) -> Vect (m + n) elem
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys
```

In both cases I'll be using the built-in Idris definitions.

```idris
||| Repeat some value some number of times.
|||
||| @ len the number of times to repeat it
||| @ x the value to repeat
replicate : (len : Nat) -> (x : elem) -> Vect len elem
replicate Z     x = []
replicate (S k) x = x :: replicate k x

||| Transpose a Vect of Vects, turning rows into columns and vice versa.
|||
||| As the types ensure rectangularity, this is an involution, unlike `Prelude.List.transpose`.
transpose : {n : Nat} -> Vect m (Vect n elem) -> Vect n (Vect m elem)
transpose []        = replicate _ []
transpose (x :: xs) = zipWith (::) x (transpose xs)
```


<!-- Section 4.1 -->

== Static Indexing and Proofs

> vrevacc : Vect n a -> Vect m a -> Vect (n + m) a
> vrevacc [] ys                      = ys
> vrevacc {n = S k} {m} (x :: xs) ys = rewrite plusSuccRightSucc k m in
>                                              vrevacc xs (x :: ys)

Again, we can't just fill in the right code because Idris doesn't know that `m +
(1 + n)` equals `1 + (m + n)`. Once again have to prove it, but this time we
will not be reinventing the wheel. We will use Idris's proofs of basic
properties provided by `prelude`.

We need to prove that:

```idris
plus k (S m) = plus (S k) m
```

Luckily, Idris comes with proofs of basic properties defined in the `prelude`
(the module `Data.Nat` in the `prelude` library). The property we need is also
there:

```idris
total plusSuccRightSucc : (left : Nat) -> (right : Nat) ->
  S (left + right) = left + (S right)
```

We will use `rewrite` to rewrite our value using `plusSuccRightSucc`. Since
`plusSuccRightSucc` proves property in the opposite direction we use `sym` to
reverse its sides.

<!-- Section 4.2 -->
== Sized Merge-Sort

> mergeS : Vect n Nat -> Vect m Nat -> Vect (n + m) Nat
> mergeS [] ys                  = ys
> mergeS (x :: xs) [] {n = S k} = rewrite plusZeroRightNeutral (S k) in
>                                         x :: xs
> mergeS (x :: xs) (y :: ys) {n = S k} {m = S j} with (isLTE x y)
>   | Yes prf   = x :: mergeS xs (y :: ys)
>   | No contra = rewrite sym (plusSuccRightSucc k j) in
>                         y :: mergeS (x :: xs) ys
>
> p2n : Parity -> Nat
> p2n P0 = Z
> p2n P1 = S Z

I renamed the data constructors to silence Idris warnings.

> data DealTS : a -> Nat -> Type where
>      EmpTS  : DealTS a Z
>      LeafTS : a -> DealTS a (S Z)
>      NodeTS : {n : Nat} -> (p : Parity) ->
>               DealTS a (p2n p + n) -> DealTS a n ->
>               DealTS a ((p2n p + n) + n)
>
> mergeTS : DealTS Nat n -> Vect n Nat
> mergeTS EmpTS          = []
> mergeTS (LeafTS x)     = [x]
> mergeTS (NodeTS p l r) = mergeS (mergeTS l) (mergeTS r)
>
> insertTS : {n : Nat} -> {X : Type} -> X -> DealTS X n -> DealTS X (S n)
> insertTS x EmpTS               = LeafTS x
> insertTS x (LeafTS y         ) = NodeTS P0 (LeafTS y) (LeafTS x)
> insertTS x (NodeTS     P0 l r) = NodeTS P1 (insertTS x l) r
> insertTS x (NodeTS {n} P1 l r) = rewrite plusSuccRightSucc n n in
>                                          NodeTS P0 l (insertTS x r)

<!-- Lest equation of insertTS looks much simpler than in Agda! -->

> dealTS : Vect n a -> DealTS a n
> dealTS []        = EmpTS
> dealTS (x :: xs) = insertTS x (dealTS xs)
>
> sortTS : Vect n Nat -> Vect n Nat
> sortTS xs = mergeTS (dealTS xs)


<!-- Section 5.1 -->

== Evidence of Ordering

```idris
||| If two numbers are ordered, their predecessors are too
fromLteSucc : (S m `LTE` S n) -> (m `LTE` n)
fromLteSucc (LTESucc x) = x

||| A decision procedure for `LTE`
isLTE : (m, n : Nat) -> Dec (m `LTE` n)
isLTE Z n = Yes LTEZero
isLTE (S k) Z = No succNotLTEzero
isLTE (S k) (S j) with (isLTE k j)
isLTE (S k) (S j) | (Yes prf) = Yes (LTESucc prf)
isLTE (S k) (S j) | (No contra) = No (contra . fromLteSucc)

||| `LTE` is reflexive.
lteRefl : LTE n n
lteRefl {n = Z}   = LTEZero
lteRefl {n = S k} = LTESucc lteRefl

||| `LTE` is transitive
lteTransitive : LTE n m -> LTE m p -> LTE n p
lteTransitive LTEZero y = LTEZero
lteTransitive (LTESucc x) (LTESucc y) = LTESucc (lteTransitive x y)
```


> lteASym : {x, y : Nat} -> LTE x y -> LTE y x -> x = x
> lteASym LTEZero      LTEZero      = Refl
> lteASym (LTESucc xy) (LTESucc yx) = Refl

<!-- Section 5.2 -->

== Locally Sorted Lists

> data LNat : Type where
>      ZL   : LNat
>      SL   : LNat -> LNat
>      InfL : LNat
>
> lift : Nat -> LNat
> lift Z     = ZL
> lift (S x) = SL (lift x)

This time I'll use `<?=` as a type constructor for types that compare
lifted `Nat`s.

> infix 4 <?=
>
> data (<?=) : LNat -> LNat -> Type where
>      LEZeroL  : ZL <?= y
>      LESuccL  : x <?= y -> SL x <?= SL y
>      LEIL  : x <?= InfL
>
> data CList : LNat -> Type where
>      CNil  : CList inf
>      CCons : (x : Nat) -> (lift x) <?= y -> CList y -> CList (lift x)
>
> clist : CList ZL
> clist = CCons Z LEZeroL (
>         CCons (S (S Z)) (LESuccL (LESuccL LEZeroL)) (
>         CCons (S (S Z))  LEIL CNil))
>
> data OList : Nat -> Type where
>      ONil  : OList b
>      OCons : (x : Nat) -> LTE b x -> OList x -> OList b
>
> olist : OList Z
> olist = OCons (S Z) LTEZero ONil
>
> olist2 : OList Z
> olist2 = OCons (S Z) LTEZero (OCons (S (S Z)) (LTESucc LTEZero) ONil)

Again, no issues with termination checker in `mergeO`.

> lteLemma : (x, y : Nat) -> Not (LTE x y) -> LTE y x
> lteLemma Z _ p         = absurd (p LTEZero)
> lteLemma _ Z _         = LTEZero
> lteLemma (S k) (S j) p = LTESucc (lteLemma k j (absurd . p . LTESucc))
>
> mergeO : OList b -> OList b -> OList b
> mergeO ONil ys = ys
> mergeO (OCons x blex xs) ONil = OCons x blex xs
> mergeO (OCons x blex xs) (OCons y bley ys) with (isLTE x y)
>   | Yes xley = OCons x blex (mergeO xs (OCons y xley ys))
>   | No nxley = let ylex = lteLemma x y nxley in
>                    OCons y bley (mergeO (OCons x ylex xs) ys)
>
> mergeTO : DealT Nat -> OList Z
> mergeTO EmpT          = ONil
> mergeTO (LeafT x)     = OCons x LTEZero ONil
> mergeTO (NodeT p l r) = mergeO (mergeTO l) (mergeTO r)
>
> sortO : List Nat -> OList Z
> sortO xs = mergeTO (dealT xs)
