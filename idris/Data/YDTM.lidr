---
author: Jan Stolarek <jan.stolarek@p.lodz.pl>
license: Public Domain

---

= Why Dependent Types Matter

> ||| Why Dependent Types Matter
> module Data.YDTM

This module contains an Idris implementation of the code presented in *Why Dependent Types Matter* by Thorsten Altenkirch, Conor McBride and James McKinna. The original code in the paper was written in Epigram. Previously I rewrote that code to Agda and now I made another rewrite in Idris. With the Idris implementation, I decided to use many of the built-in features. This made some things (like proofs) a lot simpler. Also, at the moment, Idris's totality checker does a better job than Agda's (remember that `idris-mode` does not highlight partial functions - you need to enable totality checking via the command line option, `total` annotation or in the REPL using the `:total` command).

This file is a rewrite of the Agda implementation. I decided to remove all original comments from the `.agda` file and comment only the things that are different in Idris. This allows you to focus easily on the new stuff, but it also assumes that you've read Agda implementation.

This code was written and tested in Idris 0.99. YMMV

In case of Idris, we don't need to reinvent the wheel. We have `Nat`, `Bool`, `List`s and tuples (`Pair`s) already at hand in the standard `prelude`, which is imported by default into every Idris module. Starting with Idris 0.9.16, vectors are in the `Data.Vect` module and are not available by default in `prelude`, so we need to import them.

> import Data.Vect
>
> %default total

== Introduction

The Idris `prelude` provides much of what we need already:

- `Nat` $\mapsto$ `Nat`

```idris
data Nat = Z | S Nat
```

- `Order` $\mapsto$ `Ordering`

```idris
data Ordering : Type where
  LT : Ordering
  EQ : Ordering
  GT : Ordering
```

- `List` $\mapsto$ `List`

```idris
data List : (elem : Type) -> Type where
   Nil    : List elem
   (::)   : (x : elem) -> (xs : List elem) -> List elem
```

- `order` $\mapsto$ `compare`

```idris
interface Eq ty => Ord ty where
  compare : ty -> ty -> Ordering
  -- ...

implementation Ord Nat where
  compare Z Z         = EQ
  compare Z (S k)     = LT
  compare (S k) Z     = GT
  compare (S x) (S y) = compare x y
```

The rest we'll need to write ourselves.

To avoid naming conflicts between our `merge` and `sort` functions and their `prelude` analogs, we can `%hide` them.

> %hide List.merge
> %hide List.sort

Problems we had with termination checking of merge function in Agda are gone in Idris.

> namespace Introduction
>
>   merge : (xs, ys : List Nat) -> List Nat
>   merge [] ys = ys
>   merge xs [] = xs
>   merge (x :: xs) (y :: ys) with (compare x y)
>     | GT = y :: merge (x :: xs) ys
>     | _  = x :: merge xs (y :: ys)
>
>   ||| Deal out a list into two lists of (roughly) half the length.
>   deal : List a -> (List a, List a)
>   deal []        = ([], [])
>   deal (x :: []) = (x :: [], [])
>   deal (y :: (z :: xs)) with (deal xs)
>     | (ys, zs) = (y :: ys, z :: zs)

Still, `sort` is not recognized as total.

>   partial
>   sort : List Nat -> List Nat
>   sort xs with (deal xs)
>     | (ys, []) = ys
>     | (ys, zs) = merge (sort ys) (sort zs)

<!-- Section 3.1 : Totality is Good for more than the Soul -->

== Totality is Good for more than the Soul

I'll use the `Refl` provide by Idris.

<!-- Section 3.2 : Defusing General Recursion -->

== Defusing General Recursion

> namespace DefusingGeneralRecursion
>
>   data Parity = P0 | P1
>
>   data DealT : a -> Type where
>        EmpT  : DealT a
>        LeafT : (x : a) -> DealT a
>        NodeT : (p : Parity) -> (l, r : DealT a) -> DealT a
>
>   insertT : (x : a) -> (t : DealT a) -> DealT a
>   insertT x EmpT           = LeafT x
>   insertT x (LeafT y)      = NodeT P0 (LeafT y) (LeafT x)
>   insertT x (NodeT P0 l r) = NodeT P1 (insertT x l) r
>   insertT x (NodeT P1 l r) = NodeT P0 l (insertT x r)
>
>   dealT : List a -> DealT a
>   dealT []        = EmpT
>   dealT (x :: xs) = insertT x (dealT xs)
>
>   mergeT : DealT Nat -> List Nat
>   mergeT EmpT          = []
>   mergeT (LeafT x)     = [x]
>   mergeT (NodeT p l r) = merge (mergeT l) (mergeT r)
>
>   sortT : (xs : List Nat) -> List Nat
>   sortT = mergeT . dealT

<!-- Section 4 -->
== Maintaining Invariants by Static Indexing

I'm using Idris Vectors, which are defined as:

```idris
data Vect : Nat -> Type -> Type
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a
```

This is slightly different than Agda's definition: the index comes first and the type parameter comes second. Note that prior to Idris 0.9.9, the type parameter was first and the index was second.

```idris
tail : Vect (S len) elem -> Vect len elem
tail (x::xs) = xs
```

For Epigram's 'vectorized application' we have `Vect`'s `Applicative` implementation:

```idris
implementation Applicative (Vect k) where
  -- ...
  fs <*> vs = zipWith apply fs vs
```

As a reminder, here'e the definition of addition:

```idris
total plus : (n, m : Nat) -> Nat
plus Z right        = right
plus (S left) right = S (plus left right)
```

And here's definition of appending two Vectors:

```idris
(++) : (xs : Vect m elem) -> (ys : Vect n elem) -> Vect (m + n) elem
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys
```

In both cases I'll be using the built-in Idris definitions.

Idris also provides `replicate` (née $vec_n$) and `transpose` (née `xpose`):

```idris
replicate : (len : Nat) -> (x : elem) -> Vect len elem
replicate Z     x = []
replicate (S k) x = x :: replicate k x

transpose : {n : Nat} -> Vect m (Vect n elem) -> Vect n (Vect m elem)
transpose []        = replicate _ []
transpose (x :: xs) = zipWith (::) x (transpose xs)
```

<!-- Section 4.1 -->

=== Static Indexing and Proofs

`vrevacc` from the paper is basically the local `go` from Idris's `reverse`.

```idris
reverse : Vect len elem -> Vect len elem
reverse xs = go [] xs
  where go : Vect n elem -> Vect m elem -> Vect (n+m) elem
```

In the first clause we need to prove `n + 0 = n`, aka `plusZero` in the paper. Idris calls that `plusZeroRightNeutral` in `Prelude.Nat`.

```idris
go {n} acc [] = rewrite plusZeroRightNeutral n in acc
```

Again, we can't just fill in the right-hand side of the second clause, because Idris doesn't know that `m + (1 + n)` equals `1 + (m + n)`.

Translating to Idris, We need to prove:

```idris
plus n (S m) = S (plus n m)
```

Luckily, `Prelude.Nat` also includes `plusSuccRightSucc`:

```idris
total plusSuccRightSucc : (left : Nat) -> (right : Nat) ->
  S (left + right) = left + (S right)
```

We use `rewrite` to rewrite our value using `plusSuccRightSucc`. Since `plusSuccRightSucc` proves property in the opposite direction we use `sym` to reverse its sides.

```idris
go {n} {m=S m} acc (x :: xs) = rewrite sym (plusSuccRightSucc n m) in
                                       go (x::acc) xs
```


<!-- Section 4.2 -->

== Sized Merge-Sort

> namespace Sized
>
>   merge : Vect n Nat -> Vect m Nat -> Vect (n + m) Nat
>   merge [] ys     = ys
>   merge xs [] {n} = rewrite plusZeroRightNeutral n in xs
>   merge (x :: xs) (y :: ys) {n = S k} {m = S j} with (compare x y)
>     | GT = rewrite sym (plusSuccRightSucc k j) in
>                    y :: Sized.merge (x :: xs) ys
>     | _  = x :: Sized.merge xs (y :: ys)
>
>   p2n : Parity -> Nat
>   p2n P0 = Z
>   p2n P1 = S Z
>
>   data DealT : a -> Nat -> Type where
>        EmpT  : DealT a Z
>        LeafT : a -> DealT a (S Z)
>        NodeT : (p : Parity) -> DealT a (p2n p + n) -> DealT a n ->
>                 DealT a ((p2n p + n) + n)
>
>   mergeT : DealT Nat n -> Vect n Nat
>   mergeT EmpT          = []
>   mergeT (LeafT x)     = [x]
>   mergeT (NodeT p l r) = Sized.merge (mergeT l) (mergeT r)
>
>   insertT : {n : Nat} -> {X : Type} -> X -> DealT X n -> DealT X (S n)
>   insertT x EmpT               = LeafT x
>   insertT x (LeafT y         ) = NodeT P0 (LeafT y) (LeafT x)
>   insertT x (NodeT     P0 l r) = NodeT P1 (insertT x l) r
>   insertT x (NodeT {n} P1 l r) = rewrite plusSuccRightSucc n n in
>                                          NodeT P0 l (insertT x r)

<!-- Lest equation of insertT looks much simpler than in Agda! -->

>   dealT : Vect n a -> DealT a n
>   dealT []        = EmpT
>   dealT (x :: xs) = insertT x (dealT xs)
>
>   sortT : Vect n Nat -> Vect n Nat
>   sortT xs = mergeT (dealT xs)


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

This time I'll use `<?=` as a type constructor for types that compare lifted `Nat`s.

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

TODO: describe this

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
