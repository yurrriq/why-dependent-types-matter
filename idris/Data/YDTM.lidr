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

== Introduction

> %access public export
>
> data Order : Type where
>      le : Order
>      ge : Order
>
> order : Nat -> Nat -> Order
> order Z y         = le
> order (S x) Z     = ge
> order (S x) (S y) = order x y
>
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

> total
> mergeL : List Nat -> List Nat -> List Nat
> mergeL []        ys             = ys
> mergeL xs        []             = xs
> mergeL (x :: xs) (y :: ys) with (order x y)
>   | le = x :: mergeL xs (y :: ys)
>   | ge = y :: mergeL (x :: xs) ys

Still, sortL is not recognized as total.

>sortL : List Nat -> List Nat
>sortL xs with (deal xs)
>  | (ys , []) = ys
>  | (ys , zs) = mergeL (sortL ys) (sortL zs)

<!-- Section 3.1 : Totality is Good for more than the Soul -->

== Totality is Good for more than the Soul

I'll use the `Refl` provide by Idris.

<!-- Section 3.2 : Defusing General Recursion -->

== Defusing General Recursion

> data Parity : Type where
>      p0 : Parity
>      p1 : Parity
>
> using (X : Type)
>   data DealT : X -> Type where
>     empT  : DealT X
>     leafT : X -> DealT X
>     nodeT : Parity -> DealT X -> DealT X -> DealT X
>
> insertT : {X : Type} -> X -> DealT X -> DealT X
> insertT x empT           = leafT x
> insertT x (leafT y)      = nodeT p0 (leafT y) (leafT x)
> insertT x (nodeT p0 l r) = nodeT p1 (insertT x l) r
> insertT x (nodeT p1 l r) = nodeT p0 l (insertT x r)
>
> dealT : {X : Type} -> List X -> DealT X
> dealT []       = empT
> dealT (x :: xs) = insertT x (dealT xs)
>
> mergeT : DealT Nat -> List Nat
> mergeT empT          = []
> mergeT (leafT x)     = x :: []
> mergeT (nodeT p l r) = merge (mergeT l) (mergeT r)
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
was first and the index was second - if you're using an older version of Idris,
this code will not work.

> vtail : {X : Type} -> {n : Nat} -> Vect (S n) X -> Vect n X
> vtail (x :: xs) = xs

Note that we can skip implicit arguments that can be deduced, but
we must use lower-case letters to denote type variables. So we can write:

```idris
vtail : Vect (S n) x -> Vect n x
```

instead of

```idris
vtail : {X : Type} -> {n : Nat} -> Vect (S n) X -> Vect n X
```

but we can't write:

```idris
vtail : Vect (S n) X -> Vect n X
```

From now on I will avoid implicit arguments in type signatures, unless they will
be pattern-matched in the definition.

Idris allows me to use `<@>` as an infix operator - goodbye `vapp`! The tricky
part is that if we want to use `<@>` as an infix operator, we need to declare
its fixity and precedence. If we want to use it as infix operator in the
recursive call of its definition we need to declare fixity of `<@>` before
defining `<@>` itself.

> infixl 9 <@>
>
> (<@>) : Vect n (a -> b) -> Vect n a -> Vect n b
> (<@>) Nil       Nil       = Nil
> (<@>) (f :: fs) (s :: ss) = (f s) :: (fs <@> ss)

As a reminder, here'e the definition of addition:

```idris
_+_ : Nat -> Nat -> Nat
Z  + n = n
S m + n = S (m + n)
```

And here's definition of appending two Vectors:

```idris
(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)
```

In both cases I'll be using the built-in Idris definitions.

Idris requires that implicit arguments be named explicitly in the pattern
matching.

> vec : {n : Nat} -> a -> Vect n a
> vec {n=Z}   x = Nil
> vec {n=S a} x = x :: (vec x)
>
> xpose : Vect m (Vect n a) -> Vect n (Vect m a)
> xpose Nil          = vec Nil
> xpose (xj :: xi'j) = vec (::) <@> xj <@> (xpose xi'j)

Above we defined `xpose` using our definitions of `vec` and `<@>`. These two
functions make `Vect` an `Applicative` -- `vec` is pure, `<@>` is application
(in Haskell and Idris usually named `<$>`). Idris has a very cool thing, called
idiom brackets, that allows us to rewrite:

```idris
pure f <$> x <$> y
```
as

```idris
[| f x |]
```

Here's an alternative definition of `xpose` that uses idiom brackets (remember
that it uses Idris's built-in definitions of `pure` and `<$>` instead of our
`vapp` and `<@>`).

> xpose' : Vect m (Vect n a) -> Vect n (Vect m a)
> xpose' Nil          = [| Nil |]
> xpose' (xj :: xi'j) = [| xj :: xpose' xi'j |]

<!-- Section 4.1 -->

== Static Indexing and Proofs

> vrevacc : Vect n a -> Vect m a -> Vect (n + m) a
> vrevacc Nil       ys = ys
> vrevacc (x :: xs) ys = ?zonk --vrevacc xs (x :: ys)

Again, we can't just fill in the right code because Idris doesn't know that `m +
(1 + n)` equals `1 + (m + n)`. Once again have to prove it, but this time we
will not be reinventing the wheel. We will use Idris's proofs of basic
properties provided by `prelude`.

We need to prove that:

```idris
plus n (S m) = S (plus n m)
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
reverse its sides:

We rewrote the goal to a form which equals to our value.

<!-- FIXME: Since the equality is now obvious we apply trvial tactic and end -->
<!-- the proof with qed: -->
<!-- We need to place the proof in the source code. We can use :addproof -->
<!-- to have the generated proof automcatically added at the end of source -->
<!-- file. -->

<!-- Section 4.2 -->
== Sized Merge-Sort

> mergeS : Vect n Nat -> Vect m Nat -> Vect (n + m) Nat
> mergeS Nil       ys  = ys
> mergeS (x :: xs) Nil ?= x :: xs
> mergeS (x :: xs) (y :: ys) with (order x y)
>   | le  = x :: mergeS xs (y :: ys)
>   | ge ?= y :: mergeS (x :: xs) ys
>
> mergeS_lemma_1 = proof
>   intros
>   rewrite sym (plusZeroRightNeutral n)
>   trivial
>
> mergeS_lemma_2 = proof
>   intros
>   rewrite (plusSuccRightSucc n n1)
>   trivial
>
> p2n : Parity -> Nat
> p2n p0 = Z
> p2n p1 = S Z

I renamed the data constructors to silence Idris warnings.

> using (X : Type)
>   data DealTS : X -> Nat -> Type where
>     empTS  : DealTS X Z
>     leafTS : X -> DealTS X (S Z)
>     nodeTS : {n : Nat} -> (p : Parity) -> DealTS X (p2n p + n) -> DealTS X n
>            -> DealTS X ((p2n p + n) + n)
>
> mergeTS : DealTS Nat n -> Vect n Nat
> mergeTS empTS          = Nil
> mergeTS (leafTS x)     = x :: Nil
> mergeTS (nodeTS p l r) = mergeS (mergeTS l) (mergeTS r)
>
> insertTS : {n : Nat} -> {X : Type} -> X -> DealTS X n -> DealTS X (S n)
> insertTS x empTS                = leafTS x
> insertTS x (leafTS y         )  = nodeTS p0 (leafTS y) (leafTS x)
> insertTS x (nodeTS     p0 l r)  = nodeTS p1 (insertTS x l) r
> insertTS x (nodeTS {n} p1 l r) ?= nodeTS p0 l (insertTS x r)

<!-- Lest equation of insertTS looks much simpler than in Agda! -->

> insertTS_lemma_1 = proof
>   intros
>   rewrite sym (plusSuccRightSucc n n)
>   trivial
>
> dealTS : Vect n a -> DealTS a n
> dealTS Nil       = empTS
> dealTS (x :: xs) = insertTS x (dealTS xs)
>
> sortTS : Vect n Nat -> Vect n Nat
> sortTS xs = mergeTS (dealTS xs)


<!-- Section 5.1 -->

== Evidence of Ordering

Sadly, Idris does not allow Unicode in operators, so I have to use a name other
than `≤` and `<=` (which is already defined).

> infix 4 <!=
>
> data (<!=) : Nat -> Nat -> Type where
>      le0 : Z <!= y
>      leS : x <!= y -> S x <!= S y
>
> data OrderD : Nat -> Nat -> Type where
>      leD : x <!= y -> OrderD x y
>      geD : y <!= x -> OrderD x y
>
> orderD : (x : Nat) -> (y : Nat) -> OrderD x y
> orderD Z    y     = leD le0
> orderD (S x) Z    = geD le0
> orderD (S x) (S y) with (orderD x y)
>   | leD xley = leD (leS xley)
>   | geD ylex = geD (leS ylex)
>
> leRefl : {x : Nat} -> x <!= x
> leRefl {x=Z}   = le0
> leRefl {x=S _} = leS leRefl
>
> leTrans : {x, y, z : Nat} -> x <!= y -> y <!= z -> x <!= z
> leTrans le0      yz       = le0
> leTrans (leS xy) (leS yz) = leS (leTrans xy yz)
>
> leASym : {x, y : Nat} -> x <!= y -> y <!= x -> x = x
> leASym le0      le0      = Refl
> leASym (leS xy) (leS yx) = Refl

<!-- Section 5.2 -->

== Locally Sorted Lists

> data LNat : Type where
>      ZL   : LNat
>      SL   : LNat -> LNat
>      infL : LNat
>
> lift : Nat -> LNat
> lift Z     = ZL
> lift (S x) = SL (lift x)

This time I'll use `<?=` as a type constructor for types that compare
lifted `Nat`s.

> infix 4 <?=
>
> data (<?=) : LNat -> LNat -> Type where
>      le0L  : ZL <?= y
>      leSL  : x <?= y -> SL x <?= SL y
>      leIL  : x <?= infL
>
> data CList : LNat -> Type where
>      cnil  : CList inf
>      ccons : (x : Nat) -> (lift x) <?= y -> CList y -> CList (lift x)
>
> clist : CList ZL
> clist = ccons Z le0L (
>         ccons (S (S Z)) (leSL (leSL le0L)) (
>         ccons (S (S Z))  leIL cnil))
>
> data OList : Nat -> Type where
>      onil  : OList b
>      ocons : (x : Nat) -> b <!= x -> OList x -> OList b
>
> olist : OList Z
> olist = ocons (S Z) le0 onil
>
> olist2 : OList Z
> olist2 = ocons (S Z) le0 (ocons (S (S Z)) (leS le0) onil)

Again, no issues with termination checker in `mergeO`.

> mergeO : OList b -> OList b -> OList b
> mergeO onil ys = ys
> mergeO (ocons x blex xs) onil = ocons x blex xs
> mergeO (ocons x blex xs) (ocons y bley ys) with (orderD x y)
>   | leD xley = ocons x blex (mergeO xs (ocons y xley ys))
>   | geD ylex = ocons y bley (mergeO (ocons x ylex xs) ys)
>
> mergeTO : DealT Nat -> OList Z
> mergeTO empT          = onil
> mergeTO (leafT x)     = ocons x le0 onil
> mergeTO (nodeT p l r) = mergeO (mergeTO l) (mergeTO r)
>
> sortO : List Nat -> OList Z
> sortO xs = mergeTO (dealT xs)
