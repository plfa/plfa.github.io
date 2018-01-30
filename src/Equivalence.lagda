---
title     : "Equivalence: Equivalence and equational reasoning"
layout    : page
permalink : /Equivalence
---

Much of our reasoning has involved equivalence.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have taken equivalence as a primitive,
but in fact it can be defined using the machinery of inductive
datatypes.


## Imports

This chapter has no imports.  Pretty much every module in the Agda
standard library, and every chapter in this book, imports the standard
definition of equivalence. Since we define equivalence here, any
import would create a conflict.


## Equivalence

We declare equivalence as follows.
\begin{code}
data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x
\end{code}
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`.  Hence, every
value is equivalent to itself, and we have no other way of showing values
are equivalent.  Here we have quantified over all levels, so that
we can apply equivalence to types belonging to any level.

We declare the precedence of equivalence as follows.
\begin{code}
infix 4 _≡_
\end{code}
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to the left nor right; writing `x ≡ y ≡ z`
is illegal.


## Equivalence is an equivalence relation

An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equivalence, via the
constructor `refl`.  It is straightforward to show symmetry.
\begin{code}
sym : ∀ {ℓ} {A : Set ℓ} {x y : A} →  x ≡ y → y ≡ x
sym refl = refl
\end{code}
How does this proof work? The argument to `sym` has type `x ≡ y`,
but on the left-hand side of the equation the argument has been instantiated to the pattern `refl`,
which requires that `x` and `y` are the same.  Hence, for the right-hand side of the equation
we need a term of type `x ≡ x`, and `refl` will do.

It is instructive to create the definition of `sym` interactively.
Say we use a variable for the argument on the left, and a hole for the term on the right:

    sym : ∀ {ℓ} {A : Set ℓ} {x y : A} →  x ≡ y → y ≡ x
    sym r = {! !}

If we go into the hole and type `C-C C-,` then Agda reports:

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    r  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set .ℓ
    .ℓ : .Agda.Primitive.Level

If in the hole we type `C-C C-C r` then Agda will instantiate `r` to all possible constructors,
with one equation for each. There is only one possible constructor:

    sym : ∀ {ℓ} {A : Set ℓ} {x y : A} →  x ≡ y → y ≡ x
    sym refl = {! !}

If we go into the hole again and type `C-C C-,` then Agda now reports:

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set .ℓ
     .ℓ : .Agda.Primitive.Level

This is the key step---Agda has worked out that `x` and `y` must be the same to match the pattern `refl`!

Finally, if we go back into the hole and type `C-C C-R` it will
instantiate the hole with the one constructor that yields a value of
the expected type.

    sym : ∀ {ℓ} {A : Set ℓ} {x y : A} →  x ≡ y → y ≡ x
    sym refl = refl

This completes the definition as given above.

Transitivity is equally straightforward.
\begin{code}
trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
\end{code}
Again, a useful exercise is to carry out an interactive development, checking
how Agda's knowledge changes as each of the two arguments is
instantiated.

Equivalence also satisfies *congruence*.  If two terms are equivalent,
then they remain so after the same function is applied to both.
\begin{code}
cong : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl
\end{code}
Once more, a useful exercise is to carry out an interactive development.


## Tabular reasoning

A few declarations allow us to support the form of tabular reasoning
that we have used throughout the book.  We package the declarations
into a module, named `≡-Reasoning`, to match the format used in Agda's
standard library.
\begin{code}
module ≡-Reasoning {ℓ} {A : Set ℓ} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z =  trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning
\end{code}
Opening the module makes all of the definitions
available in the current environment.

As a simple example, let's look at the proof of transitivity
rewritten in tabular form.
\begin{code}
trans′ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′ {_} {_} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎
\end{code}
Tabular proofs begin with `begin`, end with `∎`
(which is sometimes pronounced "qed" or "tombstone")
and consist of a string of equations.  Due to the
fixity declarations, the body parses as follows.

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the following term.

    trans x≡y (trans y≡z refl)

We could replace all uses of tabular reasoning by a chain of
applications of `trans`, but the result would be far less perspicuous.
Also note that the syntactic trick behind `∎` means that the chain
always ends in the form `trans e refl` even though `e` alone would do,
where `e` is a proof of an equivalence.


## Tabular reasoning, another example

As a second example of tabular reasoning, we consider the proof that zero is a right identity for
addition.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict.
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)
\end{code}

We now repeat the proof that zero is a right identity.
\begin{code}
+-identity : ∀ (m : ℕ) → m + zero ≡ m
+-identity zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identity (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identity m) ⟩
    suc m
  ∎
\end{code}
The tabular reasoning here is similar to that in the
preceding section, the one addition being the use of
`_≡⟨⟩_`, which we use when no justification is required.
One can think of occurrences of `≡⟨⟩` as an equivalent
to `≡⟨ refl ⟩`.

Agda always treats a term as equivalent to its
simplified term.  The reason that one can write

    begin
      zero + zero
    ≡⟨⟩
      zero
    ∎

is because Agda treats `zero + zero` and `zero` as the
same thing.  This also means that one could instead write
the proof in the form

    begin
      zero
    ≡⟨⟩
      zero + zero
    ∎

and Agda would not object. Agda only checks that the terms
separated by `≡⟨⟩` are equivalent; it's up to us to write
them in an order that will make sense to the reader.

## Rewriting by an equation

Consider a property of natural numbers, such as being even.
\begin{code}
data even : ℕ → Set where
  ev0 : even zero
  ev+2 : ∀ {n : ℕ} → even n → even (suc (suc n))
\end{code}

In the previous section, we proved `m + zero ≡ m`.
So given evidence that `even (m + zero)` holds,
we ought also to be able to take that as evidence
that `even m` holds.  Here is a proof of that claim
in Agda.

[CONTINUE FROM HERE]

even-id : ∀ (m : ℕ) → even (m + zero) → even m
even-id m ev with m + zero | +-identity m
...             | .m       | refl          = ev

\begin{code}
even-id : ∀ (m : ℕ) → even (m + zero) → even m
even-id m ev with m + zero | +-identity m
...             | u        | v             = {!!}
\end{code}


Goal: even m
————————————————————————————————————————————————————————————
ev : even u
v  : u ≡ m
u  : ℕ
m  : ℕ


    even-id : ∀ (m : ℕ) → even (m + zero) → even m
    even-id m ev with +-identity m
    ...             | refl         = ev

> Cannot solve variable m of type ℕ with solution m + zero because
> the variable occurs in the solution, or in the type one of the
> variables in the solution
> when checking that the pattern refl has type (m + zero) ≡ m

Including the lines
\begin{code}
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}
\end{code}
permits the use of equivalences in rewrites. 

\begin{code}
even-id′ : ∀ (m : ℕ) → even (m + zero) → even m
even-id′ m ev rewrite +-identity m = ev
\end{code}


