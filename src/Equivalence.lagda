---
title     : "Equivalence: Martin Löf equivalence"
layout    : page
permalink : /Equivalence
---

Much of our reasoning has involved equivalence.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have taken equivalence as a primitive,
but in fact it can be defined using the machinery of inductive
datatypes.

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

autocong : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {x y : A} → x ≡ y → f x ≡ f y
autocong refl = refl
\end{code}
Once more, a useful exercise is to carry out an interactive development.

## Tabular reasoning

A few declarations allow us to support the form of tabular reasoning that
we have used throughout the book.  We package the declarations into a module,
to match the format used in Agda's standard library.
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

For example, here is a repeat of the definitions of naturals and
of addition, and of the proof that `zero` is a right identity
of addition.  (We need to repeat all the definitions, rather than
importing some of them, because all of the relevant modules import
the definition of equivalence from the Agda standard library, and
hence importing any of them would report an attempt to redefine
equivalence.)

\begin{code}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

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

## Rewriting by an equation

Pretty much every module in the Agda standard library imports the
library's definition of equivalence, as does every other chapter in this
book. To avoid a conflict with the definition of equivalence given here,
we eschew imports and instead repeat the relevant definitions.

\begin{code}
data even : ℕ → Set where
  ev0 : even zero
  ev+2 : ∀ {n : ℕ} → even n → even (suc (suc n))

even-id : ∀ (m : ℕ) → even (m + zero) → even m
even-id m ev with m + zero | +-identity m
... | .m | refl = ev
\end{code}

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


