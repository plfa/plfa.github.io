---
title     : "PUC-Assignment2: PUC Assignment 2"
layout    : page
permalink : /PUC-Assignment2/
---

\begin{code}
module PUC-Assignment2 where
\end{code}

## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

Please ensure your files execute correctly under Agda!

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm;
  ≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
open import plfa.Relations using (_<_; z<s; s<s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Unary using (Decidable)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.Relations using (_<_; z<s; s<s)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)
open plfa.Isomorphism.≃-Reasoning
open import plfa.Lists using (List; []; _∷_; [_]; [_,_]; [_,_,_]; [_,_,_,_];
  _++_; reverse; map; foldr; sum; All; Any; here; there; _∈_)
\end{code}

## Equality

#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations][plfa.Relations]
can be written in a more readable form by using an anologue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.



## Isomorphism

#### Exercise `≃-implies-≲`

Show that every isomorphism implies an embedding.
\begin{code}
postulate
  ≃-implies-≲ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≲ B  
\end{code}

#### Exercise `_⇔_` (recommended) {#iff}

Define equivalence of propositions (also known as "if and only if") as follows.
\begin{code}
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

open _⇔_
\end{code}
Show that equivalence is reflexive, symmetric, and transitive.

#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin][plfa.Naturals#Bin] and
[Bin-laws][plfa.Induction#Bin-laws]
define a datatype of bitstrings representing natural numbers.
\begin{code}
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin
\end{code}
And ask you to define the following functions:

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
Why is there not an isomorphism?


## Connectives

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier][plfa.Isomorphism#iff]
is isomorphic to `(A → B) × (B → A)`.

#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

#### Exercise `⊎-assoc`

Show sum is associative up to ismorphism. 

#### Exercise `⊥-identityˡ` (recommended)

Show zero is the left identity of addition.

#### Exercise `⊥-identityʳ`

Show zero is the right identity of addition. 

#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds.
\begin{code}
postulate
  ⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
\end{code}
This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

#### Exercise `⊎×-implies-×⊎`

Show that a disjunct of conjuncts implies a conjunct of disjuncts.
\begin{code}
postulate
  ⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
\end{code}
Does the converse hold? If so, prove; if not, give a counterexample.


## Negation

#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality][plfa.Relations#strict-inequality]
is irreflexive, that is, `n < n` holds for no `n`.


#### Exercise `trichotomy`

Show that strict inequality satisfies
[trichotomy][plfa.Relations#trichotomy],
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that one of the three must hold, and each implies the
negation of the other two.


#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, give a variant that does hold.


#### Exercise `Classical` (stretch)

Consider the following principles.

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.


#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it.
\begin{code}
Stable : Set → Set
Stable A = ¬ ¬ A → A
\end{code}
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.


## Quantifiers

#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction.
\begin{code}
postulate
  ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
\end{code}
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives][plfa.Connectives].

#### Exercise `⊎∀-implies-∀⊎`

Show that a disjunction of universals implies a universal of disjunctions.
\begin{code}
postulate
  ⊎∀-implies-∀⊎ : ∀ {A : Set} { B C : A → Set } →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
\end{code}
Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction.
\begin{code}
postulate
  ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
\end{code}

#### Exercise `∃×-implies-×∃`

Show that an existential of conjunctions implies a conjunction of existentials.
\begin{code}
postulate
  ∃×-implies-×∃ : ∀ {A : Set} { B C : A → Set } →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
\end{code}
Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-even-odd`

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

#### Exercise `∃-+-≤`

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal.
\begin{code}
postulate
  ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
    → ∃[ x ] (¬ B x)
      --------------
    → ¬ (∀ x → B x)
\end{code}
Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin][plfa.Naturals#Bin],
[Bin-laws][plfa.Induction#Bin-laws], and
[Bin-predicates][plfa.Relations#Bin-predicates]
define a datatype of bitstrings representing natural numbers.

    data Bin : Set where
      nil : Bin
      x0_ : Bin → Bin
      x1_ : Bin → Bin

And ask you to define the following functions and predicates.

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties.

    from (to n) ≡ n

    ----------
    Can (to n)

    Can x
    ---------------
    to (from x) ≡ x

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ x ](Can x)`.


## Decidable

#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality.
\begin{code}
postulate
  _<?_ : ∀ (m n : ℕ) → Dec (m < n)
\end{code}

#### Exercise `_≡ℕ?_`

Define a function to decide whether two naturals are equal.
\begin{code}
postulate
  _≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
\end{code}


#### Exercise `erasure`

Show that erasure relates corresponding boolean and decidable operations.
\begin{code}
postulate
  ∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
  ∨-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
  not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
\end{code}
  
#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from 
Chapter [Isomorphism][plfa.Isomorphism#iff],
operation on booleans and decidables, and also show the corresponding erasure.
\begin{code}
postulate
  _iff_ : Bool → Bool → Bool
  _⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
  iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋  
\end{code}

## Lists

#### Exercise `reverse-++-commute` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first.
\begin{code}
postulate
  reverse-++-commute : ∀ {A : Set} {xs ys : List A}
    → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
\end{code}

#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution.
\begin{code}
postulate
  reverse-involutive : ∀ {A : Set} {xs : List A}
    → reverse (reverse xs) ≡ xs
\end{code}

#### Exercise `map-compose`

Prove that the map of a composition is equal to the composition of two maps.
\begin{code}
postulate
  map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C}
    → map (g ∘ f) ≡ map g ∘ map f
\end{code}
The last step of the proof requires extensionality.

#### Exercise `map-++-commute`

Prove the following relationship between map and append.
\begin{code}
postulate
  map-++-commute : ∀ {A B : Set} {f : A → B} {xs ys : List A}
   →  map f (xs ++ ys) ≡ map f xs ++ map f ys
\end{code}

#### Exercise `map-Tree`

Define a type of trees with leaves of type `A` and internal
nodes of type `B`.
\begin{code}
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B
\end{code}
Define a suitabve map operator over trees.
\begin{code}
postulate
  map-Tree : ∀ {A B C D : Set}
    → (A → C) → (B → D) → Tree A B → Tree C D
\end{code}

#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example,

    product [ 1 , 2 , 3 , 4 ] ≡ 24

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows.
\begin{code}
postulate
  foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
\end{code}


#### Exercise `map-is-foldr`

Show that map can be defined using fold.
\begin{code}
postulate
  map-is-foldr : ∀ {A B : Set} {f : A → B} →
    map f ≡ foldr (λ x xs → f x ∷ xs) []
\end{code}
This requires extensionality.

#### Exercise `fold-Tree`

Define a suitable fold function for the type of trees given earlier.
\begin{code}
postulate
  fold-Tree : ∀ {A B C : Set}
    → (A → C) → (C → B → C → C) → Tree A B → C
\end{code}

#### Exercise `map-is-fold-Tree`

Demonstrate an anologue of `map-is-foldr` for the type of trees.

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows.
\begin{code}
downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
\end{code}
For example,
\begin{code}
_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl
\end{code}
Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`.
\begin{code}
postulate
  sum-downFrom : ∀ (n : ℕ)
    → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
\end{code}


#### Exercise `foldl`

Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example,

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z


#### Exercise `foldr-monoid-foldl`

Show that if `_⊕_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.


#### Exercise `Any-++-⇔` (recommended)

Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.


#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.


#### Exercise `¬Any≃All¬` (stretch)

First generalise composition to arbitrary levels, using
[universe polymorphism][plfa.Equality#unipoly].
\begin{code}
_∘′_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘′ f) x  =  g (f x)
\end{code}

Show that `Any` and `All` satisfy a version of De Morgan's Law.
\begin{code}
postulate
  ¬Any≃All¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
    → (¬_ ∘′ Any P) xs ≃ All (¬_ ∘′ P) xs
\end{code}

Do we also have the following?
\begin{code}
postulate
  ¬All≃Any¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
    → (¬_ ∘′ All P) xs ≃ Any (¬_ ∘′ P) xs
\end{code}
If so, prove; if not, explain why.


#### Exercise `any?` (stretch)

Just as `All` has analogues `all` and `all?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `any?` which determine whether a predicates holds
for some element of a list.  Give their definitions.


#### Exercise `filter?` (stretch)

Define the following variant of the traditional `filter` function on lists,
which given a list and a decidable predicate returns all elements of the
list satisfying the predicate.
\begin{code}
postulate
  filter? : ∀ {A : Set} {P : A → Set}
    → (P? : Decidable P) → List A → ∃[ ys ]( All P ys )
\end{code}
