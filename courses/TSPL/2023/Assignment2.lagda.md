---
title     : "Assignment2: TSPL Assignment 2"
permalink : /TSPL/2023/Assignment2/
---

```
module Assignment2 where
```

## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using Gradescope. Go to the course page under Learn.
Select `Assessment`, then select `Assignment Submission`.
Please ensure your files execute correctly under Agda!


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

Furthermore, you are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself, or your group in the case of group practicals).


## Connectives

```
module Connectives where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open Eq.≡-Reasoning
  open import Data.Nat using (ℕ)
  open import Function using (_∘_)
  open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
  open plfa.part1.Isomorphism.≃-Reasoning
```


```
  open import plfa.part1.Connectives
    hiding (⊎-weak-×; ⊎×-implies-×⊎)
```

#### Exercise `⇔≃×` (practice)

Show that `A ⇔ B` as defined [earlier](/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.

```agda
  -- Your code goes here
```


#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

```agda
  -- Your code goes here
```

#### Exercise `⊎-assoc` (practice)

Show sum is associative up to isomorphism.

```agda
  -- Your code goes here
```

#### Exercise `⊥-identityˡ` (recommended)

Show empty is the left identity of sums up to isomorphism.

```agda
  -- Your code goes here
```

#### Exercise `⊥-identityʳ` (practice)

Show empty is the right identity of sums up to isomorphism.

```agda
  -- Your code goes here
```

#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds:
```agda
  postulate
    ⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
```
This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

```agda
  -- Your code goes here
```


#### Exercise `⊎×-implies-×⊎` (practice)

Show that a disjunct of conjuncts implies a conjunct of disjuncts:
```agda
  postulate
    ⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
```
Does the converse hold? If so, prove; if not, give a counterexample.

```agda
  -- Your code goes here
```



## Negation

```
module Negation where
```

## Imports

```agda
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.Nat using (ℕ; zero; suc)
  open import plfa.part1.Isomorphism using (_≃_; extensionality)
  open import plfa.part1.Connectives
  open import plfa.part1.Negation hiding (Stable)
```

#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality](/Relations/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.

```agda
  -- Your code goes here
```


#### Exercise `trichotomy` (practice)

Show that strict inequality satisfies
[trichotomy](/Relations/#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.

```agda
  -- Your code goes here
```

#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

```agda
  -- Your code goes here
```


Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?


#### Exercise `Classical` (stretch)

Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.

```agda
  -- Your code goes here
```


#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it:
```agda
  Stable : Set → Set
  Stable A = ¬ ¬ A → A
```
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

```agda
  -- Your code goes here
```


## Quantifiers

```
module Quantifiers where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Relation.Nullary using (¬_)
  open import Function using (_∘_)
  open import plfa.part1.Isomorphism using (_≃_; extensionality; ∀-extensionality)
  open import plfa.part1.Connectives
    hiding (Tri)
  open import plfa.part1.Quantifiers
    hiding (∀-distrib-×; ⊎∀-implies-∀⊎; ∃-distrib-⊎; ∃×-implies-×∃; ∃¬-implies-¬∀; Tri)
```

#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
```agda
  postulate
    ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
      (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
```
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives](/Connectives/).

Hint: you will need to use [`∀-extensionality`](/Isomorphism/#extensionality).

#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
```agda
  postulate
    ⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
      (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
```
Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×` (practice)

Consider the following type.
```agda
  data Tri : Set where
    aa : Tri
    bb : Tri
    cc : Tri
```
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.

Hint: you will need to use [`∀-extensionality`](/Isomorphism/#extensionality).


#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
```agda
  postulate
    ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
      ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
```

#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
```agda
  postulate
    ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
      ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
```
Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.


#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

```agda
  -- Your code goes here
```

#### Exercise `∃-+-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

```agda
  -- Your code goes here
```


#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
```agda
  postulate
    ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
      → ∃[ x ] (¬ B x)
        --------------
      → ¬ (∀ x → B x)
```
Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin](/Naturals/#Bin),
[Bin-laws](/Induction/#Bin-laws), and
[Bin-predicates](/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ] Can b`.

We recommend proving the following lemmas which show that, for a given
binary number `b`, there is only one proof of `One b` and similarly
for `Can b`.

    ≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′

    ≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′

Many of the alternatives for proving `to∘from` turn out to be tricky.
However, the proof can be straightforward if you use the following lemma,
which is a corollary of `≡Can`.

    proj₁≡→Can≡ : {cb cb′ : ∃[ b ] Can b} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′

```agda
  -- Your code goes here
```



## Decidable

```
module Decidable where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open Eq.≡-Reasoning
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation using ()
    renaming (contradiction to ¬¬-intro)
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥; ⊥-elim)
  open import plfa.part1.Relations using (_<_; z<s; s<s)
  open import plfa.part1.Isomorphism using (_⇔_)
```

```
  open import plfa.part1.Decidable
    hiding (_<?_; _≡ℕ?_; ∧-×; ∨-⊎; not-¬; _iff_; _⇔-dec_; iff-⇔)
```

#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality:
```agda
  postulate
    _<?_ : ∀ (m n : ℕ) → Dec (m < n)
```

```agda
  -- Your code goes here
```

#### Exercise `_≡ℕ?_` (practice)

Define a function to decide whether two naturals are equal:
```agda
  postulate
    _≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
```

```agda
  -- Your code goes here
```


#### Exercise `erasure` (practice)

Show that erasure relates corresponding boolean and decidable operations:
```agda
  postulate
    ∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
    ∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
    not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
```

#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from
Chapter [Isomorphism](/Isomorphism/#iff),
operation on booleans and decidables, and also show the corresponding erasure:
```agda
  postulate
    _iff_ : Bool → Bool → Bool
    _⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
    iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
```

```agda
  -- Your code goes here
```

#### Exercise `False` (practice)

Give analogues of `True`, `toWitness`, and `fromWitness` which work
with *negated* properties. Call these `False`, `toWitnessFalse`, and
`fromWitnessFalse`.


#### Exercise `Bin-decidable` (stretch)

Recall that Exercises
[Bin](/Naturals/#Bin),
[Bin-laws](/Induction/#Bin-laws), and
[Bin-predicates](/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following predicates:

    One  : Bin → Set
    Can  : Bin → Set

Show that both of the above are decidable.

    One? : ∀ (b : Bin) → Dec (One b)
    Can? : ∀ (b : Bin) → Dec (Can b)
