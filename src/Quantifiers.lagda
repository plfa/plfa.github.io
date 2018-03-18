---
title     : "Quantifiers: Universals and Existentials"
layout    : page
permalink : /Quantifiers
---

This chapter introduces universal and existential quatification.

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_)
open Isomorphism.≃-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple using (+-suc)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
\end{code}

We assume [extensionality][extensionality].
\begin{code}
postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
\end{code}

[extensionality]: Equality/index.html#extensionality


## Universals

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  The variable `x` appears free in `B x` but bound in
`∀ (x : A) → B x`.  We formalise universal quantification using the
dependent function type, which has appeared throughout this book.

Evidence that `∀ (x : A) → B x` holds is of the form

    λ (x : A) → N

where `N` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L
M` provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.

Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds.
\begin{code}
∀-elim : ∀ {A : Set} {B : A → Set} → (∀ (x : A) → B x) → (M : A) → B M
∀-elim L M = L M
\end{code}
As with `→-elim`, the rule corresponds to function application.

Ordinary function types arise as the special case of dependent
function types where the range does not depend on a variable drawn
from the domain.  When an ordinary function is viewed as evidence of
implication, both its domain and range are viewed as types of
evidence, whereas when a dependent function is viewed as evidence of a
universal, its domain is viewed as a data type and its range is viewed
as a type of evidence.  This is just a matter of interpretation, since
in Agda data types and types of evidence are indistinguishable.

Dependent function types are sometimes referred to as dependent products,
because if `A` is a finite type with values `{ x₁ , ⋯ , xᵢ }`, and if
each of the types `B x₁ , ⋯ B xᵢ` has `m₁ , ⋯ , mᵢ` distinct members,
then `∀ (x : A) → B x` has `m₁ × ⋯ × mᵢ` members.  Because of the
association of `Π` with products, sometimes the notation `∀ (x : A) → B x`
is replaced by a notation such as `Π[ x ∈ A ] (B x)`.

### Exercise (`∀-distrib-×`)

Show that universals distribute over conjunction.
\begin{code}
∀-Distrib-× = ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
\end{code}
Compare this with the result (`→-distrib-×`) in Chapter [Connectives](Connectives).

### Exercise (`⊎∀-implies-∀⊎`)

Show that a disjunction of universals implies a universal of disjunctions.
\begin{code}
⊎∀-Implies-∀⊎ = ∀ {A : Set} { B C : A → Set } →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
\end{code}
Does the converse also hold? If so, prove; if not, explain why.


## Existentials

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `∃ (λ (x : A) → B x)` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  The variable `x` appears free in `B x` but bound in
`∃ (λ (x : A) → B x)`.

We formalise existential quantification by declaring a suitable
inductive type.
\begin{code}
data ∃ {A : Set} (B : A → Set) : Set where
  _,_ : (x : A) → B x → ∃ B
\end{code}
Evidence that `∃ (λ (x : A) → B x)` holds is of the form
`(M , N)` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.

Given evidence that `∃ (λ (x : A) → B x)` holds, and
given evidence that `∀ (x : A) → B x → C` holds, where `C` does
not contain `x` as a free variable, we may conclude that `C` holds.
\begin{code}
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set} →
  (∃ (λ (x : A) → B x)) → (∀ (x : A) → B x → C) → C
∃-elim (M , N) P = P M N
\end{code}
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ (x : A) → B x → C` to any value
`M` of type `A` and any `N` of type `B M`, and exactly such values
are provided by the evidence for `∃ (λ (x : A) → B x)`.

Agda makes it possible to define our own syntactic abbreviations.
\begin{code}
syntax ∃ {A} (λ x → B) = ∃[ x ∈ A ] B
\end{code}
This allows us to write `∃[ x ∈ A ] (B x)` in place of
`∃ (λ (x : A) → B x)`.

As an example, recall the definitions of `even` from
Chapter [Relations](Relations).  
\begin{code}
data even : ℕ → Set where
  ev0 : even zero
  ev+2 : ∀ {n : ℕ} → even n → even (suc (suc n))
\end{code}
A number is even if it is zero, or if it is two
greater than an even number.

We will show that a number is even if and only if it is twice some
other number.  That is, number `n` is even if and only if there exists
a number `m` such that twice `m` is `n`.

First, we need a lemma, which allows us to
simplify twice the successor of `m` to two
more than twice `m`.
\begin{code}
lemma : ∀ (m : ℕ) → 2 * suc m ≡ suc (suc (2 * m))
lemma m =
  begin
    2 * suc m
  ≡⟨⟩
    suc m + (suc m + zero)
  ≡⟨⟩
    suc (m + (suc (m + zero)))
  ≡⟨ cong suc (+-suc m (m + zero)) ⟩
    suc (suc (m + (m + zero)))
  ≡⟨⟩
    suc (suc (2 * m))
  ∎
\end{code}
The lemma is straightforward, and uses the lemma
`+-suc` from Chapter [Properties](Properties), which
allows us to simplify `m + suc n` to `suc (m + n)`.

Here is the proof in the forward direction.
\begin{code}  
ev-ex : ∀ {n : ℕ} → even n → ∃[ m ∈ ℕ ] (2 * m ≡ n)
ev-ex ev0 =  (zero , refl)
ev-ex (ev+2 ev) with ev-ex ev
... | (m , refl) = (suc m , lemma m)
\end{code}
Given an even number, we must show it is twice some
other number.  The proof is a function, which
given a proof that `n` is even
returns a pair consisting of `m` and a proof
that twice `m` is `n`.  The proof is by induction over
the evidence that `n` is even.

- If the number is even because it is zero, then we return a pair
consisting of zero and the (trivial) proof that twice zero is zero.

- If the number is even because it is two more than another even
number `n`, then we apply the induction hypothesis, giving us a number
`m` and a proof that `2 * m ≡ n`, which we match against `refl`.  We
return a pair consisting of `suc m` and a proof that `2 * suc m ≡ suc
(suc n)`, which follows from `2 * m ≡ n` and the lemma.

Here is the proof in the reverse direction.
\begin{code}
ex-ev : ∀ {n : ℕ} → ∃[ m ∈ ℕ ] (2 * m ≡ n) → even n
ex-ev (zero , refl) = ev0
ex-ev (suc m , refl) rewrite lemma m = ev+2 (ex-ev (m , refl))
\end{code}
Given a number that is twice some other number,
we must show that it is even.  The proof is a function,
which given a number `m` and a proof that `n` is twice `m`,
returns a proof that `n` is even.  The proof is by induction
over the number `m`.

- If it is zero, then we must show that twice zero is even,
which follows by rule `ev0`. 

- If it is `suc m`, then we must show that `2 * suc m` is
even.  After rewriting with our lemma, we must show that
`suc (suc (2 * m))` is even.  The inductive hypothesis tells
us `2 * m` is even, from which the desired result follows
by rule `ev+2`.

Negation of an existential is isomorphic to universal
of a negation.  Considering that existentials are generalised
disjuntion and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjuntion is isomorphic to a conjunction of negations.
\begin{code}
¬∃∀ : ∀ {A : Set} {B : A → Set} → (¬ ∃[ x ∈ A ] B x) ≃ ∀ (x : A) → ¬ B x
¬∃∀ =
  record
    { to      =  λ { ¬∃bx x bx → ¬∃bx (x , bx) }
    ; from    =  λ { ∀¬bx (x , bx) → ∀¬bx x bx }
    ; from∘to =  λ { ¬∃bx → extensionality (λ { (x , bx) → refl }) } 
    ; to∘from =  λ { ∀¬bx → refl } 
    }
\end{code}
In the `to` direction, we are given a value `¬∃bx` of type
`¬ ∃ (λ (x : A) → B x)`, and need to show that given a value
`x` of type `A` that `¬ B x` follows, in other words, from
a value `bx` of type `B x` we can derive false.  Combining
`x` and `bx` gives us a value `(x , bx)` of type `∃ (λ (x : A) → B x)`,
and applying `¬∃bx` to that yields a contradiction.

In the `from` direction, we are given a value `∀¬bx` of type
`∀ (x : A) → ¬ B x`, and need to show that from a value `(x , bx)`
of type `∃ (λ (x : A) → B x)` we can derive false.  Applying `∀¬bx`
to `x` gives a value of type `¬ B x`, and applying that to `bx` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.

*Exercise* Show `∃ (λ (x : A) → ¬ B x) → ¬ (∀ (x : A) → B x)`.

## Standard Prelude

Definitions similar to those in this chapter can be found in the standard library.
\begin{code}
import Data.Product using (∃)
\end{code}

## Unicode

This chapter introduces the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)


