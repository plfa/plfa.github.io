---
title     : "Quantifiers: Universals and existentials"
layout    : page
permalink : /Quantifiers
---

This chapter introduces universal and existential quantification.

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
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
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

Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda values of a type and
evidence of a proposition are indistinguishable.

Dependent function types are sometimes referred to as dependent products,
because if `A` is a finite type with values `x₁ , ⋯ , xᵢ`, and if
each of the types `B x₁ , ⋯ , B xᵢ` has `m₁ , ⋯ , mᵢ` distinct members,
then `∀ (x : A) → B x` has `m₁ * ⋯ * mᵢ` members.  
Indeed, sometimes the notation `∀ (x : A) → B x`
is replaced by a notation such as `Π[ x ∈ A ] (B x)`,
where `Π` stands for product.  However, we will stick with the name
dependent function, because (as we will see) dependent product is ambiguous.


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
Does the converse hold? If so, prove; if not, explain why.


## Existentials

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  The variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.

We formalise existential quantification by declaring a suitable
inductive type.
\begin{code}
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
\end{code}
We define a convenient syntax for existentials as follows.
\begin{code}
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
\end{code}
This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.

Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`(M , N)` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.

Equivalently, we could also declare existentials as a record type.
\begin{code}
record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′
\end{code}
Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B M`.

Products arise a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda values
of a type and evidence of a proposition are indistinguishable.

Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xᵢ`, and if
each of the types `B x₁ , ⋯ B xᵢ` has `m₁ , ⋯ , mᵢ` distinct members,
then `Σ[ x ∈ A] B x` has `m₁ + ⋯ + mᵢ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.

Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universal also have a claim to the name dependent
product and since existential also have a claim to the name dependent sum.

A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit.
\begin{code}
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
\end{code}
The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.

Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds.
\begin{code}
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) → ∃[ x ] B x → C
∃-elim f ⟨ x , y ⟩ = f x y
\end{code}
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.

Indeed, the converse also holds, and the two together form an isomorphism.
\begin{code}
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
\end{code}
The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication][implication].

[implication]: Connectives/index.html#implication

### Exercise (`∃-distrib-⊎`)

Show that universals distribute over conjunction.
\begin{code}
∃-Distrib-⊎ = ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
\end{code}

### Exercise (`∃×-implies-×∃`)

Show that an existential of conjunctions implies a conjunction of existentials.
\begin{code}
∃×-Implies-×∃ = ∀ {A : Set} { B C : A → Set } →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
\end{code}
Does the converse hold? If so, prove; if not, explain why.


## An existential example

Recall the definitions of `even` and `odd` from Chapter [Relations](Relations).  
\begin{code}
data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc   : ∀ {n : ℕ} → even n → odd (suc n)
\end{code}
A number is even if it is zero or the successor of an odd number, and
odd if it the successor of an even number.

We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show

    even n   iff   ∃[ m ] (    m * 2 ≡ n)
    odd  n   iff   ∃[ m ] (1 + m * 2 ≡ n)

By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.

Here is the proof in the forward direction.
\begin{code}
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩
\end{code}
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd.

- If the number is even because it is zero, then we return a pair
consisting of zero and the (trivial) proof that twice zero is zero.

- If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2` ≡ suc n`, which is immediate after
substituting for `n`.

- If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + 2 * m = suc n`, which is immediate after
substituting for `n`.

This completes the proof in the forward direction.

Here is the proof in the reverse direction.
\begin{code}
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)
\end{code}
Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled.

- In the even case for `zero`, we must show `2 * zero` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `2 * suc m` is even.  The
inductive hypothesis tells us that `1 + 2 * m` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.

This completes the proof in the backward direction.

### Exercise (`∃-even′, ∃-odd′`)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

### Exercise (`∃-+-≤`)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.


## Existentials, Universals, and Negation

Negation of an existential is isomorphic to universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations.
\begin{code}
¬∃∀ : ∀ {A : Set} {B : A → Set} → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃∀ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } } 
    ; to∘from =  λ{ ∀¬xy → refl } 
    }
\end{code}
In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `(x , y)` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.

In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.



### Exercise (`∃¬-Implies-¬∀`)

Show `∃[ x ] ¬ B x → ¬ (∀ x → B x)`.

Does the converse hold? If so, prove; if not, explain why.


## Standard Prelude

Definitions similar to those in this chapter can be found in the standard library.
\begin{code}
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
\end{code}


## Unicode

This chapter uses the following unicode.

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    ∃  U+2203  THERE EXISTS (\ex, \exists)
