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

Function types arise as a special case of dependent function types,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda data types and types of
evidence are indistinguishable.

Dependent function types are sometimes referred to as dependent products,
because if `A` is a finite type with values `{ x₁ , ⋯ , xᵢ }`, and if
each of the types `B x₁ , ⋯ B xᵢ` has `m₁ , ⋯ , mᵢ` distinct members,
then `∀ (x : A) → B x` has `m₁ × ⋯ × mᵢ` members.  Because of this
association, sometimes the notation `∀ (x : A) → B x`
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

Equivalently, we could also declare existentials as a record type.
\begin{code}
record ∃′ {A : Set} (B : A → Set) : Set where
  field
    proj₁ : A
    proj₂ : B proj₁
\end{code}
Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ( M , N )

where `M` is a term of type `A` and `N` is a term of type `B M`.

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

Products arise a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when viewed as
evidence of an existential, the first component is viewed as an
element of a datatype and the second component is viewed as evidence
of a proposition that depends on the first component.  This difference
is largely a matter of interpretation, since in Agda data types and
types of evidence are indistinguishable.

Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `{ x₁ , ⋯ , xᵢ }`, and if
each of the types `B x₁ , ⋯ B xᵢ` has `m₁ , ⋯ , mᵢ` distinct members,
then `∃ (λ (x : A) → B x)` has `m₁ + ⋯ + mᵢ` members.  Because of this
association, sometimes the notation `∃ (λ (x : A) → B x)`
is replaced by a notation such as `Σ[ x ∈ A ] (B x)`,
where `Σ` stands for sum.

Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, because universals also have
a claim to the name dependent product, and because existentials
have a claim to the name dependent sum.





Agda makes it possible to define our own syntactic abbreviations.
\begin{code}
∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
\end{code}
This allows us to write `∃[ x ] (B x)` in place of `∃ (λ x → B x)`.
We could also define a syntax that makes the argument explicit.
\begin{code}
Σ-syntax = ∃
syntax Σ-syntax {A} (λ x → B) = Σ[ x ∈ A ] B
\end{code}
Both forms of syntax are provided by the Agda standard library.
We will usually use the first, as it is more compact.

As an example, recall the definitions of `even` and `odd` from
Chapter [Relations](Relations).  
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
some other number.

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
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    2 * m ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + 2 * m ≡ n)

even-∃ even-zero =  zero , refl
even-∃ (even-suc o) with odd-∃ o
...                    | m , refl = suc m , lemma m

odd-∃  (odd-suc e)  with even-∃ e
...                    | m , refl = m , refl
\end{code}
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `2 * m ≡ n` or `1 + 2 * m ≡ n`.
(By convention, one tends to put a constant at the
end of a term, so why have we chosen here
to write `1 + 2 * m` rather than `2 * m + 1`?)
We induct over the evidence that `n` is even or odd.

- If the number is even because it is zero, then we return a pair
consisting of zero and the (trivial) proof that twice zero is zero.

- If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + 2 * m ≡ n`. We return a pair consisting of `suc m`
and evidence that `2 * (suc m)` ≡ suc n`, which after substituting for
`n` means we need to show `2 * (suc m) ≡ 2 + 2 * m`, which follows
from our lemma.

- If the number is odd because it is the successor of an even
number, then we apply the induction hypothesis to give a number `m`
and evidence that `2 * m ≡ n`. We return a pair conisting of `suc m`
and evidence that `1 + 2 * m = suc n`, which is immediate
after substituting for `n`.

This completes the proof in the forward direction.

Here is the proof in the reverse direction.
\begin{code}
∃-even : ∀ {n : ℕ} → ∃[ m ] (   2 * m ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + 2 * m ≡ n) →  odd n

∃-even ( zero , refl)                  =  even-zero
∃-even (suc m , refl) rewrite lemma m  =  even-suc (∃-odd (m , refl))

∃-odd  (    m , refl)                  =  odd-suc (∃-even (m , refl))
\end{code}
Given a number that is twice some other number we must show
it is even, and a number that is one more than twice some other
number we must show it is odd.  We induct over the evidence
of the existential, and in particular the number that is doubled.

- In the even case, if it is `zero`, then we must show `2 * zero` is
even, which follows by `even-zero`.

- In the even case, if it is `suc n`, then we must show `2 * suc m` is
even.  After rewriting with our lemma, we must show that `2 + 2 * m`
is even. The inductive hypothesis tells us that `1 + 2 * m` is odd,
from which the desired result follows by `even-suc`.

- In the odd case, then we must show `1 + 2 * suc m` is odd.  The
inductive hypothesis tell us that `2 * m` is even, from which the
desired result follows by `odd-suc`.

This completes the proof in the backward direction.

Negation of an existential is isomorphic to universal
of a negation.  Considering that existentials are generalised
disjuntion and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjuntion is isomorphic to a conjunction of negations.
\begin{code}
¬∃∀ : ∀ {A : Set} {B : A → Set} → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃∀ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy (x , y) }
    ; from    =  λ{ ∀¬xy (x , y) → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ (x , y) → refl } } 
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
`∀ x → ¬ B x`, and need to show that from a value `(x , y)`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.



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

### Exercise (`∃¬-Implies-¬∀`)

Show `∃[ x ] ¬ B x → ¬ (∀ x → B x)`.

Does the converse hold? If so, prove; if not, explain why.


## Standard Prelude

Definitions similar to those in this chapter can be found in the standard library.
\begin{code}
import Data.Product using (∃;_,_)
\end{code}


## Unicode

This chapter uses the following unicode.

    ∃  U+2203  THERE EXISTS (\ex, \exists)


