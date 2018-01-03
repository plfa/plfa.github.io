---
title     : "Relations: Inductive Definition of Relations"
layout    : page
permalink : /Relations
---

After having defined operations such as addition and multiplication,
the next step is to define relations, such as *less than or equal*.

## Imports

\begin{code}
open import Naturals using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Properties using (com+; com+zero; com+suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}

## Defining relations

The relation *less than or equal* has an infinite number of
instances.  Here are just a few of them:

   0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
             1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                       2 ≤ 2     2 ≤ 3     ...
                                 3 ≤ 3     ...
                                           ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
\begin{code}
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {m : ℕ} → zero ≤ m
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
\end{code}
Here `z≤n` and `s≤s` (with no spaces) are constructor names,
while `m ≤ m`, and `m ≤ n` and `suc m ≤ suc n` (with spaces)
are propositions.

Both definitions above tell us the same two things:

+ *Base case*: for all naturals `n`, the proposition `zero ≤ n` holds
+ *Inductive case*: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

+ *Base case*: for all naturals `n`, the constructor `z≤n` 
  produces evidence that `zero ≤ n` holds.
+ *Inductive case*: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

Here we have used the word *evidence* as interchangeable with the
word *proof*.  We will tend to say *evidence* when we want to stress
that proofs are just terms in Agda.

For example, here in inference rule notation is the proof that
`2 ≤ 4`.

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof.
\begin{code}
ex₁ : 2 ≤ 4
ex₁ = s≤s (s≤s z≤n)
\end{code}

## Implicit arguments

In the Agda definition, the two lines defining the constructors
use `∀`, very similar to our use of `∀` in propositions such as:

    com+ : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
*implicit* and need not be written explicitly.  Thus, we would write,
for instance, `com+ m n` for the proof that `m + n ≡ n + m`, but
here will write `z≤n` for the proof that `m ≤ m`, leaving the `m` implicit,
or if `m≤n` is evidence that `m ≤ n`, we write write `s≤s m≤n` for the
evidence that `suc m ≤ suc n`, leaving both `m` and `n` implicit.

It is possible to provide implicit arguments explicitly if we wish.
For instance, here is the Agda proof that `2 ≤ 4` repeated, with the
implicit arguments made explicit.
\begin{code}
ex₂ : 2 ≤ 4
ex₂ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))
\end{code}

## Proving properties of inductive definitions.

\begin{code}
infix 4 _≤_

refl≤ : ∀ (n : ℕ) → n ≤ n
refl≤ zero = z≤n
refl≤ (suc n) = s≤s (refl≤ n)

trans≤ : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
trans≤ z≤n n≤p = z≤n
trans≤ (s≤s m≤n) (s≤s n≤p) = s≤s (trans≤ m≤n n≤p)

antisym≤ : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
antisym≤ z≤n z≤n = refl
antisym≤ (s≤s m≤n) (s≤s n≤m) rewrite antisym≤ m≤n n≤m = refl

mono+≤ : ∀ (m p q : ℕ) → p ≤ q → m + p ≤ m + q
mono+≤ zero p q p≤q =  p≤q
mono+≤ (suc m) p q p≤q =  s≤s (mono+≤ m p q p≤q)

mono+≤′ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
mono+≤′ m n p m≤n rewrite com+ m p | com+ n p = mono+≤ p m n m≤n

mono+≤″ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
mono+≤″ m n p q m≤n p≤q = trans≤ (mono+≤′ m n p m≤n) (mono+≤ n p q p≤q)

inverse+∸≤ : ∀ (m n : ℕ) → m ≤ n → (n ∸ m) + m ≡ n
inverse+∸≤ zero n z≤n rewrite com+zero n  = refl
inverse+∸≤ (suc m) (suc n) (s≤s m≤n)
  rewrite com+suc m (n ∸ m) | inverse+∸≤ m n m≤n = refl

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

infix 4 _<_

<implies≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
<implies≤ m n m<n = ?

≤implies< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤implies< m n m≤n = ?
\end{code}

## Unicode

In this chapter we use the following unicode.

    ≡  U+2261  IDENTICAL TO (\==)
    ∀  U+2200  FOR ALL (\forall)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\Gl, \lambda)
