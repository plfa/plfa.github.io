
---
title     : "Basics: Functional Programming in Agda"
layout    : page
permalink : /Basics
---

\begin{code}
open import Data.Empty       using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
                             using (_≡_; refl; _≢_; trans; sym)
\end{code}

# Natural numbers

\begin{code}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
\end{code}

\begin{code}
congruent : ∀ {m n} → m ≡ n → suc m ≡ suc n
congruent refl = refl

injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
injective refl = refl

distinct : ∀ {m} → zero ≢ suc m
distinct ()
\end{code}

\begin{code}
_≟_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≟ zero =  yes refl
zero ≟ suc n =  no (λ()) 
suc m ≟ zero =  no (λ())
suc m ≟ suc n with m ≟ n
... | yes refl =  yes refl
... | no p =  no (λ r → p (injective r))
\end{code}

# Addition and its properties

\begin{code}
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)
\end{code}

\begin{code}
+-assoc : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-zero : ∀ m → m + zero ≡ m
+-zero zero = refl
+-zero (suc m) rewrite +-zero m = refl

+-suc : ∀ m n → m + (suc n) ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ m n → m + n ≡ n + m
+-comm m zero =  +-zero m
+-comm m (suc n) rewrite +-suc m n | +-comm m n = refl
\end{code}

# Equality and decidable equality for naturals




# Showing `double` injective

\begin{code}
double : ℕ → ℕ
double zero  =  zero
double (suc n)  =  suc (suc (double n))
\end{code}

\begin{code}
double-injective : ∀ m n → double m ≡ double n → m ≡ n
double-injective zero zero refl = refl
double-injective zero (suc n) ()
double-injective (suc m) zero ()
double-injective (suc m) (suc n) r =
   congruent (double-injective m n (injective (injective r)))
\end{code}

In Coq, the inductive proof for `double-injective`
is sensitive to how one inducts on `m` and `n`. In Agda, that aspect
is straightforward. However, Agda requires helper functions for
injection and congruence which are not required in Coq.

I can remove the use of `congruent` by rewriting with its argument.
Is there an easy way to remove the two uses of `injective`?
