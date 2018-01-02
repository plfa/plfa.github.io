---
title     : "Exercises: Exercises"
layout    : page
permalink : /Exercises
---

## Imports

\begin{code}
open import Data.Nat using (ℕ; suc; zero; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
\end{code}

## Exercises

\begin{code}
_∸_ : ℕ → ℕ → ℕ
m       ∸ zero     =  m         -- (vii)
zero    ∸ (suc n)  =  zero      -- (viii)
(suc m) ∸ (suc n)  =  m ∸ n     -- (ix)

infixl 6 _∸_

assoc+ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
assoc+ zero n p = refl
assoc+ (suc m) n p rewrite assoc+ m n p = refl

com+zero : ∀ (n : ℕ) → n + zero ≡ n
com+zero zero = refl
com+zero (suc n) rewrite com+zero n = refl

com+suc : ∀ (m n : ℕ) → n + suc m ≡ suc (n + m)
com+suc m zero = refl
com+suc m (suc n) rewrite com+suc m n = refl

com+ : ∀ (m n : ℕ) → m + n ≡ n + m
com+ zero n rewrite com+zero n = refl
com+ (suc m) n rewrite com+suc m n | com+ m n = refl

dist*+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
dist*+ zero n p = refl
dist*+ (suc m) n p rewrite dist*+ m n p | assoc+ p (m * p) (n * p) = refl

assoc* : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
assoc* zero n p = refl
assoc* (suc m) n p rewrite dist*+ n (m * n) p | assoc* m n p = refl

com*zero : ∀ (n : ℕ) → n * zero ≡ zero
com*zero zero = refl
com*zero (suc n) rewrite com*zero n = refl

swap+ : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
swap+ m n p rewrite sym (assoc+ m n p) | com+ m n | assoc+ n m p = refl

com*suc : ∀ (m n : ℕ) → n * suc m ≡ n + n * m
com*suc m zero = refl
com*suc m (suc n) rewrite com*suc m n | swap+ m n (n * m) = refl

com* : ∀ (m n : ℕ) → m * n ≡ n * m
com* zero n rewrite com*zero n = refl
com* (suc m) n rewrite com*suc m n | com* m n = refl

zero∸ : ∀ (n : ℕ) → zero ∸ n ≡ zero
zero∸ zero = refl
zero∸ (suc n) = refl

assoc∸ : ∀ (m n p : ℕ) → (m ∸ n) ∸ p ≡ m ∸ (n + p)
assoc∸ m zero p = refl
assoc∸ zero (suc n) p rewrite zero∸ p = refl
assoc∸ (suc m) (suc n) p rewrite assoc∸ m n p = refl
\end{code}


