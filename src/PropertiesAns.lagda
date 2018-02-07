---
title     : "Properties Answers"
layout    : page
permalink : /PropertiesAns
---

\begin{code}
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _∸_)
open import Data.Nat.Properties.Simple using (+-assoc; +-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

\end{code}

*Swapping terms*

\begin{code}
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl
\end{code}

*Multiplication distributes over addition*

\begin{code}
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc p (m * p) (n * p) = refl
\end{code}

*Multiplication is associative*

\begin{code}
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl
\end{code}

*Multiplications is commutative*

\begin{code}
*-zero : ∀ (n : ℕ) → n * zero ≡ zero
*-zero zero = refl
*-zero (suc n) rewrite *-zero n = refl

+-*-suc : ∀ (m n : ℕ) → n * suc m ≡ n + n * m
+-*-suc m zero = refl
+-*-suc m (suc n) rewrite +-*-suc m n | +-swap m n (n * m) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zero n = refl
*-comm (suc m) n rewrite +-*-suc m n | *-comm m n = refl
\end{code}

*Monus from zero*

\begin{code}
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl
\end{code}

The proof does not require induction.

*Associativity of monus with addition*

\begin{code}
∸-+-assoc : ∀ (m n p : ℕ) → (m ∸ n) ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite 0∸n≡0 p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl
\end{code}


