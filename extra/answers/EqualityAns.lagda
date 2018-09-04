---
title     : "Equality Answers"
layout    : page
permalink : /EqualityAns
---

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm)
\end{code}


#### Exercise (`*-swap`)

Chains of equations.
\begin{code}
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎
\end{code}

Rewriting.
\begin{code}
+-swap′ : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap′ m n p
  rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p
  = refl
\end{code}

Pattern matching.
\begin{code}
+-swap″ : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap″ m n p with   m + (n + p)  |  +-assoc m n p
...              | .((m + n) + p) |  refl             =  f m n p
  where
  f : ∀ (m n p : ℕ) → (m + n) + p ≡ n + (m + p)
  f m n p with    m + n  |  +-comm m n
  ...        |  .(n + m) |  refl                      =  +-assoc n m p
\end{code}
or
\begin{code}
+-swap‴ : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap‴ m n p with   m + (n + p)  |  sym (+-assoc m n p)
...              | .((m + n) + p) |  refl                  =  f m n p
  where
  f : ∀ (m n p : ℕ) → (m + n) + p ≡ n + (m + p)
  f m n p with    m + n  |  +-comm m n
  ...        |  .(n + m) |  refl                           =  g m n p
    where
    g : ∀ (m n p : ℕ) → (n + m) + p ≡ n + (m + p)
    g m n p with    (n + m) + p  |  +-assoc n m p
    ...        |  .(n + (m + p)) |  refl                   =  refl
\end{code}



