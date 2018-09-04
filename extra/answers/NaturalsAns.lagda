---
title     : "NaturalsAns: Natural numbers (Answers)"
layout    : page
permalink : /NaturalsAns/
---

\begin{code}
module NaturalsAns where
\end{code}

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
\end{code}

#### Exercise (stretch: `ℕ¹`, `_+¹_ `, `_*¹_ `)

\begin{code}
data ℕ¹ : Set where
  one : ℕ¹
  suc : ℕ¹ → ℕ¹

_+¹_ : ℕ¹ → ℕ¹ → ℕ¹
one     +¹ n  =  suc n
(suc m) +¹ n  =  suc (m +¹ n)

_*¹_ : ℕ¹ → ℕ¹ → ℕ¹
one     *¹ n  =  n
(suc m) *¹ n  =  n +¹ (m *¹ n)

_ : suc one +¹ suc (suc one) ≡ suc (suc (suc (suc one)))
_ = refl

_ : suc one *¹ suc (suc one) ≡ suc (suc (suc (suc (suc one))))
_ = refl
\end{code}
