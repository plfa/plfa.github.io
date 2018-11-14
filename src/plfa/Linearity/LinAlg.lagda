---
title     : "Linearity: Resources and Linear Algebra"
layout    : page
permalink : /Linearity/LinAlg/
---

\begin{code}
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Algebra.Structures using (module IsSemiring; IsSemiring)
\end{code}

\begin{code}
module plfa.Linearity.LinAlg
  {Mult : Set}
  (_+_ _*_ : Mult → Mult → Mult)
  (0# 1# : Mult)
  (*-+-isSemiring : IsSemiring _≡_ _+_ _*_ 0# 1#)
  where
\end{code}

\begin{code}
open import plfa.Linearity _+_ _*_ 0# 1# *-+-isSemiring
open import Function using (_∘_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec using (Vec; _∷_; [])
\end{code}

\begin{code}
∥_∥ℕ : Precontext → ℕ
∥ ∅     ∥ℕ = zero
∥ γ , _ ∥ℕ = suc ∥ γ ∥ℕ
\end{code}

\begin{code}
∥_∥Fin : ∀ {γ} {A} → γ ∋ A → Fin ∥ γ ∥ℕ
∥ Z   ∥Fin = zero
∥ S x ∥Fin = suc ∥ x ∥Fin
\end{code}

\begin{code}
∥_∥Vec : ∀ {γ} → Context γ → Vec Mult ∥ γ ∥ℕ
∥ ∅         ∥Vec = []
∥ Γ , π ∙ _ ∥Vec = π ∷ ∥ Γ ∥Vec
\end{code}

\begin{code}
Mat : Set → ℕ → ℕ → Set
Mat A n m = Vec (Vec A m) n
\end{code}

\begin{code}
∥_∥Mat : ∀ {γ δ} → Matrix γ δ → Mat Mult ∥ γ ∥ℕ ∥ δ ∥ℕ
∥_∥Mat {∅}     {δ} Δ = []
∥_∥Mat {γ , _} {δ} Δ = ∥ Δ Z ∥Vec ∷ ∥ (Δ ∘ S_) ∥Mat
\end{code}
