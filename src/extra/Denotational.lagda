---
title     : "Denotational: Denotational Semantics"
layout    : page
permalink : /Denotational
---


## Imports

\begin{code}
module Denotational where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Typed
\end{code}

# Denotational semantics

\begin{code}
⟦_⟧ᵀ : Type → Set
⟦ `ℕ ⟧ᵀ      =  ℕ
⟦ A ⇒ B ⟧ᵀ   =  ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ

⟦_⟧ᴱ : Env → Set
⟦ ε ⟧ᴱ          =  ⊤
⟦ Γ , x ⦂ A ⟧ᴱ  =  ⟦ Γ ⟧ᴱ × ⟦ A ⟧ᵀ

⟦_⟧ⱽ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ Z ⟧ⱽ     ⟨ ρ , v ⟩ = v
⟦ S _ x ⟧ⱽ ⟨ ρ , v ⟩ = ⟦ x ⟧ⱽ ρ

⟦_⟧ : ∀ {Γ M A} → Γ ⊢ M ⦂ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ Ax x ⟧     ρ       =  ⟦ x ⟧ⱽ ρ
⟦ ⊢λ ⊢N ⟧    ρ       =  λ{ v → ⟦ ⊢N ⟧ ⟨ ρ , v ⟩ }
⟦ ⊢L · ⊢M ⟧  ρ       =  (⟦ ⊢L ⟧ ρ) (⟦ ⊢M ⟧ ρ)
⟦ ⊢zero ⟧    ρ       =  zero
⟦ ⊢suc ⊢M ⟧  ρ       =  suc (⟦ ⊢M ⟧ ρ)
⟦ ⊢pred ⊢M ⟧ ρ       =  pred (⟦ ⊢M ⟧ ρ)
  where
  pred : ℕ → ℕ
  pred zero     =  zero
  pred (suc n)  =  n
⟦ ⊢if0 ⊢L ⊢M ⊢N ⟧ ρ  =  if0 ⟦ ⊢L ⟧ ρ then ⟦ ⊢M ⟧ ρ else ⟦ ⊢N ⟧ ρ
  where
  if0_then_else_ : ∀ {A} → ℕ → A → A → A
  if0 zero  then m else n  =  m
  if0 suc _ then m else n  =  n
⟦ ⊢Y ⊢M ⟧    ρ       =  {!!}

{-
_ : ⟦ ⊢four ⟧ tt ≡ 4
_ = refl
-}

_ : ⟦ ⊢fourCh ⟧ tt ≡ 4
_ = refl
\end{code}


