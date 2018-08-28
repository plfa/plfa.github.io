---
title     : "Linearity: Introduction to the Linear Lambda Calculus"
layout    : page
permalink : /Linearity/
---

\begin{code}
open import Algebra using (Semiring)
\end{code}

\begin{code}
module plfa.Linearity {c} {ℓ} (MultSemiring : Semiring c ℓ) where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; refl)
open Semiring MultSemiring
  renaming (Carrier to Mult)
  using (0#; 1#; _+_; _*_)
\end{code}


\begin{code}
infixl 5 _,_
infixl 5 _,_·_
\end{code}

\begin{code}
data Type : Set c where
  [_·_]⊸_ : Mult → Type → Type → Type
  `ℕ      : Type
\end{code}

\begin{code}
data Precontext : Set c where
  ∅   : Precontext
  _,_ : Precontext → Type → Precontext
\end{code}

\begin{code}
_ : Precontext
_ = ∅ , [ 1# · `ℕ ]⊸ `ℕ , `ℕ
\end{code}

\begin{code}
data Context : Precontext → Set c where
  ∅     : Context ∅
  _,_·_ : ∀ {Γ} → Context Γ → Mult → (A : Type) → Context (Γ , A)
\end{code}

\begin{code}
_ : Context (∅ , [ 1# · `ℕ ]⊸ `ℕ , `ℕ)
_ = ∅ , 0# · [ 1# · `ℕ ]⊸ `ℕ , 1# · `ℕ
\end{code}

\begin{code}
_++_ : ∀ {Γ} → Context Γ → Context Γ → Context Γ
∅ ++ ∅ = ∅
(Δ , ρ · A) ++ (Δ′ , ρ′ · .A) = Δ ++ Δ′ , ρ + ρ′ · A
\end{code}

\begin{code}
0·_ : (Γ : Precontext) → Context Γ
0·  ∅      = ∅
0· (Γ , A) = 0· Γ , 0# · A
\end{code}

\begin{code}
data _·_∈_ : {Γ : Precontext} → Mult → Type → Context Γ → Set where

  Z : ∀ {Γ A ρ}
      ----------------------
    → ρ · A ∈ (0· Γ , ρ · A)

  S_ : ∀ {Γ} {Δ : Context Γ} {A B ρ}
    → ρ · A ∈ Δ
      --------------------
    → ρ · A ∈ (Δ , 0# · B)
\end{code}

\begin{code}
data _⊢_·_ : {Γ : Precontext} → Context Γ → Mult → Type → Set where

  `_ : ∀ {Γ} {Δ : Context Γ} {ρ A}
     → ρ · A ∈ Δ
       ----------
     → Δ ⊢ ρ · A
\end{code}
