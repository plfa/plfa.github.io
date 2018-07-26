---
title     : "Linearity: Introduction to the Linear Lambda Calculus"
layout    : page
permalink : /Linearity/
---

\begin{code}
open import Algebra using (Semiring; module Semiring)
\end{code}

\begin{code}
module plfa.Linearity {c} {ℓ} (semiring : Semiring c ℓ) where
\end{code}

\begin{code}
open Semiring semiring using (_+_; 0#; _*_; 1#) renaming (Carrier to Multiplicity)
\end{code}

\begin{code}
infixl 5 _,_
infixl 5 _,_·_
\end{code}

\begin{code}
data Type : Set c where
  [_·_]⊸_ : Multiplicity → Type → Type → Type
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
  _,_·_ : ∀ {Γ} → Context Γ → Multiplicity → (A : Type) → Context (Γ , A)
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
