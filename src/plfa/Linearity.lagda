---
title     : "Linearity: Introduction to the Linear Lambda Calculus"
layout    : page
permalink : /Linearity/
---

\begin{code}
module plfa.Linearity where
\end{code}

\begin{code}
open import Data.Maybe as Maybe using (Maybe; just; nothing; Is-just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc; zero; _≤?_; _<_; s≤s)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable as D using (True; toWitness)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Relation.Binary.Core using (Reflexive; Transitive; Total)
\end{code}

\begin{code}
infix  1 _⊢₁_
infix  1 _∋₁_
infixl 5 _,_
infixl 5 _,_∙_

infixr 6 [_∙_]⊸_
infixr 7 _⊗_
infixr 7 _&_
infixr 7 _⊕_

infixl 9 _**_
infixr 8 _⋈_

infix  5 ƛ_
infixl 7 _·_
infix  9 `_
\end{code}

\begin{code}
data Mult : Set where
  0# : Mult
  1# : Mult
  ω# : Mult
\end{code}

\begin{code}
_+_ : Mult → Mult → Mult
0# + π  = π
1# + 0# = 1#
1# + 1# = ω#
1# + ω# = ω#
ω# + _  = ω#
\end{code}

\begin{code}
_*_ : Mult → Mult → Mult
0# * _  = 0#
1# * 0# = 0#
ω# * 0# = 0#
1# * 1# = 1#
ω# * 1# = ω#
1# * ω# = ω#
ω# * ω# = ω#
\end{code}

\begin{code}
data Type : Set where
  [_∙_]⊸_ : Mult → Type → Type → Type
  `1      : Type
  `0      : Type
  `⊤      : Type
  _⊗_     : Type → Type → Type
  _&_     : Type → Type → Type
  _⊕_     : Type → Type → Type
\end{code}

\begin{code}
data Precontext : Set where
  ∅   : Precontext
  _,_ : Precontext → Type → Precontext
\end{code}

\begin{code}
_ : Precontext
_ = ∅ , [ 1# ∙ `1 ]⊸ `1 , `1
\end{code}

\begin{code}
data Context : Precontext → Set where
  ∅     : Context ∅
  _,_∙_ : ∀ {Γ} → Context Γ → Mult → (A : Type) → Context (Γ , A)
\end{code}

\begin{code}
_ : Context (∅ , [ 1# ∙ `1 ]⊸ `1 , `1)
_ = ∅ , 1# ∙ [ 1# ∙ `1 ]⊸ `1 , 0# ∙ `1
\end{code}

\begin{code}
_⋈_ : ∀ {γ} → Context γ → Context γ → Context γ
∅ ⋈ ∅ = ∅
(Γ₁ , π₁ ∙ A) ⋈ (Γ₂ , π₂ ∙ .A) = Γ₁ ⋈ Γ₂ , π₁ + π₂ ∙ A
\end{code}

\begin{code}
data _⋈_↦_ : ∀ {γ} (Γ Γ′ Δ : Context γ) → Set where

  ∅       : ---------
            ∅ ⋈ ∅ ↦ ∅

  _,0+0∙_ : ∀ {γ} {Γ Γ′ Δ : Context γ}
          → Γ ⋈ Γ′ ↦ Δ
          → (A : Type)
          → (Γ , 0# ∙ A) ⋈ (Γ′ , 0# ∙ A) ↦ (Δ , 0# ∙ A)

  _,0+1∙_ : ∀ {γ} {Γ Γ′ Δ : Context γ}
          → Γ ⋈ Γ′ ↦ Δ
          → (A : Type)
          → (Γ , 0# ∙ A) ⋈ (Γ′ , 1# ∙ A) ↦ (Δ , 1# ∙ A)

  _,1+0∙_ : ∀ {γ} {Γ Γ′ Δ : Context γ}
          → Γ ⋈ Γ′ ↦ Δ
          → (A : Type)
          → (Γ , 1# ∙ A) ⋈ (Γ′ , 0# ∙ A) ↦ (Δ , 1# ∙ A)
\end{code}

\begin{code}
0∙_ : ∀ γ → Context γ
0∙  ∅      = ∅
0∙ (γ , A) = 0∙ γ , 0# ∙ A
\end{code}

\begin{code}
_**_ : ∀ {γ} → Mult → Context γ → Context γ
π ** ∅ = ∅
π ** (Γ , ρ ∙ A) = π ** Γ , π * ρ ∙ A
\end{code}

\begin{code}
data _∋₁_ : ∀ {γ} → Context γ → Type → Set where

  Z  : ∀ {γ} {A}
       -----------------
     → 0∙ γ , 1# ∙ A ∋₁ A

  S_ : ∀ {γ} {Γ : Context γ} {A B}

     → Γ ∋₁ A
       --------------
     → Γ , 0# ∙ B ∋₁ A
\end{code}


\begin{code}
data _⊢₁_ : ∀ {γ} → Context γ → Type → Set where

  `_  : ∀ {γ} {Γ : Context γ} {A}

      → Γ ∋₁ A
        -----
      → Γ ⊢₁ A

  ƛ_  : ∀ {γ} {Γ : Context γ} {A B} {π}

      → Γ , π ∙ A ⊢₁ B
        -----------------
      → Γ ⊢₁ [ π ∙ A ]⊸ B

  _·_ : ∀ {γ} {Γ Δ : Context γ} {A B} {π}

      → Γ ⊢₁ [ π ∙ A ]⊸ B
      → Δ ⊢₁ A
        ----------
      → Γ ⋈ π ** Δ ⊢₁ B
\end{code}

\begin{code}
_ : ∅ , 0# ∙ [ 1# ∙ `1 ]⊸ `1 , 1# ∙ `1 ⊢₁ `1
_ = ` Z

_ : ∅ , 1# ∙ [ 1# ∙ `1 ]⊸ `1 , 0# ∙ `1 ⊢₁ [ 1# ∙ `1 ]⊸ `1
_ = ` S Z

_ : ∅ , 1# ∙ [ 1# ∙ `1 ]⊸ `1 , 1# ∙ `1 ⊢₁ `1
_ = ` S Z · ` Z

_ : ∅ , ω# ∙ [ 1# ∙ `1 ]⊸ `1 , 1# ∙ `1 ⊢₁ `1
_ = ` S Z · (` S Z · ` Z)

_ : ∅ , ω# ∙ [ 1# ∙ `1 ]⊸ `1 ⊢₁ [ 1# ∙ `1 ]⊸ `1
_ = ƛ ` S Z · (` S Z · ` Z)

_ : ∅ ⊢₁ [ ω# ∙ [ 1# ∙ `1 ]⊸ `1 ]⊸ [ 1# ∙ `1 ]⊸ `1
_ = ƛ ƛ ` S Z · (` S Z · ` Z)
\end{code}
