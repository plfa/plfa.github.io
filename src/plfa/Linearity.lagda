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
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Relation.Binary.Core using (Reflexive; Transitive; Total)
\end{code}

\begin{code}
infix  1 _⊢_
infix  1 _∋_
infixl 5 _,_
infixl 5 _,_∙_

infixr 8 [_∙_]⊸_
infixr 9 _⊗_
infixr 9 _&_
infixr 9 _⊕_


infix  5 ƛ_
infixl 7 _·_
infix  9 `_
\end{code}

\begin{code}
data Usage : Set where
  0# : Usage
  1# : Usage
  ω# : Usage
\end{code}

\begin{code}
_+_ : Usage → Usage → Usage
0# + π  = π
1# + 0# = 1#
1# + 1# = ω#
1# + ω# = ω#
ω# + _  = ω#
\end{code}

\begin{code}
_*_ : Usage → Usage → Usage
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
  [_∙_]⊸_ : Usage → Type → Type → Type
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
  _,_∙_ : ∀ {Γ} → Context Γ → Usage → (A : Type) → Context (Γ , A)
\end{code}

\begin{code}
_ : Context (∅ , [ 1# ∙ `1 ]⊸ `1 , `1)
_ = ∅ , 0# ∙ [ 1# ∙ `1 ]⊸ `1 , 1# ∙ `1
\end{code}

\begin{code}
_⋈_ : ∀ {γ} → Context γ → Context γ → Context γ
∅ ⋈ ∅ = ∅
(Γ₁ , π₁ ∙ A) ⋈ (Γ₂ , π₂ ∙ .A) = Γ₁ ⋈ Γ₂ , π₁ + π₂ ∙ A
\end{code}

\begin{code}
0∙_ : (Γ : Precontext) → Context Γ
0∙  ∅      = ∅
0∙ (Γ , A) = 0∙ Γ , 0# ∙ A
\end{code}

\begin{code}
data _∋_ : {γ : Precontext} → Context γ → Type → Set where

  Z  : ∀ {γ A}

       -----------------
     → 0∙ γ , 1# ∙ A ∋ A

  S_ : ∀ {γ} {Γ : Context γ} {A B}

     → Γ ∋ A
       --------------
     → Γ , 0# ∙ B ∋ A
\end{code}

\begin{code}
data _⊢_ : {γ : Precontext} → Context γ → Type → Set where

  `_  : ∀ {γ} {Γ : Context γ} {A}

      → Γ ∋ A
        -----
      → Γ ⊢ A

  ƛ_  : ∀ {γ} {Γ : Context γ} {A B π}

      → Γ , π ∙ A ⊢ B
        ----------------
      → Γ ⊢ [ π ∙ A ]⊸ B

  _·_ : ∀ {γ} {Γ Δ : Context γ} {A B π}

      → Γ ⊢ [ π ∙ A ]⊸ B
      → Δ ⊢ A
        -----------
      → Γ ⋈ Δ ⊢ B

  `tt : ∀ {γ} {Γ : Context γ}

        ------
      → Γ ⊢ `1

  `case1 : ∀ {γ} {Γ Δ : Context γ} {A}

      → Γ ⊢ `1
      → Δ ⊢ A
        -----------
      → Γ ⋈ Δ ⊢ A

  `⟨_,_⟩ : ∀ {γ} {Γ Δ : Context γ} {A B}

      → Γ ⊢ A
      → Δ ⊢ B
        ---------------
      → Γ ⋈ Δ ⊢ A ⊗ B

  `case⊗ : ∀ {γ} {Γ Δ : Context γ} {A B C}

      → Γ ⊢ A ⊗ B
      → Δ , 1# ∙ A , 1# ∙ B ⊢ C
        ------------------------
      → Γ ⋈ Δ ⊢ C

  `⟪_,_⟫ : ∀ {γ} {Γ : Context γ} {A B}

      → Γ ⊢ B
      → Γ ⊢ A
        ---------
      → Γ ⊢ A & B

  `proj₁ : ∀ {γ} {Γ : Context γ} {A B}

      → Γ ⊢ A & B
        ---------
      → Γ ⊢ A

  `proj₂ : ∀ {γ} {Γ : Context γ} {A B}

      → Γ ⊢ A & B
        ---------
      → Γ ⊢ B

  `inj₁ : ∀ {γ} {Γ : Context γ} {A B}

      → Γ ⊢ A
        ---------
      → Γ ⊢ A ⊕ B

  `inj₂ : ∀ {γ} {Γ : Context γ} {A B}

      → Γ ⊢ B
        ---------
      → Γ ⊢ A ⊕ B

  `case⊕ : ∀ {γ} {Γ Δ : Context γ} {A B C}

      → Γ ⊢ A ⊕ B
      → Δ , 1# ∙ A ⊢ C
      → Δ , 1# ∙ B ⊢ C
\end{code}

\begin{code}
_ : ∅ , 0# ∙ [ 1# ∙ `1 ]⊸ `1 , 1# ∙ `1 ⊢ `1
_ = ` Z

_ : ∅ , 1# ∙ [ 1# ∙ `1 ]⊸ `1 , 0# ∙ `1 ⊢ [ 1# ∙ `1 ]⊸ `1
_ = ` S Z

_ : ∅ , 1# ∙ [ 1# ∙ `1 ]⊸ `1 , 1# ∙ `1 ⊢ `1
_ = ` S Z · ` Z

_ : ∅ , ω# ∙ [ 1# ∙ `1 ]⊸ `1 , 1# ∙ `1 ⊢ `1
_ = ` S Z · (` S Z · ` Z)

_ : ∅ , ω# ∙ [ ω# ∙ `1 ]⊸ `1 ⊢ [ 1# ∙ `1 ]⊸ `1
_ = ƛ ` S Z · (` S Z · ` Z)

_ : ∅ ⊢ [ ω# ∙ [ 1# ∙ `1 ]⊸ `1 ]⊸ [ 1# ∙ `1 ]⊸ `1
_ = ƛ ƛ ` S Z · (` S Z · ` Z)
\end{code}

