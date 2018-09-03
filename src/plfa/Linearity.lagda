---
title     : "Linearity: Introduction to the Linear Lambda Calculus"
layout    : page
permalink : /Linearity/
---

\begin{code}
open import Algebra using (Semiring)
open import Function using (_∘_)
\end{code}

\begin{code}
module plfa.Linearity where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
\end{code}

\begin{code}
infix  1 _⊢_
infix  1 _∋_
infixl 5 _,_
infixl 5 _,_∙_
infix  6 _++ᵖ_ _++ᶜ_ _⋈_
infix  7 0∙_
infixr 9 [_∙_]⊸_

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
suc : Mult → Mult
suc 0# = 1#
suc 1# = ω#
suc ω# = ω#

_+_ : Mult → Mult → Mult
0# + π = π
1# + π = suc π
ω# + _ = ω#

_*_ : Mult → Mult → Mult
0# * _  = 0#
1# * π  = π
ω# * 0# = 0#
ω# * _  = ω#
\end{code}

\begin{code}
data Type : Set where
  [_∙_]⊸_ : Mult → Type → Type → Type
  `1      : Type
  `0      : Type
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
_++ᵖ_ : Precontext → Precontext → Precontext
Γ ++ᵖ ∅        = Γ
Γ ++ᵖ (Γ′ , A) = (Γ ++ᵖ Γ′) , A
\end{code}

\begin{code}
data Context : Precontext → Set where
  ∅     : Context ∅
  _,_∙_ : ∀ {Γ} → Context Γ → Mult → (A : Type) → Context (Γ , A)
\end{code}

\begin{code}
_ : Context (∅ , [ 1# ∙ `1 ]⊸ `1 , `1)
_ = ∅ , 0# ∙ [ 1# ∙ `1 ]⊸ `1 , 1# ∙ `1
\end{code}

\begin{code}
_++ᶜ_ : ∀ {Γ Γ′} → Context Γ → Context Γ′ → Context (Γ ++ᵖ Γ′)
Δ ++ᶜ ∅            = Δ
Δ ++ᶜ (Δ′ , π ∙ A) = (Δ ++ᶜ Δ′) , π ∙ A
\end{code}

\begin{code}
_⋈_ : ∀ {Γ} → Context Γ → Context Γ → Context Γ
∅ ⋈ ∅ = ∅
(Δ , π ∙ A) ⋈ (Δ′ , π′ ∙ .A) = Δ ⋈ Δ′ , π + π′ ∙ A
\end{code}

\begin{code}
0∙_ : (Γ : Precontext) → Context Γ
0∙  ∅      = ∅
0∙ (Γ , A) = 0∙ Γ , 0# ∙ A
\end{code}

\begin{code}
data _∋_ : {Γ : Precontext} → Context Γ → Type → Set where

  Z : ∀ {Γ A}
      ----------------------
    → 0∙ Γ , 1# ∙ A ∋ A

  S_ : ∀ {Γ} {Δ : Context Γ} {A B}
     → Δ ∋ A
       --------------------
     → (Δ , 0# ∙ B) ∋ A
\end{code}

\begin{code}
data _⊢_ : {Γ : Precontext} → Context Γ → Type → Set where

  `_  : ∀ {Γ} {Δ : Context Γ} {A}
      → Δ ∋ A
        -----
      → Δ ⊢ A

  ƛ_  : ∀ {Γ} {Δ : Context Γ} {A B π}
      → Δ , π ∙ A ⊢ B
        ----------------
      → Δ ⊢ [ π ∙ A ]⊸ B

  _·_ : ∀ {Γ} {Δ₁ Δ₂ : Context Γ} {A B π}
      → Δ₁ ⊢ [ π ∙ A ]⊸ B
      → Δ₂ ⊢ A
        -----------
      → Δ₁ ⋈ Δ₂ ⊢ B

  `tt : ∀ {Γ} {Δ : Context Γ}
        ------
      → Δ ⊢ `1
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

_ : ∅ , ω# ∙ [ ω# ∙ `1 ]⊸ `1 ⊢ [ ω# ∙ `1 ]⊸ `1
_ = ƛ {!!}
-- ƛ (` S Z · (` S Z · ` Z))

_ : ∅ ⊢ [ ω# ∙ [ ω# ∙ `1 ]⊸ `1 ]⊸ [ ω# ∙ `1 ]⊸ `1
_ = {!!}
-- ƛ ƛ ` S Z · (` S Z · ` Z)
\end{code}
