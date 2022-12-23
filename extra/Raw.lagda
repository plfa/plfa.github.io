---
title     : "Raw"
permalink : /Raw/
---

\begin{code}
module plfa.Raw where

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.String using (String)

infix  4  _⊢_⦂_
infix  4  _∋_⦂_
infixl 5  _,_⦂_
\end{code}

## WTF

\begin{code}
Id : Set
Id = String

data Term : Set where
  `_    :  Id → Term
  ƛ_⇒_  :  Id → Term → Term
  _·_   :  Term → Term → Term

data Type : Set where
  _⇒_   : Type → Type → Type
  `ℕ    : Type

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

data _⊢_⦂_ : Context → Term → Type → Set where

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
       -------------
    → Γ ⊢ ` x ⦂ A

  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B
\end{code}
