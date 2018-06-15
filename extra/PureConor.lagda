---
title     : "Pure: Pure Type Systems"
layout    : page
permalink : /Pure/
---

Barendregt, H. (1991). Introduction to generalized type
systems. Journal of Functional Programming, 1(2),
125-154. doi:10.1017/S0956796800020025

Attempt to create inherently typed terms with Connor.


## Imports

\begin{code}
module PureConor where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)
\end{code}

## Syntax

\begin{code}
infix   4  _⊢_
infix   4  _∋_
infix   4  _⊆_
infixl  5  _,_
infix   6  _/_
infix   6  ƛ_⇒_
infix   7  Π_⇒_
-- infixr  8  _⇒_
infixl  9  _·_

data Sort : Set where
  * : Sort
  ▢ : Sort

ok2 : Sort → Sort → Set
ok2 * ▢  =  ⊤
ok2 _ _  =  ⊥

ok3 : Sort → Sort → Sort → Set
ok3 * * ▢  =  ⊤
ok3 * ▢ ▢  =  ⊤
ok3 ▢ * *  =  ⊤
ok3 ▢ ▢ ▢  =  ⊤
ok3 _ _ _  =  ⊥

data Ctx : Set

data Tp : ∀ (Γ : Ctx) → Set
data _∋_ : ∀ (Γ : Ctx) → Tp Γ → Set
data _⊢_ : ∀ (Γ : Ctx) → Tp Γ → Set

data _⟶_ {Γ : Ctx} {A : Tp Γ} : Γ ⊢ A → Γ ⊢ A → Set
data _=β_ {Γ : Ctx} {A : Tp Γ} : Γ ⊢ A → Γ ⊢ A → Set

data Ctx where

  ∅ :
      ---
      Ctx

  _,_ : 
      (Γ : Ctx)
    → (A : Tp Γ)
      -----------
    → Ctx

data Tp where

  ⟪_⟫ : ∀ {Γ : Ctx}
    → Sort
      ----
    → Tp Γ

  ⌈_⌉ : ∀ {Γ : Ctx} {s : Sort}
    → Γ ⊢ ⟪ s ⟫
      ----------
    → Tp Γ

  W : ∀ {Γ : Ctx} {A : Tp Γ}
    → Tp Γ
      -----------
    → Tp (Γ , A)

-- vcons : Π (n : ℕ) → Vec n → Vec (suc n)

_[_] : ∀ {Γ : Ctx}
  → {A : Tp Γ}
  → (B : Tp (Γ , A))
  → (M : Γ ⊢ A)
    ----------------
  → Tp Γ

_⟨_⟩ : ∀ {Γ : Ctx} {A : Tp Γ} {B : Tp (Γ , A)}
  → (N : Γ , A ⊢ B)
  → (M : Γ ⊢ A)
    ---------------
  → Γ ⊢ B [ M ]

data _∋_ where

  Z : ∀ {Γ : Ctx} {A : Tp Γ}
      ----------------------
    → Γ , A ∋ W A

  S : ∀ {Γ : Ctx} {A B : Tp Γ}
    → Γ ∋ B
      -----------
    → Γ , A ∋ W B

data _⊢_ where

  ⟪_⟫ : ∀ {Γ : Ctx} {t : Sort}
    → (s : Sort)
    → {_ : ok2 s t}
      -------------
    → Γ ⊢ ⟪ t ⟫

  ⌊_⌋ : ∀ {Γ : Ctx} {A : Tp Γ}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  Π_⇒_ : ∀ {Γ : Ctx} {s t u : Sort} {stu : ok3 s t u} 
    → (A : Γ ⊢ ⟪ s ⟫)
    → Γ , ⌈ A ⌉ ⊢ ⟪ t ⟫
      ------------------
    → Γ ⊢ ⟪ u ⟫

  ƛ_⇒_ : ∀ {Γ : Ctx} {s t u : Sort} {stu : ok3 s t u}
    → (A : Γ ⊢ ⟪ s ⟫)
    → {B : Γ , ⌈ A ⌉ ⊢ ⟪ t ⟫}
    → Γ , ⌈ A ⌉ ⊢ ⌈ B ⌉
      -------------------------------------
    → Γ ⊢ ⌈ Π_⇒_ {u = u} {stu = stu} A B ⌉

  _·_ : ∀ {Γ : Ctx} {s t u : Sort} {stu : ok3 s t u}
    → {A : Γ ⊢ ⟪ s ⟫}
    → {B : Γ , ⌈ A ⌉ ⊢ ⟪ t ⟫}
    → (L : Γ ⊢ ⌈ Π_⇒_ {u = u} {stu = stu} A B ⌉)
    → (M : Γ ⊢ ⌈ A ⌉)
      ------------------------------------------
    → Γ ⊢ ⌈ B ⌉ [ M ]

data _⊆_ : Ctx → Ctx → Set

_/_ : ∀ {Γ Δ : Ctx} → Γ ⊆ Δ → Tp Γ → Tp Δ

_/∋_ : ∀ {Γ Δ : Ctx} {A : Tp Γ} → (θ : Γ ⊆ Δ) → Γ ∋ A → Δ ∋ θ / A

_/⊢_ : ∀ {Γ Δ : Ctx} {A : Tp Γ} → (θ : Γ ⊆ Δ) → Γ ⊢ A → Δ ⊢ θ / A

data _⊆_ where

  ∅ :
      -----
      ∅ ⊆ ∅

  W : ∀ {Γ Δ : Ctx} {A : Tp Δ}
    → Γ ⊆ Δ
      ---------
    → Γ ⊆ Δ , A

  S : ∀ {Γ Δ : Ctx} {A : Tp Γ}
    → (θ : Γ ⊆ Δ)
      -----------------
    → Γ , A ⊆ Δ , θ / A

∅ / A = A
W θ / A = {!!}
S θ / A = {!!}

∅ /∋ x = x
W θ /∋ x = {!S x!}
S θ /∋ x = {!!}

θ /⊢ A = {!!} 

_[_]  =  {!!}

_⟨_⟩  =  {!!}

data _⟶_ where

data _=β_ where



\end{code}

