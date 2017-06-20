---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

This chapter defines the simply-typed lambda calculus.

## Imports
\begin{code}
open import Maps using (Id; id; _≟_; PartialMap; module PartialMap)
open PartialMap using (∅; _,_↦_)
open import Data.String using (String)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
-- open import Relation.Binary.Core using (Rel)
-- open import Data.Product using (∃; ∄; _,_)
-- open import Function using (_∘_; _$_)
\end{code}


## Syntax

Syntax of types and terms. All source terms are labeled with $ᵀ$.

\begin{code}
data Type : Set where
  𝔹 : Type
  _⇒_ : Type → Type → Type

data Term : Set where
  varᵀ : Id → Term
  λᵀ_∈_⇒_ : Id → Type → Term → Term
  _·ᵀ_ : Term → Term → Term
  trueᵀ : Term
  falseᵀ : Term
  ifᵀ_then_else_ : Term → Term → Term → Term
\end{code}

Some examples.
\begin{code}
f x y : Id
f  =  id 0 -- "f"
x  =  id 1 -- "x"
y  =  id 2 -- "y"

I[𝔹] I[𝔹⇒𝔹] K[𝔹][𝔹] not[𝔹] : Term 
I[𝔹]  =  (λᵀ x ∈ 𝔹 ⇒ (varᵀ x))
I[𝔹⇒𝔹]  =  (λᵀ f ∈ (𝔹 ⇒ 𝔹) ⇒ (λᵀ x ∈ 𝔹 ⇒ ((varᵀ f) ·ᵀ (varᵀ x))))
K[𝔹][𝔹]  =  (λᵀ x ∈ 𝔹 ⇒ (λᵀ y ∈ 𝔹 ⇒ (varᵀ x)))
not[𝔹]  =  (λᵀ x ∈ 𝔹 ⇒ (ifᵀ (varᵀ x) then falseᵀ else trueᵀ))
\end{code}

## Values

\begin{code}
data value : Term → Set where
  value-λᵀ : ∀ x A N → value (λᵀ x ∈ A ⇒ N)
  value-trueᵀ : value (trueᵀ)
  value-falseᵀ : value (falseᵀ)
\end{code}

## Substitution

\begin{code}
_[_:=_] : Term → Id → Term → Term
(varᵀ x) [ y := P ] = if ⌊ x ≟ y ⌋ then P else (varᵀ x)
(λᵀ x ∈ A ⇒ N) [ y := P ] =  λᵀ x ∈ A ⇒ (if ⌊ x ≟ y ⌋ then N else (N [ y := P ])) 
(L ·ᵀ M) [ y := P ] =  (L [ y := P ]) ·ᵀ (M [ y := P ])
(trueᵀ) [ y := P ] = trueᵀ
(falseᵀ) [ y := P ] = falseᵀ
(ifᵀ L then M else N) [ y := P ] = ifᵀ (L [ y := P ]) then (M [ y := P ]) else (N [ y := P ])
\end{code}

## Reduction rules

\begin{code}
data _⟹_ : Term → Term → Set where
  β⇒ : ∀ {x A N V} → value V →
    ((λᵀ x ∈ A ⇒ N) ·ᵀ V) ⟹ (N [ x := V ])
  γ·₁ : ∀ {L L' M} →
    L ⟹ L' →
    (L ·ᵀ M) ⟹ (L' ·ᵀ M)
  γ·₂ : ∀ {V M M'} → value V →
    M ⟹ M' →
    (V ·ᵀ M) ⟹ (V ·ᵀ M)
  βif₁ : ∀ {M N} →
    (ifᵀ trueᵀ then M else N) ⟹ M
  βif₂ : ∀ {M N} →
    (ifᵀ falseᵀ then M else N) ⟹ N
  γif : ∀ {L L' M N} →
    L ⟹ L' →    
    (ifᵀ L then M else N) ⟹ (ifᵀ L' then M else N)
\end{code}

## Reflexive and transitive closure of a relation

\begin{code}
Rel : Set → Set₁
Rel A = A → A → Set

data _* {A : Set} (R : Rel A) : Rel A where
  refl* : ∀ {x : A} → (R *) x x
  step* : ∀ {x y : A} → R x y → (R *) x y
  tran* : ∀ {x y z : A} → (R *) x y → (R *) y z → (R *) x z
\end{code}

\begin{code}
_⟹*_ : Term → Term → Set
_⟹*_ = (_⟹_) *
\end{code}

## Type rules

\begin{code}
Env : Set
Env = PartialMap Type

data _⊢_∈_ : Env → Term → Type → Set where
  Ax : ∀ {Γ x A} →
    Γ x ≡ just A →
    Γ ⊢ varᵀ x ∈ A
  ⇒-I : ∀ {Γ x N A B} →
    (Γ , x ↦ A) ⊢ N ∈ B →
    Γ ⊢ (λᵀ x ∈ A ⇒ N) ∈ (A ⇒ B)
  ⇒-E : ∀ {Γ L M A B} →
    Γ ⊢ L ∈ (A ⇒ B) →
    Γ ⊢ M ∈ A →
    Γ ⊢ L ·ᵀ M ∈ B
  𝔹-I₁ : ∀ {Γ} →
    Γ ⊢ trueᵀ ∈ 𝔹
  𝔹-I₂ : ∀ {Γ} →
    Γ ⊢ falseᵀ ∈ 𝔹
  𝔹-E : ∀ {Γ L M N A} →
    Γ ⊢ L ∈ 𝔹 →
    Γ ⊢ M ∈ A →
    Γ ⊢ N ∈ A →
    Γ ⊢ (ifᵀ L then M else N) ∈ A    
\end{code}
