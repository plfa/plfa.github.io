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
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl)
-- open import Relation.Binary.Core using (Rel)
-- open import Data.Product using (∃; ∄; _,_)
-- open import Function using (_∘_; _$_)
\end{code}


## Syntax

Syntax of types and terms. All source terms are labeled with $ᵀ$.

\begin{code}
infixr 100 _⇒_
infixl 100 _·ᵀ_

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
f  =  id "f"
x  =  id "x"
y  =  id "y"

I[𝔹] I[𝔹⇒𝔹] K[𝔹][𝔹] not[𝔹] : Term 
I[𝔹]  =  (λᵀ x ∈ 𝔹 ⇒ (varᵀ x))
I[𝔹⇒𝔹]  =  (λᵀ f ∈ (𝔹 ⇒ 𝔹) ⇒ (λᵀ x ∈ 𝔹 ⇒ ((varᵀ f) ·ᵀ (varᵀ x))))
K[𝔹][𝔹]  =  (λᵀ x ∈ 𝔹 ⇒ (λᵀ y ∈ 𝔹 ⇒ (varᵀ x)))
not[𝔹]  =  (λᵀ x ∈ 𝔹 ⇒ (ifᵀ (varᵀ x) then falseᵀ else trueᵀ))
\end{code}

## Values

\begin{code}
data value : Term → Set where
  value-λᵀ : ∀ {x A N} → value (λᵀ x ∈ A ⇒ N)
  value-trueᵀ : value (trueᵀ)
  value-falseᵀ : value (falseᵀ)
\end{code}

## Substitution

\begin{code}
_[_:=_] : Term → Id → Term → Term
(varᵀ x′) [ x := V ] with x ≟ x′
... | yes _ = V
... | no  _ = varᵀ x′
(λᵀ x′ ∈ A′ ⇒ N′) [ x := V ] with x ≟ x′
... | yes _ = λᵀ x′ ∈ A′ ⇒ N′
... | no  _ = λᵀ x′ ∈ A′ ⇒ (N′ [ x := V ])
(L′ ·ᵀ M′) [ x := V ] =  (L′ [ x := V ]) ·ᵀ (M′ [ x := V ])
(trueᵀ) [ x := V ] = trueᵀ
(falseᵀ) [ x := V ] = falseᵀ
(ifᵀ L′ then M′ else N′) [ x := V ] = ifᵀ (L′ [ x := V ]) then (M′ [ x := V ]) else (N′ [ x := V ])
\end{code}

## Reduction rules

\begin{code}
data _⟹_ : Term → Term → Set where
  β⇒ : ∀ {x A N V} → value V →
    ((λᵀ x ∈ A ⇒ N) ·ᵀ V) ⟹ (N [ x := V ])
  γ⇒₁ : ∀ {L L' M} →
    L ⟹ L' →
    (L ·ᵀ M) ⟹ (L' ·ᵀ M)
  γ⇒₂ : ∀ {V M M'} →
    value V →
    M ⟹ M' →
    (V ·ᵀ M) ⟹ (V ·ᵀ M')
  β𝔹₁ : ∀ {M N} →
    (ifᵀ trueᵀ then M else N) ⟹ M
  β𝔹₂ : ∀ {M N} →
    (ifᵀ falseᵀ then M else N) ⟹ N
  γ𝔹 : ∀ {L L' M N} →
    L ⟹ L' →    
    (ifᵀ L then M else N) ⟹ (ifᵀ L' then M else N)
\end{code}

## Reflexive and transitive closure of a relation

\begin{code}
Rel : Set → Set₁
Rel A = A → A → Set

infixl 100 _>>_

data _* {A : Set} (R : Rel A) : Rel A where
  ⟨⟩ : ∀ {x : A} → (R *) x x
  ⟨_⟩ : ∀ {x y : A} → R x y → (R *) x y
  _>>_ : ∀ {x y z : A} → (R *) x y → (R *) y z → (R *) x z
\end{code}

\begin{code}
infix 80 _⟹*_

_⟹*_ : Term → Term → Set
_⟹*_ = (_⟹_) *
\end{code}

\begin{code}
open import Relation.Binary using (Preorder)

⟹*-Preorder : Preorder _ _ _
⟹*-Preorder = record
  { Carrier    = Term
  ; _≈_        = _≡_
  ; _∼_        = _⟹*_
  ; isPreorder = record
    { isEquivalence = P.isEquivalence
    ; reflexive     = λ {refl → ⟨⟩}
    ; trans         = _>>_
    }
  }

open import Relation.Binary.PreorderReasoning ⟹*-Preorder
     using (begin_; _∎) renaming (_≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _⟹*⟨_⟩_)
\end{code}

Example evaluation.

\begin{code}
example₀′ : not[𝔹] ·ᵀ trueᵀ ⟹* falseᵀ
example₀′ =
  begin
    not[𝔹] ·ᵀ trueᵀ
  ⟹*⟨ ⟨ β⇒ value-trueᵀ ⟩ ⟩
    ifᵀ trueᵀ then falseᵀ else trueᵀ
  ⟹*⟨ ⟨ β𝔹₁ ⟩ ⟩
    falseᵀ
  ∎

example₀ : (not[𝔹] ·ᵀ trueᵀ) ⟹* falseᵀ
example₀ = ⟨ step₀ ⟩ >> ⟨ step₁ ⟩
  where
  M₀ M₁ M₂ : Term
  M₀ = (not[𝔹] ·ᵀ trueᵀ)
  M₁ = (ifᵀ trueᵀ then falseᵀ else trueᵀ)
  M₂ = falseᵀ
  step₀ : M₀ ⟹ M₁
  step₀ = β⇒ value-trueᵀ
  step₁ : M₁ ⟹ M₂
  step₁ = β𝔹₁

example₁ : (I[𝔹⇒𝔹] ·ᵀ I[𝔹] ·ᵀ (not[𝔹] ·ᵀ falseᵀ)) ⟹* trueᵀ
example₁ = ⟨ step₀ ⟩ >> ⟨ step₁ ⟩ >> ⟨ step₂ ⟩ >> ⟨ step₃ ⟩ >> ⟨ step₄ ⟩
  where
  M₀ M₁ M₂ M₃ M₄ M₅ : Term
  M₀ = (I[𝔹⇒𝔹] ·ᵀ I[𝔹] ·ᵀ (not[𝔹] ·ᵀ falseᵀ))
  M₁ = ((λᵀ x ∈ 𝔹 ⇒ (I[𝔹] ·ᵀ varᵀ x)) ·ᵀ (not[𝔹] ·ᵀ falseᵀ))
  M₂ = ((λᵀ x ∈ 𝔹 ⇒ (I[𝔹] ·ᵀ varᵀ x)) ·ᵀ (ifᵀ falseᵀ then falseᵀ else trueᵀ))
  M₃ = ((λᵀ x ∈ 𝔹 ⇒ (I[𝔹] ·ᵀ varᵀ x)) ·ᵀ trueᵀ)
  M₄ = I[𝔹] ·ᵀ trueᵀ
  M₅ = trueᵀ
  step₀ : M₀ ⟹ M₁
  step₀ = γ⇒₁ (β⇒ value-λᵀ)
  step₁ : M₁ ⟹ M₂
  step₁ = γ⇒₂ value-λᵀ (β⇒ value-falseᵀ)
  step₂ : M₂ ⟹ M₃
  step₂ = γ⇒₂ value-λᵀ β𝔹₂
  step₃ : M₃ ⟹ M₄
  step₃ = β⇒ value-trueᵀ         
  step₄ : M₄ ⟹ M₅
  step₄ = β⇒ value-trueᵀ         
\end{code}

## Type rules

\begin{code}
Context : Set
Context = PartialMap Type

infix 50 _⊢_∈_

data _⊢_∈_ : Context → Term → Type → Set where
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
