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
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl)
open import Relation.Binary using (Preorder)
import Relation.Binary.PreorderReasoning as PreorderReasoning
-- open import Relation.Binary.Core using (Rel)
-- open import Data.Product using (∃; ∄; _,_)
-- open import Function using (_∘_; _$_)
\end{code}


## Syntax

Syntax of types and terms.

\begin{code}
infixr 20 _⇒_

data Type : Set where
  𝔹 : Type
  _⇒_ : Type → Type → Type

infixl 20 _·_
infix  15 λ[_∶_]_
infix  15 if_then_else_

data Term : Set where
  var : Id → Term
  λ[_∶_]_ : Id → Type → Term → Term
  _·_ : Term → Term → Term
  true : Term
  false : Term
  if_then_else_ : Term → Term → Term → Term
\end{code}

Some examples.
\begin{code}
f x y : Id
f  =  id "f"
x  =  id "x"
y  =  id "y"

I I² K not : Term 
I   =  λ[ x ∶ 𝔹 ] var x
I²  =  λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] var f · var x
K   =  λ[ x ∶ 𝔹 ] λ[ y ∶ 𝔹 ] var x
not =  λ[ x ∶ 𝔹 ] (if var x then false else true)

check : not ≡ λ[ x ∶ 𝔹 ] (if var x then false else true)
check = refl
\end{code}

## Values

\begin{code}
data Value : Term → Set where
  value-λ     : ∀ {x A N} → Value (λ[ x ∶ A ] N)
  value-true  : Value true
  value-false : Value false
\end{code}

## Substitution

\begin{code}
_[_∶=_] : Term → Id → Term → Term
(var x′) [ x ∶= V ] with x ≟ x′
... | yes _ = V
... | no  _ = var x′
(λ[ x′ ∶ A′ ] N′) [ x ∶= V ] with x ≟ x′
... | yes _ = λ[ x′ ∶ A′ ] N′
... | no  _ = λ[ x′ ∶ A′ ] (N′ [ x ∶= V ])
(L′ · M′) [ x ∶= V ] =  (L′ [ x ∶= V ]) · (M′ [ x ∶= V ])
(true) [ x ∶= V ] = true
(false) [ x ∶= V ] = false
(if L′ then M′ else N′) [ x ∶= V ] = if (L′ [ x ∶= V ]) then (M′ [ x ∶= V ]) else (N′ [ x ∶= V ])
\end{code}

## Reduction rules

\begin{code}
infix 10 _⟹_ 

data _⟹_ : Term → Term → Set where
  β⇒ : ∀ {x A N V} → Value V →
    (λ[ x ∶ A ] N) · V ⟹ N [ x ∶= V ]
  γ⇒₁ : ∀ {L L' M} →
    L ⟹ L' →
    L · M ⟹ L' · M
  γ⇒₂ : ∀ {V M M'} →
    Value V →
    M ⟹ M' →
    V · M ⟹ V · M'
  β𝔹₁ : ∀ {M N} →
    if true then M else N ⟹ M
  β𝔹₂ : ∀ {M N} →
    if false then M else N ⟹ N
  γ𝔹 : ∀ {L L' M N} →
    L ⟹ L' →    
    if L then M else N ⟹ if L' then M else N
\end{code}

## Reflexive and transitive closure of a relation

\begin{code}
Rel : Set → Set₁
Rel A = A → A → Set

infixl 10 _>>_

data _* {A : Set} (R : Rel A) : Rel A where
  ⟨⟩ : ∀ {x : A} → (R *) x x
  ⟨_⟩ : ∀ {x y : A} → R x y → (R *) x y
  _>>_ : ∀ {x y z : A} → (R *) x y → (R *) y z → (R *) x z
\end{code}

\begin{code}
infix 10 _⟹*_

_⟹*_ : Rel Term
_⟹*_ = (_⟹_) *
\end{code}

\begin{code}
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

open PreorderReasoning ⟹*-Preorder
     using (_IsRelatedTo_; begin_; _∎) renaming (_≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _⟹*⟨_⟩_)

infixr 2 _⟹*⟪_⟫_

_⟹*⟪_⟫_ : ∀ x {y z} → x ⟹ y → y IsRelatedTo z → x IsRelatedTo z
x ⟹*⟪ x⟹y ⟫ yz  =  x ⟹*⟨ ⟨ x⟹y ⟩ ⟩ yz
\end{code}

Example evaluation.

\begin{code}
example₀ : not · true ⟹* false
example₀ =
  begin
    not · true
  ⟹*⟪ β⇒ value-true ⟫
    if true then false else true
  ⟹*⟪ β𝔹₁ ⟫
    false
  ∎

example₁ : I² · I · (not · false) ⟹* true
example₁ =
  begin
    I² · I · (not · false)
  ⟹*⟪ γ⇒₁ (β⇒ value-λ) ⟫
    (λ[ x ∶ 𝔹 ] I · var x) · (not · false)                  
  ⟹*⟪ γ⇒₂ value-λ (β⇒ value-false) ⟫
    (λ[ x ∶ 𝔹 ] I · var x) · (if false then false else true)
  ⟹*⟪ γ⇒₂ value-λ β𝔹₂ ⟫
    (λ[ x ∶ 𝔹 ] I · var x) · true
  ⟹*⟪ β⇒ value-true ⟫
    I · true
  ⟹*⟪ β⇒ value-true ⟫
    true
  ∎  
\end{code}

## Type rules

\begin{code}
Context : Set
Context = PartialMap Type

infix 10 _⊢_∶_

data _⊢_∶_ : Context → Term → Type → Set where
  Ax : ∀ {Γ x A} →
    Γ x ≡ just A →
    Γ ⊢ var x ∶ A
  ⇒-I : ∀ {Γ x N A B} →
    Γ , x ↦ A ⊢ N ∶ B →
    Γ ⊢ λ[ x ∶ A ] N ∶ A ⇒ B
  ⇒-E : ∀ {Γ L M A B} →
    Γ ⊢ L ∶ A ⇒ B →
    Γ ⊢ M ∶ A →
    Γ ⊢ L · M ∶ B
  𝔹-I₁ : ∀ {Γ} →
    Γ ⊢ true ∶ 𝔹
  𝔹-I₂ : ∀ {Γ} →
    Γ ⊢ false ∶ 𝔹
  𝔹-E : ∀ {Γ L M N A} →
    Γ ⊢ L ∶ 𝔹 →
    Γ ⊢ M ∶ A →
    Γ ⊢ N ∶ A →
    Γ ⊢ if L then M else N ∶ A    
\end{code}
