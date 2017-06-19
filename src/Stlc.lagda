---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

This chapter defines the simply-typed lambda calculus.

## Imports

\begin{code}
-- open import Data.Sum renaming (_⊎_ to _+_)
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.List
open import Data.String
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
\end{code}

## Identifiers

[Replace this by $Id$ from $Map$]

\begin{code}
data Id : Set where
  id : String → Id

_===_ : Id → Id → Bool
(id s) === (id t)  =  s == t
\end{code}

## Syntax

Syntax of types and terms. All source terms are labeled with $ᵀ$.

\begin{code}
data Type : Set where
  𝔹 : Type
  _⟶_ : Type → Type → Type

data Term : Set where
  varᵀ : Id → Term
  λᵀ_∷_⟶_ : Id → Type → Term → Term
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

I[𝔹] I[𝔹⟶𝔹] K[𝔹][𝔹] not[𝔹] : Term 
I[𝔹]  =  (λᵀ x ∷ 𝔹 ⟶ (varᵀ x))
I[𝔹⟶𝔹]  =  (λᵀ f ∷ (𝔹 ⟶ 𝔹) ⟶ (λᵀ x ∷ 𝔹 ⟶ ((varᵀ f) ·ᵀ (varᵀ x))))
K[𝔹][𝔹]  =  (λᵀ x ∷ 𝔹 ⟶ (λᵀ y ∷ 𝔹 ⟶ (varᵀ x)))
not[𝔹]  =  (λᵀ x ∷ 𝔹 ⟶ (ifᵀ (varᵀ x) then falseᵀ else trueᵀ))
\end{code}

## Values

\begin{code}
data value : Term → Set where
  value-λᵀ : ∀ x A N → value (λᵀ x ∷ A ⟶ N)
  value-trueᵀ : value (trueᵀ)
  value-falseᵀ : value (falseᵀ)
\end{code}

## Substitution

\begin{code}
_[_:=_] : Term → Id → Term → Term
(varᵀ x) [ y := P ] = if x === y then P else (varᵀ x)
(λᵀ x ∷ A ⟶ N) [ y := P ] =  λᵀ x ∷ A ⟶ (if x === y then N else (N [ y := P ])) 
(L ·ᵀ M) [ y := P ] =  (L [ y := P ]) ·ᵀ (M [ y := P ])
(trueᵀ) [ y := P ] = trueᵀ
(falseᵀ) [ y := P ] = falseᵀ
(ifᵀ L then M else N) [ y := P ] = ifᵀ (L [ y := P ]) then (M [ y := P ]) else (N [ y := P ])
\end{code}

