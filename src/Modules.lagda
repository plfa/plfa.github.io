---
title     : "Modules: Modules and List Examples"
layout    : page
permalink : /Modules
---

** Turn this into a Setoid example. Copy equivalence relation and setoid
from the standard library. **

This chapter introduces modules as a way of structuring proofs,
and proves some general results which will be useful later.

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
-- open import Data.Nat.Properties using
--   (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Isomorphism using (_≃_)
open import Function using (_∘_)
open import Level using (Level)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; map; foldr; downFrom)
open import Data.List.All using (All; []; _∷_)
open import Data.List.Any using (Any; here; there)
-- open import Data.List.Any.Membership.Propositional using (_∈_)
\end{code}

We assume [extensionality][extensionality].
\begin{code}
postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
\end{code}

[extensionality]: Equality#extensionality


## Modules

Let's say we want to prove some standard results about collections of
elements of a given type at a given universe level with a given
equivalence relation for equality. One way to do so is to begin every
signature with a suitable sequence of implicit parameters.  Here are
some definitions, where we represent collections as lists.  (We would
call collections *sets*, save that the name `Set` already plays a
special role in Agda.)

\begin{code}
Coll′ : ∀ {ℓ : Level} → Set ℓ → Set ℓ
Coll′ A  =  List A

_∈′_ : ∀ {ℓ : Level} {A : Set ℓ} {_≈_ : A → A → Set ℓ} → A → Coll′ A → Set ℓ
_∈′_ {_≈_ = _≈_} x xs  =  All (x ≈_) xs

_⊆′_ : ∀ {ℓ : Level} {A : Set ℓ} {_≈_ : A → A → Set ℓ} → Coll′ A → Coll′ A → Set ℓ
_⊆′_ {_≈_ = _≈_} xs ys  =  ∀ {w} → _∈′_  {_≈_ = _≈_} w xs → _∈′_ {_≈_ = _≈_} w ys
\end{code}

This rapidly gets tired.  Passing around the equivalence relation `_≈_`
takes a lot of space, hinders the use of infix notation, and obscures the
essence of the definitions.

Instead, we can define a module parameterised by the desired concepts,
which are then available throughout.
\begin{code}
module Collection {ℓ : Level} (A : Set ℓ) (_≈_ : A → A → Set ℓ) where

  Coll : ∀ {ℓ : Level} → Set ℓ → Set ℓ
  Coll A  =  List A

  _∈_ : A → Coll A → Set ℓ
  x ∈ xs  =  Any (x ≈_) xs

  _⊆_ : Coll A → Coll A → Set ℓ
  xs ⊆ ys  =  ∀ {w} → w ∈ xs → w ∈ ys
\end{code}

Use of a module
\begin{code}
open Collection (ℕ) (_≡_)

pattern [_] x  =  x ∷ []
pattern [_,_] x y  =  x ∷ y ∷ []
pattern [_,_,_] x y z  =  x ∷ y ∷ z ∷ []

ex : [ 1 , 3 ] ⊆ [ 1 , 2 , 3 ]
ex (here refl)          =  here refl
ex (there (here refl))  =  there (there (here refl))
ex (there (there ()))
\end{code}


## Abstract types

Say I want to define a type of stacks, with operations push and pop.
I can define stacks in terms of lists, but hide the definitions from
the rest of the program.
\begin{code}
abstract 

  Stack : Set → Set
  Stack A = List A

  empty : ∀ {A} → Stack A
  empty = []

  push : ∀ {A} → A → Stack A → Stack A
  push x xs  =  x ∷ xs

  pop : ∀ {A} → Stack A → Maybe (A × Stack A)
  pop []        =  nothing
  pop (x ∷ xs)  =  just ⟨ x , xs ⟩

  lemma-pop-push : ∀ {A} {x : A} {xs} → pop (push x xs) ≡ just ⟨ x , xs ⟩
  lemma-pop-push = refl

  lemma-pop-empty : ∀ {A} → pop {A} empty ≡ nothing
  lemma-pop-empty = refl
\end{code}


## Standard Library

Definitions similar to those in this chapter can be found in the standard library.
\begin{code}
-- EDIT
\end{code}
The standard library version of `IsMonoid` differs from the
one given here, in that it is also parameterised on an equivalence relation.


## Unicode

This chapter uses the following unicode.

    EDIT
    ∷  U+2237  PROPORTION  (\::)
    ⊗  U+2297  CIRCLED TIMES  (\otimes)
    ∈  U+2208  ELEMENT OF  (\in)
    ∉  U+2209  NOT AN ELEMENT OF  (\inn)
