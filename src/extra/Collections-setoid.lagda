---
title     : "Collections: Collections represented as Lists"
layout    : page
permalink : /Collections
---

This chapter presents operations on collections and a number of
useful operations on them.


## Imports

\begin{code}
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; sym; trans; cong)
-- open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
-- open import Data.Nat.Properties using
--   (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Isomorphism using (_≃_)
open import Function using (_∘_)
open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_; map; foldr; filter)
open import Data.List.All using (All; []; _∷_)
open import Data.List.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing)
-- open import Data.List.Any.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contraposition; ¬?)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary using (IsEquivalence)
\end{code}


## Collections

\begin{code}
infix 0 _↔_

_↔_ : Set → Set → Set
A ↔ B  =  (A → B) × (B → A)

module Collection
         (A : Set)
         (_≈_ : A → A → Set)
         (isEquivalence : IsEquivalence _≈_)
         where

  open IsEquivalence isEquivalence 

  abstract

    Coll : Set → Set
    Coll A  =  List A
\end{code}

Collections support the same abbreviations as lists for writing
collections with a small number of elements.
\begin{code}
    [_] : A → Coll A
    [ x ]  =  x ∷ []
\end{code}

\begin{code}
    infix 4 _∈_
    infix 4 _⊆_
    infix 5 _∪_

    _∈_ : A → Coll A → Set
    w ∈ xs  =  Any (w ≈_) xs

    _⊆_ : Coll A → Coll A → Set
    xs ⊆ ys  =  ∀ {w} → w ∈ xs → w ∈ ys

    _∪_ : Coll A → Coll A → Coll A
    _∪_ = _++_

    preserves : ∀ {u v xs} → u ≈ v → u ∈ xs → v ∈ xs
    preserves u≈v (here u≈)   =  here (trans (sym u≈v) u≈)
    preserves u≈v (there u∈)  =  there (preserves u≈v u∈)

    ⊆-refl : ∀ {xs} → xs ⊆ xs
    ⊆-refl ∈xs  =  ∈xs

    ⊆-trans : ∀ {xs ys zs} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
    ⊆-trans xs⊆ ys⊆  =  ys⊆ ∘ xs⊆

    lemma₁ : ∀ {w xs} → w ∈ xs ↔ [ w ] ⊆ xs
    lemma₁ = ⟨ forward , backward ⟩
      where

      forward : ∀ {w xs} → w ∈ xs → [ w ] ⊆ xs
      forward ∈xs (here w≈)    =   preserves (sym w≈) ∈xs  -- ∈xs
      forward ∈xs (there ())

      backward : ∀ {w xs} → [ w ] ⊆ xs → w ∈ xs
      backward ⊆xs  =  ⊆xs (here refl)

    lemma₂ : ∀ {xs ys} → xs ⊆ xs ∪ ys
    lemma₂ (here w≈)    =  here w≈
    lemma₂ (there ∈xs)  =  there (lemma₂ ∈xs)

    lemma₃ : ∀ {xs ys} → ys ⊆ xs ∪ ys
    lemma₃ {[]}     ∈ys  =  ∈ys
    lemma₃ {x ∷ xs} ∈ys  =  there (lemma₃ {xs} ∈ys)

    lemma₄ : ∀ {w xs ys} → w ∈ xs ⊎ w ∈ ys ↔ w ∈ xs ∪ ys
    lemma₄ = ⟨ forward , backward ⟩
      where

      forward : ∀ {w xs ys} → w ∈ xs ⊎ w ∈ ys → w ∈ xs ∪ ys
      forward (inj₁ ∈xs)  =  lemma₂ ∈xs
      forward (inj₂ ∈ys)  =  lemma₃ ∈ys

      backward : ∀ {xs ys w} → w ∈ xs ∪ ys → w ∈ xs ⊎ w ∈ ys
      backward {[]}     ∈ys                               =  inj₂ ∈ys
      backward {x ∷ xs} (here w≈)                         =  inj₁ (here w≈)
      backward {x ∷ xs} (there w∈) with backward {xs} w∈
      ...                             | inj₁ ∈xs          =  inj₁ (there ∈xs)
      ...                             | inj₂ ∈ys          =  inj₂ ∈ys
      
    
\end{code}

# Operations with decidable equivalence

\begin{code}
    module DecCollection (_≟_ : ∀ (x y : A) → Dec (x ≈ y)) where

      abstract

        infix 5 _\\_

        _\\_ : Coll A → A → Coll A
        xs \\ x  =  filter (¬? ∘ (x ≟_)) xs


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
