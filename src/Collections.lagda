---
title     : "Collections: Representing collections as lists"
layout    : page
permalink : /Collections
---

This chapter presents operations on collections and a number of
useful operations on them.


## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
-- open import Data.Nat.Properties using
--   (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
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
-- open import Relation.Binary using (IsEquivalence)
\end{code}


## Collections

\begin{code}
infix 0 _↔_

_↔_ : Set → Set → Set
A ↔ B  =  (A → B) × (B → A)

module CollectionDec (A : Set) (_≟_ : ∀ (x y : A) → Dec (x ≡ y)) where

    Coll : Set → Set
    Coll A  =  List A

    [_] : A → Coll A
    [ x ]  =  x ∷ []

    infix 4 _∈_
    infix 4 _⊆_
    infixl 5 _∪_
    infixl 5 _\\_

    data _∈_ : A → Coll A → Set where

      here : ∀ {x xs} →
        ----------
        x ∈ x ∷ xs
        
      there : ∀ {w x xs} →
        w ∈ xs →
        ----------
        w ∈ x ∷ xs

    _⊆_ : Coll A → Coll A → Set
    xs ⊆ ys  =  ∀ {w} → w ∈ xs → w ∈ ys

    _∪_ : Coll A → Coll A → Coll A
    _∪_ = _++_

    _\\_ : Coll A → A → Coll A
    xs \\ x  =  filter (¬? ∘ (_≟ x)) xs

    refl-⊆ : ∀ {xs} → xs ⊆ xs
    refl-⊆ ∈xs  =  ∈xs

    trans-⊆ : ∀ {xs ys zs} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
    trans-⊆ xs⊆ ys⊆  =  ys⊆ ∘ xs⊆

    lemma-[_] : ∀ {w xs} → w ∈ xs ↔ [ w ] ⊆ xs
    lemma-[_] = ⟨ forward , backward ⟩
      where

      forward : ∀ {w xs} → w ∈ xs → [ w ] ⊆ xs
      forward ∈xs here        =  ∈xs
      forward ∈xs (there ())

      backward : ∀ {w xs} → [ w ] ⊆ xs → w ∈ xs
      backward ⊆xs  =  ⊆xs here

    lemma-\\-∈-≢ : ∀ {w x xs} → w ∈ xs \\ x ↔ w ∈ xs × w ≢ x
    lemma-\\-∈-≢ = ⟨ forward , backward ⟩
      where    

      next : ∀ {w x y xs} → w ∈ xs × w ≢ x → w ∈ y ∷ xs × w ≢ x
      next ⟨ w∈ , w≢ ⟩   =  ⟨ there w∈ , w≢ ⟩

      forward : ∀ {w x xs} → w ∈ xs \\ x → w ∈ xs × w ≢ x
      forward {_} {x} {[]}    ()
      forward {_} {x} {y ∷ _} w∈         with y ≟ x
      forward {_} {x} {y ∷ _} w∈            | yes refl  =  next (forward w∈)
      forward {_} {x} {y ∷ _} here          | no  y≢    =  ⟨ here , (λ y≡ → y≢ y≡) ⟩
      forward {_} {x} {y ∷ _} (there w∈)    | no  _     =  next (forward w∈)

      backward : ∀ {w x xs} → w ∈ xs × w ≢ x → w ∈ xs \\ x
      backward {_} {x} {y ∷ _} ⟨ here     , w≢ ⟩
                                         with y ≟ x
      ...                                   | yes refl  =  ⊥-elim (w≢ refl)
      ...                                   | no  _     =  here
      backward {_} {x} {y ∷ _} ⟨ there w∈ , w≢ ⟩
                                         with y ≟ x
      ...                                  | yes refl   =  backward ⟨ w∈ , w≢ ⟩
      ...                                  | no  _      =  there (backward ⟨ w∈ , w≢ ⟩)


    lemma-\\-∷ : ∀ {x xs ys} → xs \\ x ⊆ ys ↔ xs ⊆ x ∷ ys
    lemma-\\-∷ = ⟨ forward , backward ⟩
      where

      forward : ∀ {x xs ys} → xs \\ x ⊆ ys → xs ⊆ x ∷ ys
      forward {x} ⊆ys {w} ∈xs
           with w ≟ x
      ...     | yes refl  =  here
      ...     | no  ≢x    =  there (⊆ys (proj₂ lemma-\\-∈-≢ ⟨ ∈xs , ≢x ⟩))

      backward : ∀ {x xs ys} → xs ⊆ x ∷ ys → xs \\ x ⊆ ys
      backward {x} xs⊆ {w} w∈
           with proj₁ lemma-\\-∈-≢ w∈
      ...     | ⟨ ∈xs , ≢x ⟩ with w ≟ x
      ...                       | yes refl                  =  ⊥-elim (≢x refl)
      ...                       | no  w≢   with (xs⊆ ∈xs)
      ...                                     | here        =  ⊥-elim (≢x refl)
      ...                                     | there ∈ys   =  ∈ys

    lemma-∪₁ : ∀ {xs ys} → xs ⊆ xs ∪ ys
    lemma-∪₁ here         =  here
    lemma-∪₁ (there ∈xs)  =  there (lemma-∪₁ ∈xs)

    lemma-∪₂ : ∀ {xs ys} → ys ⊆ xs ∪ ys
    lemma-∪₂ {[]}     ∈ys  =  ∈ys
    lemma-∪₂ {x ∷ xs} ∈ys  =  there (lemma-∪₂ {xs} ∈ys)

    lemma-⊎-∪ : ∀ {w xs ys} → w ∈ xs ⊎ w ∈ ys ↔ w ∈ xs ∪ ys
    lemma-⊎-∪ = ⟨ forward , backward ⟩
      where

      forward : ∀ {w xs ys} → w ∈ xs ⊎ w ∈ ys → w ∈ xs ∪ ys
      forward (inj₁ ∈xs)  =  lemma-∪₁ ∈xs
      forward (inj₂ ∈ys)  =  lemma-∪₂ ∈ys

      backward : ∀ {xs ys w} → w ∈ xs ∪ ys → w ∈ xs ⊎ w ∈ ys
      backward {[]}     ∈ys                               =  inj₂ ∈ys
      backward {x ∷ xs} here                              =  inj₁ here
      backward {x ∷ xs} (there w∈) with backward {xs} w∈
      ...                             | inj₁ ∈xs          =  inj₁ (there ∈xs)
      ...                             | inj₂ ∈ys          =  inj₂ ∈ys


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
