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
open import Data.List using (List; []; _∷_; [_]; _++_; map; foldr; filter)
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

    infix 4 _∈_
    infix 4 _⊆_
    infixl 5 _\\_

    data _∈_ : A → List A → Set where

      here : ∀ {x xs} →
        ----------
        x ∈ x ∷ xs
        
      there : ∀ {w x xs} →
        w ∈ xs →
        ----------
        w ∈ x ∷ xs

    _⊆_ : List A → List A → Set
    xs ⊆ ys  =  ∀ {w} → w ∈ xs → w ∈ ys

    _\\_ : List A → A → List A
    xs \\ x  =  filter (¬? ∘ (_≟ x)) xs

    refl-⊆ : ∀ {xs} → xs ⊆ xs
    refl-⊆ ∈xs  =  ∈xs

    trans-⊆ : ∀ {xs ys zs} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
    trans-⊆ xs⊆ ys⊆  =  ys⊆ ∘ xs⊆

    ∈-[_] : ∀ {w x} → w ∈ [ x ] → w ≡ x
    ∈-[_] here         =  refl
    ∈-[_] (there ())

    there⁻¹ : ∀ {w x xs} → w ∈ x ∷ xs → w ≢ x → w ∈ xs
    there⁻¹ here       w≢  =  ⊥-elim (w≢ refl)
    there⁻¹ (there w∈) w≢  =  w∈

    there⟨_⟩ : ∀ {w x y xs} → w ∈ xs × w ≢ x → w ∈ y ∷ xs × w ≢ x
    there⟨ ⟨ w∈ , w≢ ⟩ ⟩  =  ⟨ there w∈ , w≢ ⟩

    \\-to-∈-≢ : ∀ {w x xs} → w ∈ xs \\ x → w ∈ xs × w ≢ x
    \\-to-∈-≢ {_} {x} {[]}    ()
    \\-to-∈-≢ {_} {x} {y ∷ _} w∈            with y ≟ x
    \\-to-∈-≢ {_} {x} {y ∷ _} w∈               | yes refl  =  there⟨ \\-to-∈-≢ w∈ ⟩
    \\-to-∈-≢ {_} {x} {y ∷ _} here             | no  w≢    =  ⟨ here , w≢ ⟩
    \\-to-∈-≢ {_} {x} {y ∷ _} (there w∈)       | no  _     =  there⟨ \\-to-∈-≢ w∈ ⟩

    ∈-≢-to-\\ : ∀ {w x xs} → w ∈ xs → w ≢ x → w ∈ xs \\ x
    ∈-≢-to-\\ {_} {x} {y ∷ _} here       w≢ with y ≟ x
    ...                                        | yes refl  =  ⊥-elim (w≢ refl)
    ...                                        | no  _     =  here
    ∈-≢-to-\\ {_} {x} {y ∷ _} (there w∈) w≢ with y ≟ x
    ...                                        | yes refl  =  ∈-≢-to-\\ w∈ w≢
    ...                                        | no  _     =  there (∈-≢-to-\\ w∈ w≢)


    \\-to-∷ : ∀ {x xs ys} → xs \\ x ⊆ ys → xs ⊆ x ∷ ys
    \\-to-∷ {x} ⊆ys {w} ∈xs
         with w ≟ x
    ...     | yes refl  =  here
    ...     | no  ≢x    =  there (⊆ys (∈-≢-to-\\ ∈xs ≢x))

    ∷-to-\\ : ∀ {x xs ys} → xs ⊆ x ∷ ys → xs \\ x ⊆ ys
    ∷-to-\\ {x} xs⊆ {w} w∈
         with \\-to-∈-≢ w∈
    ...     | ⟨ ∈xs , ≢x ⟩ with w ≟ x
    ...                       | yes refl                  =  ⊥-elim (≢x refl)
    ...                       | no  w≢   with (xs⊆ ∈xs)
    ...                                     | here        =  ⊥-elim (≢x refl)
    ...                                     | there ∈ys   =  ∈ys

    ⊆-++₁ : ∀ {xs ys} → xs ⊆ xs ++ ys
    ⊆-++₁ here         =  here
    ⊆-++₁ (there ∈xs)  =  there (⊆-++₁ ∈xs)

    ⊆-++₂ : ∀ {xs ys} → ys ⊆ xs ++ ys
    ⊆-++₂ {[]}     ∈ys  =  ∈ys
    ⊆-++₂ {x ∷ xs} ∈ys  =  there (⊆-++₂ {xs} ∈ys)

    ++-to-⊎ : ∀ {xs ys w} → w ∈ xs ++ ys → w ∈ xs ⊎ w ∈ ys
    ++-to-⊎ {[]}     ∈ys                            =  inj₂ ∈ys
    ++-to-⊎ {x ∷ xs} here                           =  inj₁ here
    ++-to-⊎ {x ∷ xs} (there w∈) with ++-to-⊎ {xs} w∈
    ...                            | inj₁ ∈xs       =  inj₁ (there ∈xs)
    ...                            | inj₂ ∈ys       =  inj₂ ∈ys


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
