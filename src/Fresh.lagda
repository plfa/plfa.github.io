---
title     : "Fresh: Choose fresh variable name"
layout    : page
permalink : /Fresh
---

## Imports

\begin{code}
module Fresh where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; foldr; filter; concat; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; 1+n≰n)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)
import Data.String as Str
import Collections

pattern [_]       w        =  w ∷ []
pattern [_,_]     w x      =  w ∷ x ∷ []
pattern [_,_,_]   w x y    =  w ∷ x ∷ y ∷ []
pattern [_,_,_,_] w x y z  =  w ∷ x ∷ y ∷ z ∷ []
\end{code}

\begin{code}
Id : Set
Id = String

open Collections (Id) (_≟_)

prime : Id → Id
prime x = x Str.++ "′"

lemma₀ : ∀ (us : List Id) → us ++ [] ≡ us
lemma₀ []        =  refl
lemma₀ (u ∷ us)  =  cong (u ∷_) (lemma₀ us)

lemma₁ : ∀ (us vs : List Id) (v : Id) →
  (us ++ [ v ]) ++ vs ≡ us ++ (v ∷ vs)
lemma₁ [] vs v        =  refl
lemma₁ (u ∷ us) vs v  =  cong (u ∷_) (lemma₁ us vs v)

lemma₂ : ∀ (us : List Id) (v w : Id)
  → w ∉ us → w ≢ v → w ∉ (us ++ [ v ])
lemma₂ []       v w w∉ w≢ =  λ{ here → w≢ refl
                              ; (there ())
                              }
lemma₂ (u ∷ us) v w w∉ w≢ =  λ{ here → w∉ here
                              ; (there y∈) → (lemma₂ us v w (w∉ ∘ there) w≢) y∈
                              }

helper : ∀ (n : ℕ) (us vs xs : List Id) (w : Id)
  → w ∉ us → us ++ vs ≡ xs → ∃[ y ]( y ∉ xs)
helper n us []       xs w w∉ refl rewrite lemma₀ us = ⟨ w , w∉ ⟩
helper n us (v ∷ vs) xs w w∉ refl with w ≟ v
helper n us (v ∷ vs) xs w w∉ refl | no w≢
  =  helper n (us ++ [ v ]) vs xs w (lemma₂ us v w w∉ w≢) (lemma₁ us vs v)
helper (suc n) us (v ∷ vs) xs w w∉ refl | yes _
  =  helper n [] xs xs w (λ()) refl
helper zero us (v ∷ vs) xs w w∉ refl | yes _
  =  ⊥-elim impossible
  where postulate impossible : ⊥

fresh : List Id → Id → Id
fresh xs y = proj₁ (helper (length xs) [] xs xs y (λ()) refl)

fresh-lemma : ∀ (xs : List Id) (x : Id) → fresh xs x ∉ xs
fresh-lemma xs y = proj₂ (helper (length xs) [] xs xs y (λ()) refl)
\end{code}
