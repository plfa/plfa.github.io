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

++-identityʳ : ∀ (us : List Id) → us ++ [] ≡ us
++-identityʳ []        =  refl
++-identityʳ (u ∷ us)  =  cong (u ∷_) (++-identityʳ us)

++-assoc : ∀ (us vs ws : List Id) →
  (us ++ vs) ++ ws ≡ us ++ (vs ++ ws)
++-assoc [] vs ws        =  refl
++-assoc (u ∷ us) vs ws  =  cong (u ∷_) (++-assoc us vs ws)

lemma : ∀ (us : List Id) (v w : Id)
  → w ∉ us → w ≢ v → w ∉ (us ++ [ v ])
lemma []       v w w∉ w≢ =  λ{ here → w≢ refl
                              ; (there ())
                              }
lemma (u ∷ us) v w w∉ w≢ =  λ{ here → w∉ here
                              ; (there y∈) → (lemma us v w (w∉ ∘ there) w≢) y∈
                              }

helper : ∀ (n : ℕ) (us vs xs : List Id) (w : Id)
  → w ∉ us → us ++ vs ≡ xs → ∃[ y ]( y ∉ xs)
helper n us []       xs w w∉ refl rewrite ++-identityʳ us = ⟨ w , w∉ ⟩
helper n us (v ∷ vs) xs w w∉ refl with w ≟ v
helper n us (v ∷ vs) xs w w∉ refl | no w≢
  =  helper n (us ++ [ v ]) vs xs w (lemma us v w w∉ w≢) (++-assoc us [ v ] vs)
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
