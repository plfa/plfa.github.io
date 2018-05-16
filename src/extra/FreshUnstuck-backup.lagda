---
title     : "FreshUnstuck: Generation of fresh names with strings"
layout    : page
permalink : /FreshUnstuck
---

Generation of fresh names, where names are string-integer pairs.
Fixed by James McKinna.

\begin{code}
module FreshUnstuck where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; foldr; filter)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; 1+n≰n)
open import Data.String using (String)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)
import Data.Nat as Nat
import Data.String as String

data Id : Set where
  id : String → ℕ → Id

_≟_ : ∀ (x y : Id) → Dec (x ≡ y)
id s m ≟ id t n with s String.≟ t | m Nat.≟ n
...                | yes refl     | yes refl   =  yes refl
...                | yes refl     | no  m≢n    =  no (λ {refl → m≢n refl})
...                | no  s≢t      | _          =  no (λ {refl → s≢t refl})

infix 4 _∈_

data _∈_ : Id → List Id → Set where

      here : ∀ {x xs} →
        ----------
        x ∈ x ∷ xs
        
      there : ∀ {w x xs} →
        w ∈ xs →
        ----------
        w ∈ x ∷ xs

bump : String → Id → ℕ
bump s (id t n) with s String.≟ t
...                | yes refl       = suc n
...                | no  _          = 0

next : String → List Id → ℕ
next s  = foldr _⊔_ 0 ∘ map (bump s)

⊔-lemma : ∀ {s w xs} → w ∈ xs → bump s w ≤ next s xs
⊔-lemma {s} {_} {_ ∷ xs} here        =  m≤m⊔n _ (next s xs)
⊔-lemma {s} {w} {x ∷ xs} (there x∈)  =  ≤-trans (⊔-lemma {s} {w} x∈) (n≤m⊔n (bump s x) (next s xs)) 

fresh : Id → List Id → Id
fresh (id s _) xs = id s (next s xs)

id-invert-str : ∀ {s t m n} → (id s m) ≡ (id t n) → t ≡ s
id-invert-str refl = refl 

id-invert-nat : ∀ {s t m n} → (id s m) ≡ (id t n) → n ≡ m
id-invert-nat refl = refl

not-suc-le : ∀ {n} → ¬ (suc n ≤ n)
not-suc-le {zero} ()
not-suc-le {suc n} (Nat.s≤s sn≤n) = not-suc-le sn≤n 

fresh-lemma : ∀ {w x xs} → w ∈ xs → w ≢ fresh x xs
fresh-lemma {w @ (id t n)} {x @ (id s _)} {xs} w∈ w≢fr
  with s String.≟ t | ⊔-lemma {s} {w} {xs} w∈ 
... | yes refl | prf rewrite id-invert-nat w≢fr = not-suc-le prf 
... | no ¬p    | _  = ¬p (id-invert-str w≢fr)

pattern [_]       x        =  x ∷ []
pattern [_,_]     x y      =  x ∷ y ∷ []
pattern [_,_,_]   x y z    =  x ∷ y ∷ z ∷ []
pattern [_,_,_,_] x y z w  =  x ∷ y ∷ z ∷ w ∷ []

x0 = id "x" 0
x1 = id "x" 1
x2 = id "x" 2
x3 = id "x" 3
y0 = id "y" 0
y1 = id "y" 1
z4 = id "z" 4

_ : fresh x0 [ x0 , x1 , x2 , z4 ] ≡ x3
_ = refl

_ : fresh y1 [ x0 , x1 , x2 , z4 ] ≡ y0
_ = refl
\end{code}
