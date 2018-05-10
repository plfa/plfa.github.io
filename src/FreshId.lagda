---
title     : "FreshId: Generation of fresh names"
layout    : page
permalink : /FreshId
---

Generation of fresh names, where names are strings.
Each name has a base (a string not ending in a prime)
and a suffix (a sequence of primes).

Based on an earlier version fixed by James McKinna.

\begin{code}
module FreshId where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; foldr; filter;
  reverse; partition; replicate; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; 1+n≰n)
open import Data.String using (String; toList; fromList; _≟_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)
import Data.Nat as Nat
import Data.String as String
import Data.Char as Char
import Collections

pattern [_]       x        =  x ∷ []
pattern [_,_]     x y      =  x ∷ y ∷ []
pattern [_,_,_]   x y z    =  x ∷ y ∷ z ∷ []
pattern [_,_,_,_] x y z w  =  x ∷ y ∷ z ∷ w ∷ []

Id : Set
Id = String

open Collections (Id) (String._≟_)

break : Id → String × ℕ
break x with partition (Char._≟_ '′') (reverse (toList x))
... | ⟨ s , t ⟩  =  ⟨ fromList (reverse t) , length s ⟩

make : String → ℕ → Id
make s n  =  fromList (toList s ++ replicate n '′')

bump : String → Id → ℕ
bump s x with break x
...         | ⟨ t , n ⟩ with s String.≟ t
...                        | yes _          = suc n
...                        | no  _          = 0

next : String → List Id → ℕ
next s  = foldr _⊔_ 0 ∘ map (bump s)

fresh : Id → List Id → Id
fresh x xs with break x
...           | ⟨ s , _ ⟩ = make s (next s xs)

x0 = "x"
x1 = "x′"
x2 = "x′′"
x3 = "x′′′"
y0 = "y"
y1 = "y′"
zs4 = "zs′′′′"

_ : break x2 ≡ ⟨ "x" , 2 ⟩
_ = refl

_ : break zs4 ≡ ⟨ "zs" , 4 ⟩
_ = refl

_ : fresh x0 [ x0 , x1 , x2 , zs4 ] ≡ x3
_ = refl

_ : fresh y1 [ x0 , x1 , x2 , zs4 ] ≡ y0
_ = refl

⊔-lemma : ∀ {s w xs} → w ∈ xs → bump s w ≤ next s xs
⊔-lemma {s} {_} {_ ∷ xs} here        =  m≤m⊔n _ (next s xs)
⊔-lemma {s} {w} {x ∷ xs} (there x∈)  =
  ≤-trans (⊔-lemma {s} {w} x∈) (n≤m⊔n (bump s x) (next s xs))

{-
bump-lemma : ∀ {s n} → bump s (make s n) ≡ suc n
bump-lemma = {!!}

fresh-lemma : ∀ {x w xs} → w ∈ xs → w ≢ fresh x xs
fresh-lemma {x} {w} {xs} w∈ w≡ with break x
... | ⟨ s , _ ⟩ with w≡
...    | refl with ⊔-lemma {s} {make s (next s xs)} {xs} w∈
...        | prf rewrite bump-lemma {s} {next s xs} = 1+n≰n prf
-}
\end{code}

Why does `⊔-lemma` imply `fresh x xs ∉ xs`?

    fresh : Id → List Id → Id
    fresh x xs with break x
    ...           | ⟨ s , _ ⟩ = make s (next s xs)

So

    bump s (make s (next s xs)) ≤ next s xs

becomes

    suc (next s xs) ≤ next s xs



