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
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
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

br : Id → String × ℕ
br x with partition (Char._≟_ '′') (reverse (toList x))
... | ⟨ s , t ⟩  =  ⟨ fromList (reverse t) , length s ⟩

Prefix : Set
Prefix = ∃[ x ] (proj₂ (br x) ≡ zero)

br-lemma : (x : Id) → proj₂ (br (proj₁ (br x))) ≡ zero
br-lemma = {!!}

break : Id → Prefix × ℕ
break x  =  ⟨ ⟨ s , br-lemma x ⟩ , n ⟩
  where
  s = proj₁ (br x)
  n = proj₂ (br x)

make : Prefix → ℕ → Id
make s n  =  fromList (toList (proj₁ s) ++ replicate n '′')

bump : Prefix → Id → ℕ
bump s x with proj₁ s String.≟ proj₁ (proj₁ (break x))
...         | yes _  =  suc (proj₂ (break x))
...         | no  _  =  zero

next : Prefix → List Id → ℕ
next s  = foldr _⊔_ 0 ∘ map (bump s)

fresh : Id → List Id → Id
fresh x xs  =  make s (next s xs)
  where
  s = proj₁ (break x)

x0 = "x"
x1 = "x′"
x2 = "x′′"
x3 = "x′′′"
y0 = "y"
y1 = "y′"
zs4 = "zs′′′′"

_ : fresh x0 [ x0 , x1 , x2 , zs4 ] ≡ x3
_ = refl

_ : fresh y1 [ x0 , x1 , x2 , zs4 ] ≡ y0
_ = refl

break-lemma₁ : ∀ {s n} → proj₁ (break (make s n)) ≡ s
break-lemma₁ = {!!}

break-lemma₂ : ∀ {s n} → proj₂ (break (make s n)) ≡ n
break-lemma₂ = {!!}

make-lemma : ∀ {x} → x ≡ make (proj₁ (break x)) (proj₂ (break x))
make-lemma = {!!}

⊔-lemma : ∀ {s w xs} → w ∈ xs → bump s w ≤ next s xs
⊔-lemma {s} {_} {_ ∷ xs} here        =  m≤m⊔n _ (next s xs)
⊔-lemma {s} {w} {x ∷ xs} (there x∈)  =
  ≤-trans (⊔-lemma {s} {w} x∈) (n≤m⊔n (bump s x) (next s xs))

bump-lemma : ∀ {s n} → bump s (make s n) ≡ suc n
bump-lemma {s} {n} rewrite break-lemma₁ {s} {n} | break-lemma₂ {s} {n}
  with proj₁ s ≟ proj₁ s
...  | yes refl rewrite break-lemma₁ {s} {n} | break-lemma₂ {s} {n} = {! refl!}
...  | no  s≢s  = ⊥-elim (s≢s refl)

fresh-lemma₁ : ∀ {s n w xs} → w ∈ xs → w ≢ fresh (make s n) xs
fresh-lemma₁ {s} {n} {w} {xs} w∈ refl
  with ⊔-lemma {s} {make s (next s xs)} {xs} {!!} -- w∈
...  | prf rewrite bump-lemma {s} {next s xs} = 1+n≰n prf

fresh-lemma : ∀ {x w xs} → w ∈ xs → w ≢ fresh x xs
fresh-lemma {x} {w} {xs} w∈ refl rewrite make-lemma {x}
  = fresh-lemma₁ {s} {n} {w} {xs} {!!} {- w∈ -} {! refl!} -- refl
  where
  s = proj₁ (break x)
  n = proj₂ (break x)
\end{code}

Why does `⊔-lemma` imply `fresh x xs ∉ xs`?

    fresh : Id → List Id → Id
    fresh x xs with break x
    ...           | ⟨ s , _ ⟩ = make s (next s xs)

So

    bump s (make s (next s xs)) ≤ next s xs

becomes

    suc (next s xs) ≤ next s xs



