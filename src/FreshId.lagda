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
  reverse; partition; replicate; length; takeWhile; dropWhile)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; 1+n≰n)
open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.String using (String; toList; fromList; _≟_)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary.Decidable using (⌊_⌋)
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
\end{code}

## Abstract operators prefix, suffix, and make

\begin{code}
abstract

  data Head {A : Set} (P : A → Bool) : List A → Set where
    head : ∀ {x xs} → P x ≡ true → Head P (x ∷ xs)

  prime : Char
  prime = '′'

  isPrime : Char → Bool
  isPrime c = ⌊ c Char.≟ prime ⌋

  isPrefix : String → Set
  isPrefix s =  ¬ Head isPrime (reverse (toList s))

  Prefix : Set
  Prefix = ∃[ x ] (isPrefix x)

  body : Prefix → String
  body = proj₁

  make : Prefix → ℕ → Id
  make ⟨ s , _ ⟩ n = fromList (toList s ++ replicate n prime)

  prefixS : Id → String
  prefixS = fromList ∘ dropWhile isPrime ∘ reverse ∘ toList

  prefix : Id → Prefix
  prefix x  =  ⟨ s , pr ⟩ 
    where
    s : String
    s = prefixS x
    pr : isPrefix s
    pr = {!!}
    
  suffix : Id → ℕ
  suffix =  length ∘ takeWhile isPrime ∘ reverse ∘ toList

  _≟Pr_ : ∀ (p q : Prefix) → Dec (body p ≡ body q)
  p ≟Pr q = (body p) String.≟ (body q)

  prefix-lemma : ∀ {p n} → prefix (make p n) ≡ p
  prefix-lemma {p} {n} = {!!}

  suffix-lemma : ∀ {p n} → suffix (make p n) ≡ n
  suffix-lemma = {!!}

  make-lemma : ∀ {x} → make (prefix x) (suffix x) ≡ x
  make-lemma = {!!}
\end{code}

## Basic lemmas

\begin{code}
bump : Prefix → Id → ℕ
bump p x with p ≟Pr prefix x
...         | yes _  =  suc (suffix x)
...         | no  _  =  zero

next : Prefix → List Id → ℕ
next p  = foldr _⊔_ 0 ∘ map (bump p)

fresh : Id → List Id → Id
fresh x xs  =  make p (next p xs)
  where
  p = prefix x
\end{code}

## Test cases

\begin{code}
x0 = "x"
x1 = "x′"
x2 = "x′′"
x3 = "x′′′"
y0 = "y"
y1 = "y′"
zs4 = "zs′′′′"

_ : fresh x0 [ x0 , x1 , x2 , zs4 ] ≡ x3
_ = {!!}

_ : fresh y1 [ x0 , x1 , x2 , zs4 ] ≡ y0
_ = {!!}
\end{code}

## Main lemmas

\begin{code}
⊔-lemma : ∀ {p w xs} → w ∈ xs → bump p w ≤ next p xs
⊔-lemma {p} {_} {_ ∷ xs} here        =  m≤m⊔n _ (next p xs)
⊔-lemma {p} {w} {x ∷ xs} (there x∈)  =
  ≤-trans (⊔-lemma {p} {w} x∈) (n≤m⊔n (bump p x) (next p xs))

bump-lemma : ∀ {p n} → bump p (make p n) ≡ suc n
bump-lemma {p} {n}
  with p ≟Pr prefix (make p n)
...  | yes eqn  rewrite suffix-lemma {p} {n}  =  refl
...  | no  p≢   rewrite prefix-lemma {p} {n}  =  ⊥-elim (p≢ refl)

fresh-lemma : ∀ {w x xs} → w ∈ xs → w ≢ fresh x xs
fresh-lemma {w} {x} {xs} w∈  =  h {prefix x}
  where
  h : ∀ {p} → w ≢ make p (next p xs)
  h {p} refl
    with ⊔-lemma {p} {make p (next p xs)} {xs} w∈
  ... | leq rewrite bump-lemma {p} {next p xs} = 1+n≰n leq
\end{code}



