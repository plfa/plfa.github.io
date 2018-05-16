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
open import Data.List.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; 1+n≰n)
open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
import Data.Char as Char using (_≟_)
open import Data.String using (String; toList; fromList; _≟_;
  toList∘fromList; fromList∘toList)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary.Decidable using (⌊_⌋)
import Data.Nat as Nat
import Data.String as String
import Collections

pattern [_]       x        =  x ∷ []
pattern [_,_]     x y      =  x ∷ y ∷ []
pattern [_,_,_]   x y z    =  x ∷ y ∷ z ∷ []
pattern [_,_,_,_] x y z w  =  x ∷ y ∷ z ∷ w ∷ []

\end{code}

## Abstract operators prefix, suffix, and make

\begin{code}
Id : Set
Id = String

module ListLemmas (A : Set) (P : A → Bool) where

  data Head : List A → Set where
    head : ∀ (x : A) (xs : List A) → T (P x) → Head (x ∷ xs)

  drop-lemma : ∀ (s : List A) → ¬ Head (dropWhile P s)
  drop-lemma [] = λ()
  drop-lemma (c ∷ s) with P c
  ...  | true   =  drop-lemma s
  ...  | false  =  f
    where
    f : ¬ Head (c ∷ s)
    f (head c s eq) = {!!}

  take-lemma : ∀ (s : List A) → All (T ∘ P) (takeWhile P s)
  take-lemma [] = []
  take-lemma (c ∷ s) with P c
  ...  | true   =  {!!} ∷ take-lemma s
  ...  | false  =  []

open Collections (Id) (String._≟_)

module IdBase
  (P : Char → Bool)
  (toℕ : List Char → ℕ)
  (fromℕ : ℕ → List Char)
  (toℕ∘fromℕ : ∀ (n : ℕ) → toℕ (fromℕ n) ≡ n)
  (fromℕ∘toℕ : ∀ (s : List Char) → (All (T ∘ P) s) → fromℕ (toℕ s) ≡ s)
  where

  open ListLemmas (Char) (P)

  isPrefix : String → Set
  isPrefix s =  ¬ Head (reverse (toList s))

  Prefix : Set
  Prefix = ∃[ x ] (isPrefix x)

  body : Prefix → String
  body = proj₁

  make : Prefix → ℕ → Id
  make p n = fromList (toList (body p) ++ fromℕ n)

  prefixS : Id → String
  prefixS = fromList ∘ dropWhile P ∘ reverse ∘ toList

  prefixS-lemma : ∀ (x : Id) → isPrefix (prefixS x)
  prefixS-lemma x  =  h (reverse (toList x))
    where
    h : ∀ (s : List Char) → isPrefix ((fromList ∘ dropWhile P) s)
    h = {!!}
    
  prefix : Id → Prefix
  prefix x  =  ⟨ prefixS x , prefixS-lemma x ⟩ 
    
  suffix : Id → ℕ
  suffix =  length ∘ takeWhile P ∘ reverse ∘ toList

  _≟Pr_ : ∀ (p q : Prefix) → Dec (body p ≡ body q)
  p ≟Pr q = (body p) String.≟ (body q)

  prefix-lemma : ∀ (p : Prefix) (n : ℕ) → prefix (make p n) ≡ p
  prefix-lemma = {!!}

  suffix-lemma : ∀ (p : Prefix) (n : ℕ) → suffix (make p n) ≡ n
  suffix-lemma = {!!}

  make-lemma : ∀ (x : Id) → make (prefix x) (suffix x) ≡ x
  make-lemma = {!!}
\end{code}

## Main lemmas

\begin{code}
module IdLemmas
  (Prefix : Set)
  (prefix : Id → Prefix)
  (suffix : Id → ℕ)
  (make : Prefix → ℕ → Id)
  (body : Prefix → String)
  (_≟Pr_ : ∀ (p q : Prefix) → Dec (body p ≡ body q))
  (prefix-lemma : ∀ (p : Prefix) (n : ℕ) → prefix (make p n) ≡ p)
  (suffix-lemma : ∀ (p : Prefix) (n : ℕ) → suffix (make p n) ≡ n)
  (make-lemma : ∀ (x : Id) → make (prefix x) (suffix x) ≡ x)
  where

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

  ⊔-lemma : ∀ {p w xs} → w ∈ xs → bump p w ≤ next p xs
  ⊔-lemma {p} {_} {_ ∷ xs} here        =  m≤m⊔n _ (next p xs)
  ⊔-lemma {p} {w} {x ∷ xs} (there x∈)  =
    ≤-trans (⊔-lemma {p} {w} x∈) (n≤m⊔n (bump p x) (next p xs))

  bump-lemma : ∀ {p n} → bump p (make p n) ≡ suc n
  bump-lemma {p} {n}
    with p ≟Pr prefix (make p n)
  ...  | yes eqn  rewrite suffix-lemma p n  =  refl
  ...  | no  p≢   rewrite prefix-lemma p n  =  ⊥-elim (p≢ refl)

  fresh-lemma : ∀ {w x xs} → w ∈ xs → w ≢ fresh x xs
  fresh-lemma {w} {x} {xs} w∈  =  h {prefix x}
    where
    h : ∀ {p} → w ≢ make p (next p xs)
    h {p} refl
      with ⊔-lemma {p} {make p (next p xs)} {xs} w∈
    ... | leq rewrite bump-lemma {p} {next p xs} = 1+n≰n leq
\end{code}

## Test cases

\begin{code}
prime : Char
prime = '′'

isPrime : Char → Bool
isPrime c = ⌊ c Char.≟ prime ⌋

toℕ : List Char → ℕ
toℕ s  =  length s

fromℕ : ℕ → List Char
fromℕ n  =  replicate n prime

toℕ∘fromℕ : ∀ (n : ℕ) → toℕ (fromℕ n) ≡ n
toℕ∘fromℕ = {!!}

fromℕ∘toℕ : ∀ (s : List Char) → All (T ∘ isPrime) s → fromℕ (toℕ s) ≡ s
fromℕ∘toℕ = {!!}

open IdBase (isPrime) (toℕ) (fromℕ) (toℕ∘fromℕ) (fromℕ∘toℕ)
open IdLemmas (Prefix) (prefix) (suffix) (make) (body) (_≟Pr_)
  (prefix-lemma) (suffix-lemma) (make-lemma)

x0 = "x"
x1 = "x′"
x2 = "x′′"
x3 = "x′′′"
y0 = "y"
y1 = "y′"
zs4 = "zs′′′′"

_ : fresh x0 [ x0 , x1 , x2 , zs4 ] ≡ x3
_ = refl

-- fresh "x" [ "x" , "x′" , "x′′" , "y" ] ≡ "x′′′"

_ : fresh y1 [ x0 , x1 , x2 , zs4 ] ≡ y0
_ = refl
\end{code}



