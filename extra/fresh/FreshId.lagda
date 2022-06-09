---
title     : "FreshId: Generation of fresh names"
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
open Eq.≡-Reasoning
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List
  using (List; []; _∷_; _++_; map; foldr; replicate; length; _∷ʳ_)
  renaming (reverse to rev)
open import Data.List.Properties
  using (++-assoc; ++-identityʳ)
  renaming (unfold-reverse to revʳ;
            reverse-++-commute to rev-++;
            reverse-involutive to rev-inv)
open import Data.List.All using (All; []; _∷_)
open import Data.List.All.Properties
  renaming (++⁺ to _++All_)
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
-- open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Unary using (Decidable)
import Data.Nat as Nat
import Data.String as String
import Collections

pattern [_]       x        =  x ∷ []
pattern [_,_]     x y      =  x ∷ y ∷ []
pattern [_,_,_]   x y z    =  x ∷ y ∷ z ∷ []
pattern [_,_,_,_] x y z w  =  x ∷ y ∷ z ∷ w ∷ []
\end{code}

## DropWhile and TakeWhile for decidable predicates

\begin{code}
module Break {A : Set} where

  data Break (P : A → Set) : List A → Set where
    none : ∀ {xs} → All P xs → Break P xs
    some : ∀ {xs y zs} → All P xs → ¬ P y → Break P (xs ++ [ y ] ++ zs)

  break : ∀ {P : A → Set} (P? : Decidable P) → (xs : List A) → Break P xs
  break P? []                                           =  none []
  break P? (w ∷ ws) with P? w
  ...                  | no ¬Pw                         =  some [] ¬Pw
  ...                  | yes Pw with break P? ws
  ...                              | none Pws           =  none (Pw ∷ Pws)
  ...                              | some Pws ¬Py       =  some (Pw ∷ Pws) ¬Py

  takeWhile : ∀ {P : A → Set} (P? : Decidable P) → List A → List A
  takeWhile P? ws with break P? ws
  ...                | none {xs} Pxs               =  xs
  ...                | some {xs} {y} {zs} Pxs ¬Py  =  xs

  dropWhile : ∀ {P : A → Set} (P? : Decidable P) → List A → List A
  dropWhile P? ws with break P? ws
  ...                | none {xs} Pxs               =  []
  ...                | some {xs} {y} {zs} Pxs ¬Py  =  y ∷ zs

module RevBreak {A : Set} where

  open Break {A}

  data RevBreak (P : A → Set) : List A → Set where
    rnone : ∀ {xs} → All P (rev xs) → RevBreak P xs
    rsome : ∀ {zs y xs} → ¬ P y → All P (rev xs) → RevBreak P (zs ++ [ y ] ++ xs)

{-
  revBreak : ∀ {P : A → Set} (P? : Decidable P) → (xs : List A) → RevBreak P xs
  revBreak P? ws with break P? (rev ws)
  ... | none {xs} Pxs = ?
--    rewrite rev-inv ws
--    = rnone {xs = rev xs} Pxs
  ... | some {xs} {y} {zs} Pxs ¬Py = ?
--    rewrite rev-inv xs | rev-inv zs
--    = rsome {zs = rev zs} {y = y} {xs = rev xs} ¬Py Pxs
-}

{-
  _++All_ : ∀ {xs ys : List A} (P : A → Set) → All P xs → All P ys → All P (xs ++ ys)

  revAll : ∀ {xs : List A} (P : A → Set) → All P xs → All P (rev xs)

  data BBreak (P : A → Set) : List A → Set where
    none : ∀ {xs} → All P xs → BBreak P xs
    some : ∀ {xs y zs} → ¬ P y → All P zs → BBreak P (xs ++ [ y ] ++ zs)

  bbreak : ∀ {P : A → Set} (P? : Decidable P) → (xs : List A) → Break P xs
  bbreak P? ws with break P? (rev ws)
  ...             | none {xs} Pxs               =  none {rev xs} (revAll Pws)
  ...             | some {xs} {y} {zs} Pxs ¬Py  =  some ¬Py
-}
\end{code}

## Abstract operators prefix, suffix, and make

\begin{code}
{-
Id : Set
Id = String

open Collections (Id) (String._≟_)

module IdBase

  (P : Char → Set)
  (P? : ∀ (c : Char) → Dec (P c))
  (toℕ : List Char → ℕ)
  (fromℕ : ℕ → List Char)
  (toℕ∘fromℕ : ∀ (n : ℕ) → toℕ (fromℕ n) ≡ n)
  (fromℕ∘toℕ : ∀ (s : List Char) → (All P s) → fromℕ (toℕ s) ≡ s)
  where

  open Break

  isPrefix : String → Set
  isPrefix s =  ¬ Head P (reverse (toList s))

  Prefix : Set
  Prefix = ∃[ s ] (isPrefix s)

  body : Prefix → String
  body = proj₁

  prop : (p : Prefix) → isPrefix (body p)
  prop = proj₂

  make : Prefix → ℕ → Id
  make p n = fromList (toList (body p) ++ fromℕ n)

  prefixS : Id → String
  prefixS = fromList ∘ reverse ∘ dropWhile P? ∘ reverse ∘ toList

  prefixS-lemma : ∀ (x : Id) → isPrefix (prefixS x)
  prefixS-lemma x
    rewrite toList∘fromList ((reverse ∘ dropWhile P? ∘ reverse ∘ toList) x)
          | reverse-involutive ((dropWhile P? ∘ reverse ∘ toList) x)
    =  dropWhile-lemma P? ((reverse ∘ toList) x)

  prefix : Id → Prefix
  prefix x  =  ⟨ prefixS x , prefixS-lemma x ⟩

  suffix : Id → ℕ
  suffix =  length ∘ takeWhile P? ∘ reverse ∘ toList

  _≟Pr_ : ∀ (p q : Prefix) → Dec (body p ≡ body q)
  p ≟Pr q = (body p) String.≟ (body q)

  prefix-lemma : ∀ (p : Prefix) (n : ℕ) → prefix (make p n) ≡ p
  prefix-lemma p n = ?

  suffix-lemma : ∀ (p : Prefix) (n : ℕ) → suffix (make p n) ≡ n
  suffix-lemma = {!!}

  make-lemma : ∀ (x : Id) → make (prefix x) (suffix x) ≡ x
  make-lemma = {!!}
-}
\end{code}

## Main lemmas

\begin{code}
{-
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
-}
\end{code}

## Test cases

\begin{code}
{-
prime : Char
prime = '′'

isPrime : Char → Set
isPrime c  =  c ≡ prime

isPrime? : (c : Char) → Dec (isPrime c)
isPrime? c  =  c Char.≟ prime

toℕ : List Char → ℕ
toℕ s  =  length s

fromℕ : ℕ → List Char
fromℕ n  =  replicate n prime

toℕ∘fromℕ : ∀ (n : ℕ) → toℕ (fromℕ n) ≡ n
toℕ∘fromℕ = {!!}

fromℕ∘toℕ : ∀ (s : List Char) → All isPrime s → fromℕ (toℕ s) ≡ s
fromℕ∘toℕ = {!!}

open IdBase (isPrime) (isPrime?) (toℕ) (fromℕ) (toℕ∘fromℕ) (fromℕ∘toℕ)
open IdLemmas (Prefix) (prefix) (suffix) (make) (body) (_≟Pr_)
  (prefix-lemma) (suffix-lemma) (make-lemma)

x0 = "x"
x1 = "x′"
x2 = "x′′"
x3 = "x′′′"
y0 = "y"
y1 = "y′"
zs0 = "zs"
zs1 = "zs′"
zs2 = "zs′′"

_ : fresh x0 [ x0 , x1 , x2 , zs2 ] ≡ x3
_ = refl

-- fresh "x" [ "x" , "x′" , "x′′" , "y" ] ≡ "x′′′"

_ : fresh zs0 [ x0 , x1 , x2 , zs1 ] ≡ zs2
_ = refl
-}
\end{code}



