---
title     : "Lists Answers"
layout    : page
permalink : /ListsAns
---

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _∸_)
open import Data.Nat.Properties using (*-comm; *-distribˡ-+)
  renaming (*-distribʳ-+ to funny-*-distribʳ-+)
open import Data.List using (List; []; _∷_; [_]; _++_; length; foldr)
open import Data.Product using (proj₁; proj₂)
\end{code}

We copy the proofs of associativity and identity, which are hard to extract from
the standard libary.
\begin{code}
infix 5 _∷ ∷_

_∷ : ∀ {A : Set} → A → List A → List A
(x ∷) xs = x ∷ xs

∷_ : ∀ {A : Set} → List A → A → List A
(∷ xs) x = x ∷ xs

infix 5 _++ ++_ 

_++ : ∀ {A : Set} → List A → List A → List A
(xs ++) ys = xs ++ ys

++_ : ∀ {A : Set} → List A → List A → List A
(++ ys) xs = xs ++ ys

++-assoc : ∀ {A : Set} (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc [] ys zs =
  begin
    [] ++ (ys ++ zs)
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    ([] ++ ys) ++ zs
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs) ++ (ys ++ zs)
  ≡⟨⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨ cong (x ∷) (++-assoc xs ys zs) ⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨⟩
    ((x ∷ xs) ++ ys) ++ zs
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]
\end{code}


## Reverse and append

\begin{code}
reverse-++ : ∀ {A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ [] ys =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ []
  ≡⟨⟩
    reverse ys ++ reverse []
  ∎
reverse-++ (x ∷ xs) ys =
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (++ [ x ]) (reverse-++ xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ sym (++-assoc (reverse ys) (reverse xs) ([ x ])) ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎
\end{code}

## Reverse is involutive

\begin{code}
reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] =
  begin
    reverse (reverse [])
  ≡⟨⟩
    []
  ∎
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++ (reverse xs) ([ x ]) ⟩
    reverse ([ x ]) ++ reverse (reverse xs)
  ≡⟨⟩
    x ∷ reverse (reverse xs)
  ≡⟨ cong (x ∷) (reverse-involutive xs) ⟩
    x ∷ xs
  ∎
\end{code}




## Sum of count

The proof of distribution of multiplication over addition from
the standard library takes its arguments in a strange order.
We fix that here.
\begin{code}
*-distribʳ-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distribʳ-+ m n p = funny-*-distribʳ-+ p m n
\end{code}

\begin{code}
sum : List ℕ → ℕ
sum = foldr _+_ 0

downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

cong2 : ∀ {A B C : Set} {x x′ : A} {y y′ : B} →
  (f : A → B → C) → (x ≡ x′) → (y ≡ y′) → (f x y ≡ f x′ y′)
cong2 f x≡x′ y≡y′ rewrite x≡x′ | y≡y′ = refl

sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc zero) = refl
sum-downFrom (suc (suc n)) = 
  begin
    sum (downFrom (suc (suc n))) * 2
  ≡⟨⟩
    sum (suc n ∷ downFrom (suc n)) * 2
  ≡⟨⟩
    (suc n + sum (downFrom (suc n))) * 2
  ≡⟨ *-distribʳ-+ (suc n) (sum (downFrom (suc n))) 2 ⟩
    suc n * 2 + sum (downFrom (suc n)) * 2
  ≡⟨ cong (suc n * 2 +_) (sum-downFrom (suc n)) ⟩
    suc n * 2 + suc n * n
  ≡⟨ sym (*-distribˡ-+ (suc n) 2 n) ⟩
    suc n * (2 + n)
  ≡⟨ *-comm (suc n) (2 + n) ⟩
    suc (suc n) * suc n
  ∎
\end{code}

