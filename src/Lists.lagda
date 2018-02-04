---
title     : "Lists: Lists and other data types"
layout    : page
permalink : /Lists
---

This chapter gives examples of other data types in Agda, as well as
introducing polymorphic types and functions.

[This is a test.]

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
\end{code}

## Lists

Lists are defined in Agda as follows.
\begin{code}
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
\end{code}


Here

\begin{code}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}
\end{code}

List abbreviations.
\begin{code}
infix 5 [_
infixr 6 _,_
infix 7 _]

[_ : ∀ {A : Set} → List A → List A
[ xs  =  xs

_,_ : ∀ {A : Set} → A → List A → List A
x , xs = x ∷ xs

_] : ∀ {A : Set} → A → List A
x ] = x ∷ []
\end{code}

\begin{code}
ex₁ : [ 1 , 2 , 3 ] ≡ 1 ∷ 2 ∷ 3 ∷ []
ex₁ = refl
\end{code}

\begin{code}
infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

ex₂ : [ 1 , 2 , 3 ] ++ [ 4 , 5 ] ≡ [ 1 , 2 , 3 , 4 , 5 ]
ex₂ = refl

ex₃ : length ([ 1 , 2 , 3 ]) ≡ 3
ex₃ = refl

ex₄ : map (λ x → x * x) ([ 1 , 2 , 3 ]) ≡ [ 1 , 4 , 9 ]
ex₄ = refl

ex₅ : foldr _+_ 0 ([ 1 , 2 , 3 ]) ≡ 6
ex₅ = refl

ex₆ : length {ℕ} [] ≡ zero
ex₆ = refl
\end{code}

\begin{code}
_∷ : ∀ {A : Set} → A → List A → List A
x ∷ = λ xs → x ∷ xs

assoc-++ : ∀ {A : Set} (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ [] ys zs =
  begin
    [] ++ (ys ++ zs)
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    ([] ++ ys) ++ zs
  ∎
assoc-++ (x ∷ xs) ys zs =
  begin
    (x ∷ xs) ++ (ys ++ zs)
  ≡⟨⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨ cong (x ∷) (assoc-++ xs ys zs) ⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨⟩
    ((x ∷ xs) ++ ys) ++ zs
  ∎

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys = 
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎
\end{code}

\begin{code}
data _∈_ {A : Set} (x : A) : List A → Set where
  here : {y : A} {ys : List A} → x ≡ y → x ∈ y ∷ ys
  there : {y : A} {ys : List A} → x ∈ ys → x ∈ y ∷ ys

infix 4 _∈_
\end{code}

## Unicode

    ∷  U+2237  PROPORTION  (\::)
