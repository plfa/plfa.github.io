---
title     : "Untyped: Untyped lambda calculus with full normalisation"
layout    : page
permalink : /Untyped
---

This chapter considers a system that varies, in interesting ways,
what has gone earlier.  The lambda calculus in this section is
untyped rather than simply-typed; uses terms that are inherently-scoped
(as opposed to inherently-typed); reduces terms to full normal form
rather than weak head-normal form; and uses call-by-name rather than
call-by-value order of reduction.

## Imports

\begin{code}
module Untyped where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)
\end{code}


## Syntax

\begin{code}
infix  6  ƛ_
infixl 7  _·_

data Var : ℕ → Set where

  Z : ∀ {n}
     -----------
   → Var (suc n)

  S_ : ∀ {n}
    → Var n
      -----------
    → Var (suc n)

data Term : ℕ → Set where

  ⌊_⌋ : ∀ {n}
    → Var n
      ------
    → Term n

  ƛ_  :  ∀ {n}
    → Term (suc n)
      ------------
    → Term n

  _·_ : ∀ {n}
    → Term n
    → Term n
      ------
    → Term n
\end{code}

## Writing variables as numerals

\begin{code}
#_ : ∀ {n} → ℕ → Term n
#_ {n} m  =  ⌊ h n m ⌋
  where
  h : ∀ n → ℕ → Var n
  h zero    _        =  ⊥-elim impossible
    where postulate impossible : ⊥
  h (suc n) 0        =  Z
  h (suc n) (suc m)  =  S (h n m)
\end{code}

## Test examples

\begin{code}
plus : ∀ {n} → Term n
plus = ƛ ƛ ƛ ƛ ⌊ S S S Z ⌋ · ⌊ S Z ⌋ · (⌊ S S Z ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)

two : ∀ {n} → Term n
two = ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)

four : ∀ {n} → Term n
four = ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))
\end{code}

## Renaming

\begin{code}
rename : ∀ {m n} → (Var m → Var n) → (Term m → Term n)
rename ρ ⌊ k ⌋            =  ⌊ ρ k ⌋
rename {m} {n} ρ (ƛ N)    =  ƛ (rename {suc m} {suc n} ρ′ N)
  where
  ρ′ : Var (suc m) → Var (suc n)
  ρ′ Z      =  Z
  ρ′ (S k)  =  S (ρ k)
rename ρ (L · M)           =  (rename ρ L) · (rename ρ M)
\end{code}

## Substitution

\begin{code}
subst : ∀ {m n} → (Var m → Term n) → (Term m → Term n)
subst ρ ⌊ k ⌋                =  ρ k
subst {m} {n} ρ (ƛ N)        =  ƛ (subst {suc m} {suc n} ρ′ N)
  where
  ρ′ : Var (suc m) → Term (suc n)
  ρ′ Z      =  ⌊ Z ⌋
  ρ′ (S k)  =  rename {n} {suc n} S_ (ρ k)
subst ρ (L · M)               =  (subst ρ L) · (subst ρ M)

_[_] : ∀ {n} → Term (suc n) → Term n → Term n
_[_] {n} N M  =  subst {suc n} {n} ρ N
  where
  ρ : Var (suc n) → Term n
  ρ Z      =  M
  ρ (S k)  =  ⌊ k ⌋
\end{code}

## Normal

\begin{code}
data Normal  : ∀ {n} → Term n → Set
data Neutral : ∀ {n} → Term n → Set

data Normal where
  ƛ_  : ∀ {n} {N : Term (suc n)} → Normal N → Normal (ƛ N)
  ⌈_⌉ : ∀ {n} {M : Term n} → Neutral M → Normal M

data Neutral where
  ⌊_⌋  : ∀ {n} → (k : Var n) → Neutral ⌊ k ⌋
  _·_  : ∀ {n} → {L : Term n} {M : Term n} → Neutral L → Normal M → Neutral (L · M)
\end{code}

## Reduction step

\begin{code}
infix 2 _⟶_

data App : ∀ {n} → Term n → Set where
  app : ∀ {n}
    → {L : Term n}
    → {M : Term n}
      ------------
    → App (L · M)

data _⟶_ : ∀ {n} → Term n → Term n → Set where

  ξ₁ : ∀ {n} {L L′ M : Term n}
    → App L
    → L ⟶ L′
      ----------------
    → L · M ⟶ L′ · M

{-
  ξ₁ : ∀ {n} {L M LM′ N : Term n}
    → L · M ⟶ LM′
      ---------------------
    → L · M · N ⟶ LM′ · N
-}

  ξ₂ : ∀ {n} {L M M′ : Term n}
    → Neutral L
    → M ⟶ M′
      ----------------
    → L · M ⟶ L · M′

  β : ∀ {n} {N : Term (suc n)} {M : Term n}
      -------------------------------------
    → (ƛ N) · M ⟶ N [ M ]

  ζ : ∀ {n} {N N′ : Term (suc n)}
    → N ⟶ N′
      -----------
    → ƛ N ⟶ ƛ N′
\end{code}

## Reflexive and transitive closure

\begin{code}
infix  2 _⟶*_
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3 _∎

data _⟶*_ : ∀ {n} → Term n → Term n → Set where

  _∎ : ∀ {n} (M : Term n)
      ---------------------
    → M ⟶* M

  _⟶⟨_⟩_ : ∀ {n} (L : Term n) {M N : Term n}
    → L ⟶ M
    → M ⟶* N
      ---------
    → L ⟶* N

begin_ : ∀ {n} {M N : Term n} → (M ⟶* N) → (M ⟶* N)
begin M⟶*N = M⟶*N
\end{code}


## Example reduction sequences

\begin{code}
id : Term zero
id = ƛ ⌊ Z ⌋

_ : id · id  ⟶* id
_ =
  begin
    (ƛ ⌊ Z ⌋) · (ƛ ⌊ Z ⌋)
  ⟶⟨ β ⟩
    ƛ ⌊ Z ⌋
  ∎

_ : plus {zero} · two · two ⟶* four
_ =
  begin
    plus · two · two
  ⟶⟨ ξ₁ app β ⟩
    (ƛ ƛ ƛ two · ⌊ S Z ⌋ · (⌊ S (S Z) ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)) · two
  ⟶⟨ β ⟩
    ƛ ƛ two · ⌊ S Z ⌋ · (two · ⌊ S Z ⌋ · ⌊ Z ⌋)
  ⟶⟨ ζ (ζ (ξ₁ app β)) ⟩
    ƛ ƛ (ƛ ⌊ S (S Z) ⌋ · (⌊ S (S Z) ⌋ · ⌊ Z ⌋)) · (two · ⌊ S Z ⌋ · ⌊ Z ⌋)
  ⟶⟨ ζ (ζ β) ⟩
    ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (two · ⌊ S Z ⌋ · ⌊ Z ⌋))
  ⟶⟨ ζ (ζ (ξ₂ ⌊ S Z ⌋ (ξ₂ ⌊ S Z ⌋ (ξ₁ app β)))) ⟩
    ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ((ƛ ⌊ S (S Z) ⌋ · (⌊ S (S Z) ⌋ · ⌊ Z ⌋)) · ⌊ Z ⌋))
  ⟶⟨ ζ (ζ (ξ₂ ⌊ S Z ⌋ (ξ₂ ⌊ S Z ⌋ β))) ⟩
   ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))))
  ∎
\end{code}


## Progress

\begin{code}
data Progress {n} (M : Term n) : Set where

  step : ∀ {N : Term n}
    → M ⟶ N
      ----------
    → Progress M

  done :
      Normal M
      ----------
    → Progress M

progress : ∀ {n} → (M : Term n) → Progress M
progress ⌊ x ⌋                                 =  done ⌈ ⌊ x ⌋ ⌉
progress (ƛ N)  with  progress N
... | step N⟶N′                              =  step (ζ N⟶N′)
... | done Nⁿ                                  =  done (ƛ Nⁿ)
progress (⌊ x ⌋ · M) with progress M
... | step M⟶M′                              =  step (ξ₂ ⌊ x ⌋ M⟶M′)
... | done Mⁿ                                  =  done ⌈ ⌊ x ⌋ · Mⁿ ⌉
progress ((ƛ N) · M)                           =  step β
progress (L@(_ · _) · M) with progress L
... | step L⟶L′                              =  step (ξ₁ app L⟶L′)
... | done ⌈ Lᵘ ⌉ with progress M
...    | step M⟶M′                           =  step (ξ₂ Lᵘ M⟶M′)
...    | done Mⁿ                               =  done ⌈ Lᵘ · Mⁿ ⌉
\end{code}


## Normalise

\begin{code}
Gas : Set
Gas = ℕ

data Normalise {n} (M : Term n) : Set where

  out-of-gas : ∀ {N : Term n}
    → M ⟶* N
      -------------
    → Normalise M

  normal : ∀ {N : Term n}
    → Gas
    → M ⟶* N
    → Normal N
     --------------
    → Normalise M

normalise : ∀ {n}
  → Gas
  → ∀ (M : Term n)
    -------------
  → Normalise M
normalise zero L                         =  out-of-gas (L ∎)
normalise (suc g) L with progress L
... | done Lⁿ                            =  normal (suc g) (L ∎) Lⁿ
... | step {M} L⟶M with normalise g M
...     | out-of-gas M⟶*N              =  out-of-gas (L ⟶⟨ L⟶M ⟩ M⟶*N)
...     | normal g′ M⟶*N Nⁿ            =  normal g′ (L ⟶⟨ L⟶M ⟩ M⟶*N) Nⁿ
\end{code}

\begin{code}
_ : normalise 100 (plus {zero} · two · two) ≡ 
  normal 94
  ((ƛ
    (ƛ
     (ƛ
      (ƛ ⌊ S (S (S Z)) ⌋ · ⌊ S Z ⌋ · (⌊ S (S Z) ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)))))
   · (ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))
   · (ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))
   ⟶⟨ ξ₁ app β ⟩
   (ƛ
    (ƛ
     (ƛ
      (ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))) · ⌊ S Z ⌋ ·
      (⌊ S (S Z) ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋))))
   · (ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))
   ⟶⟨ β ⟩
   ƛ
   (ƛ
    (ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))) · ⌊ S Z ⌋ ·
    ((ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))) · ⌊ S Z ⌋ · ⌊ Z ⌋))
   ⟶⟨ ζ (ζ (ξ₁ app β)) ⟩
   ƛ
   (ƛ
    (ƛ ⌊ S (S Z) ⌋ · (⌊ S (S Z) ⌋ · ⌊ Z ⌋)) ·
    ((ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))) · ⌊ S Z ⌋ · ⌊ Z ⌋))
   ⟶⟨ ζ (ζ β) ⟩
   ƛ
   (ƛ
    ⌊ S Z ⌋ ·
    (⌊ S Z ⌋ ·
     ((ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))) · ⌊ S Z ⌋ · ⌊ Z ⌋)))
   ⟶⟨ ζ (ζ (ξ₂ ⌊ S Z ⌋ (ξ₂ ⌊ S Z ⌋ (ξ₁ app β)))) ⟩
   ƛ
   (ƛ
    ⌊ S Z ⌋ ·
    (⌊ S Z ⌋ · ((ƛ ⌊ S (S Z) ⌋ · (⌊ S (S Z) ⌋ · ⌊ Z ⌋)) · ⌊ Z ⌋)))
   ⟶⟨ ζ (ζ (ξ₂ ⌊ S Z ⌋ (ξ₂ ⌊ S Z ⌋ β))) ⟩
   ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))) ∎)
  (ƛ
   (ƛ
    ⌈ ⌊ S Z ⌋ · ⌈ ⌊ S Z ⌋ · ⌈ ⌊ S Z ⌋ · ⌈ ⌊ S Z ⌋ · ⌈ ⌊ Z ⌋ ⌉ ⌉ ⌉ ⌉ ⌉))
_ = refl
\end{code}
