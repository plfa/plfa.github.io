---
title     : "Untyped: Normal forms for untyped lambda calculus"
layout    : page
permalink : /Untyped
---

This is still the typed code for full normalisation,
and needs to be updated.

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
infixl 6 _,_
infix  4 _⊢_
infix  4 _∋_
infixr 5 _⇒_
infixl 5 _·_
infix  6 S_
infix  4 ƛ_

data Type : Set where
  o   : Type
  _⇒_ : Type → Type → Type

data Env : Set where
  ε   : Env
  _,_ : Env → Type → Env

data _∋_ : Env → Type → Set where

  Z : ∀ {Γ} {A} →
    ------------
    Γ , A ∋ A

  S_ : ∀ {Γ} {A B} →
    Γ ∋ B →
    -----------
    Γ , A ∋ B

data _⊢_ : Env → Type → Set where

  ⌊_⌋ : ∀ {Γ} {A} →
    Γ ∋ A →
    -------
    Γ ⊢ A

  ƛ_  :  ∀ {Γ} {A B} →
    Γ , A ⊢ B →
    ------------
    Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ} {A B} →
    Γ ⊢ A ⇒ B →
    Γ ⊢ A →
    ------------
    Γ ⊢ B
\end{code}

## Test examples

\begin{code}
Ch : Type
Ch = (o ⇒ o) ⇒ o ⇒ o

plus : ∀ {Γ} → Γ ⊢ Ch ⇒ Ch ⇒ Ch
plus = ƛ ƛ ƛ ƛ ⌊ S S S Z ⌋ · ⌊ S Z ⌋ · (⌊ S S Z ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)

two : ∀ {Γ} → Γ ⊢ Ch
two = ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)

four : ∀ {Γ} → Γ ⊢ Ch
four = ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))

four′ : ∀ {Γ} → Γ ⊢ Ch
four′ = plus · two · two
\end{code}

# Denotational semantics

\begin{code}
⟦_⟧ᵀ : Type → Set
⟦ o ⟧ᵀ      =  ℕ
⟦ A ⇒ B ⟧ᵀ  =  ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ

⟦_⟧ᴱ : Env → Set
⟦ ε ⟧ᴱ      =  ⊤
⟦ Γ , A ⟧ᴱ  =  ⟦ Γ ⟧ᴱ × ⟦ A ⟧ᵀ

⟦_⟧ⱽ : ∀ {Γ : Env} {A : Type} → Γ ∋ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ Z ⟧ⱽ   ⟨ ρ , v ⟩ = v
⟦ S n ⟧ⱽ ⟨ ρ , v ⟩ = ⟦ n ⟧ⱽ ρ

⟦_⟧ : ∀ {Γ : Env} {A : Type} → Γ ⊢ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ ⌊ n ⌋ ⟧ ρ  =  ⟦ n ⟧ⱽ ρ
⟦ ƛ N   ⟧ ρ  =  λ{ v → ⟦ N ⟧ ⟨ ρ , v ⟩ }
⟦ L · M ⟧ ρ  =  (⟦ L ⟧ ρ) (⟦ M ⟧ ρ)

_ : ⟦ four ⟧ tt ≡ ⟦ four′ ⟧ tt
_ = refl

_ : ⟦ four ⟧ tt suc zero ≡ 4
_ = refl
\end{code}

## Operational semantics - with simultaneous substitution, a la McBride

## Renaming

\begin{code}
rename : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ∋ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
rename ρ (⌊ n ⌋)                   =  ⌊ ρ n ⌋
rename {Γ} {Δ} ρ (ƛ_ {A = A} N)    =  ƛ (rename {Γ , A} {Δ , A} ρ′ N)
  where
  ρ′ : ∀ {C} → Γ , A ∋ C → Δ , A ∋ C
  ρ′ Z      =  Z
  ρ′ (S k)  =  S (ρ k)
rename ρ (L · M)                   =  (rename ρ L) · (rename ρ M)
\end{code}

## Substitution

\begin{code}
subst : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ⊢ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
subst ρ (⌊ k ⌋)                   =  ρ k
subst {Γ} {Δ} ρ (ƛ_ {A = A} N)    =  ƛ (subst {Γ , A} {Δ , A} ρ′ N)
  where
  ρ′ : ∀ {C} → Γ , A ∋ C → Δ , A ⊢ C
  ρ′ Z      =  ⌊ Z ⌋
  ρ′ (S k)  =  rename {Δ} {Δ , A} S_ (ρ k)
subst ρ (L · M)                   =  (subst ρ L) · (subst ρ M)

substitute : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A → Γ ⊢ B
substitute {Γ} {A} N M =  subst {Γ , A} {Γ} ρ N
  where
  ρ : ∀ {C} → Γ , A ∋ C → Γ ⊢ C
  ρ Z      =  M
  ρ (S k)  =  ⌊ k ⌋
\end{code}

## Normal

\begin{code}
data Normal  : ∀ {Γ} {A} → Γ ⊢ A → Set
data Neutral : ∀ {Γ} {A} → Γ ⊢ A → Set

data Normal where
  ƛ_  : ∀ {Γ} {A B} {N : Γ , A ⊢ B} → Normal N → Normal (ƛ N)
  ⌈_⌉ : ∀ {Γ} {A} {M : Γ ⊢ A} → Neutral M → Normal M

data Neutral where
  ⌊_⌋   : ∀ {Γ} {A} → (n : Γ ∋ A) → Neutral ⌊ n ⌋
  _·_  : ∀ {Γ} {A B} → {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} → Neutral L → Normal M → Neutral (L · M)
\end{code}

## Reduction step

\begin{code}
infix 2 _⟶_

data _⟶_ : ∀ {Γ} {A} → Γ ⊢ A → Γ ⊢ A → Set where

  ξ₁ : ∀ {Γ} {A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} →
    L ⟶ L′ →
    -----------------
    L · M ⟶ L′ · M

  ξ₂ : ∀ {Γ} {A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A} →
    Normal V →
    M ⟶ M′ →
    ----------------
    V · M ⟶ V · M′

  ζ : ∀ {Γ} {A B} {N N′ : Γ , A ⊢ B} →
    N ⟶ N′ →
    ------------
    ƛ N ⟶ ƛ N′

  β : ∀ {Γ} {A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A} → 
    Normal W →
    ----------------------------
    (ƛ N) · W ⟶ substitute N W
\end{code}

## Reflexive and transitive closure

\begin{code}
infix  2 _⟶*_
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3 _∎

data _⟶*_ : ∀ {Γ} {A} → Γ ⊢ A → Γ ⊢ A → Set where

  _∎ : ∀ {Γ} {A} (M : Γ ⊢ A) →
    -------------
    M ⟶* M

  _⟶⟨_⟩_ : ∀ {Γ} {A} (L : Γ ⊢ A) {M N : Γ ⊢ A} →
    L ⟶ M →
    M ⟶* N →
    ---------
    L ⟶* N

begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A} → (M ⟶* N) → (M ⟶* N)
begin M⟶*N = M⟶*N
\end{code}


## Example reduction sequences

\begin{code}
id : ∀ (A : Type) → ε ⊢ A ⇒ A
id A = ƛ ⌊ Z ⌋

_ : id (o ⇒ o) · id o  ⟶* id o
_ =
  begin
    (ƛ ⌊ Z ⌋) · (ƛ ⌊ Z ⌋)
  ⟶⟨ β (ƛ ⌈ ⌊ Z ⌋ ⌉) ⟩
    ƛ ⌊ Z ⌋
  ∎


_ : four′ {ε} ⟶* four {ε}
_ =
  begin
    plus · two · two
  ⟶⟨ ξ₁ (β (ƛ (ƛ ⌈ ⌊ S Z ⌋ · ⌈ ⌊ S Z ⌋ · ⌈ ⌊ Z ⌋ ⌉ ⌉ ⌉))) ⟩
    (ƛ ƛ ƛ two · ⌊ S Z ⌋ · (⌊ S (S Z) ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)) · two
  ⟶⟨ ξ₁ (ζ (ζ (ζ (ξ₁ (β ⌈ ⌊ S Z ⌋ ⌉))))) ⟩
    (ƛ ƛ ƛ (ƛ ⌊ S (S Z) ⌋ · (⌊ S (S Z) ⌋ · ⌊ Z ⌋)) · (⌊ S (S Z) ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)) · two
  ⟶⟨ ξ₁ (ζ (ζ (ζ (β ⌈ (⌊ S (S Z) ⌋ · ⌈ ⌊ S Z ⌋ ⌉) · ⌈ ⌊ Z ⌋ ⌉ ⌉)))) ⟩
    (ƛ ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S (S Z) ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋))) · two
  ⟶⟨ β (ƛ (ƛ ⌈ ⌊ S Z ⌋ · ⌈ ⌊ S Z ⌋ · ⌈ ⌊ Z ⌋ ⌉ ⌉ ⌉)) ⟩
    ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ((ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))) · ⌊ S Z ⌋ · ⌊ Z ⌋))
  ⟶⟨ ζ (ζ (ξ₂ ⌈ ⌊ S Z ⌋ ⌉ (ξ₂ ⌈ ⌊ S Z ⌋ ⌉ (ξ₁ (β ⌈ ⌊ S Z ⌋ ⌉))))) ⟩
    ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ((ƛ ⌊ S (S Z) ⌋ · (⌊ S (S Z) ⌋ · ⌊ Z ⌋)) · ⌊ Z ⌋))
  ⟶⟨ ζ (ζ (ξ₂ ⌈ ⌊ S Z ⌋ ⌉ (ξ₂ ⌈ ⌊ S Z ⌋ ⌉ (β ⌈ ⌊ Z ⌋ ⌉)))) ⟩
    ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))
  ∎
\end{code}


## Progress

\begin{code}
data Progress {Γ A} (M : Γ ⊢ A) : Set where
  step : ∀ (N : Γ ⊢ A) → M ⟶ N → Progress M
  done : Normal M → Progress M

progress : ∀ {Γ} {A} → (M : Γ ⊢ A) → Progress M
progress ⌊ x ⌋                                                  =  done ⌈ ⌊ x ⌋ ⌉
progress (ƛ N)       with progress N
progress (ƛ N)          | step N′ r                             =  step (ƛ N′) (ζ r)
progress (ƛ V)          | done NmV                              =  done (ƛ NmV)
progress (L · M)     with progress L
progress (L · M)        | step L′ r                             =  step (L′ · M) (ξ₁ r)
progress (V · M)        | done NmV     with progress M
progress (V · M)        | done NmV        | step M′ r           =  step (V · M′) (ξ₂ NmV r)
progress (V · W)        | done ⌈ NeV ⌉    | done NmW            =  done ⌈ NeV · NmW ⌉
progress ((ƛ V) · W)    | done (ƛ NmV)    | done NmW            =  step (substitute V W) (β NmW)
\end{code}


## Normalise

\begin{code}
data Normalise {Γ A} (M : Γ ⊢ A) : Set where
  out-of-gas : Normalise M
  normal : ∀ (N : Γ ⊢ A) → Normal N → M ⟶* N → Normalise M

normalise : ∀ {Γ} {A} → ℕ → (M : Γ ⊢ A) → Normalise M
normalise zero    L                                                =  out-of-gas
normalise (suc n) L with progress L
...                    | done NmL                                  =  normal L NmL (L ∎)
...                    | step M L⟶M with normalise n M
...                                      | out-of-gas              =  out-of-gas
...                                      | normal N NmN M⟶*N     =  normal N NmN (L ⟶⟨ L⟶M ⟩ M⟶*N)
\end{code}


