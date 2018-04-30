---
title     : "TypedDB: Typed DeBruijn representation"
layout    : page
permalink : /TypedDB
---

## Imports

\begin{code}
module TypedDB where
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
  `ℕ  : Type
  _⇒_ : Type → Type → Type

data Env : Set where
  ε   : Env
  _,_ : Env → Type → Env

data _∋_ : Env → Type → Set where

  Z : ∀ {Γ} {A}
      ----------
    → Γ , A ∋ A

  S_ : ∀ {Γ} {A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B

data _⊢_ : Env → Type → Set where

  ⌊_⌋ : ∀ {Γ} {A}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ_  :  ∀ {Γ} {A B}
    → Γ , A ⊢ B
      ----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ} {A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ----------
    → Γ ⊢ B

  `zero : ∀ {Γ}
      ----------
    → Γ ⊢ `ℕ

  `suc : ∀ {Γ}
    → Γ ⊢ `ℕ
      -------
    → Γ ⊢ `ℕ
\end{code}

## Test examples

\begin{code}
Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

plus : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plus = ƛ ƛ ƛ ƛ ⌊ S S S Z ⌋ · ⌊ S Z ⌋ · (⌊ S S Z ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)

two : ∀ {Γ A} → Γ ⊢ Ch A
two = ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)

four : ∀ {Γ A} → Γ ⊢ Ch A
four = ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))

four′ : ∀ {Γ A} → Γ ⊢ Ch A
four′ = plus · two · two

fromCh : ε ⊢ Ch `ℕ ⇒ `ℕ
fromCh = ƛ ⌊ Z ⌋ · (ƛ `suc ⌊ Z ⌋) · `zero
\end{code}

# Denotational semantics

\begin{code}
⟦_⟧ᵀ : Type → Set
⟦ `ℕ ⟧ᵀ     =  ℕ
⟦ A ⇒ B ⟧ᵀ  =  ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ

⟦_⟧ᴱ : Env → Set
⟦ ε ⟧ᴱ      =  ⊤
⟦ Γ , A ⟧ᴱ  =  ⟦ Γ ⟧ᴱ × ⟦ A ⟧ᵀ

⟦_⟧ⱽ : ∀ {Γ : Env} {A : Type} → Γ ∋ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ Z ⟧ⱽ   ⟨ ρ , v ⟩ = v
⟦ S n ⟧ⱽ ⟨ ρ , v ⟩ = ⟦ n ⟧ⱽ ρ

⟦_⟧ : ∀ {Γ : Env} {A : Type} → Γ ⊢ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ ⌊ n ⌋  ⟧ ρ  =  ⟦ n ⟧ⱽ ρ
⟦ ƛ N    ⟧ ρ  =  λ{ v → ⟦ N ⟧ ⟨ ρ , v ⟩ }
⟦ L · M  ⟧ ρ  =  (⟦ L ⟧ ρ) (⟦ M ⟧ ρ)
⟦ `zero  ⟧ ρ  =  zero
⟦ `suc M ⟧ ρ  =  suc (⟦ M ⟧ ρ)

_ : ⟦ four {ε} {`ℕ} ⟧ tt ≡ ⟦ four′ {ε} {`ℕ} ⟧ tt
_ = refl

_ : ⟦ fromCh · four ⟧ tt ≡ 4
_ = refl
\end{code}

## Operational semantics - with simultaneous substitution, a la McBride

## Renaming

\begin{code}
rename : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ∋ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
rename σ (⌊ n ⌋)                   =  ⌊ σ n ⌋
rename {Γ} {Δ} σ (ƛ_ {A = A} N)    =  ƛ (rename {Γ , A} {Δ , A} σ′ N)
  where
  σ′ : ∀ {C} → Γ , A ∋ C → Δ , A ∋ C
  σ′ Z      =  Z
  σ′ (S k)  =  S (σ k)
rename σ (L · M)                   =  (rename σ L) · (rename σ M)
rename σ (`zero)                   =  `zero
rename σ (`suc M)                  =  `suc (rename σ M)
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
subst ρ (`zero)                   =  `zero
subst ρ (`suc M)                  =  `suc (subst ρ M)

_[_] : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A → Γ ⊢ B
_[_] {Γ} {A} N M =  subst {Γ , A} {Γ} ρ N
  where
  ρ : ∀ {C} → Γ , A ∋ C → Γ ⊢ C
  ρ Z      =  M
  ρ (S k)  =  ⌊ k ⌋
\end{code}

## Value

\begin{code}
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  Zero : ∀ {Γ} → 
      -----------------
      Value (`zero {Γ})

  Suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)
      
  Fun : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)
\end{code}

Here `` `zero `` requires an implicit parameter to aid inference
(much in the same way that `[]` did in [Lists](Lists)).

## Reduction step

\begin{code}
infix 2 _⟶_

data _⟶_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-⇒₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ⟶ L′
      -----------------
    → L · M ⟶ L′ · M

  ξ-⇒₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M ⟶ M′
      ----------------
    → V · M ⟶ V · M′

  β-⇒ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      ---------------------
    → (ƛ N) · W ⟶ N [ W ]

  ξ-ℕ : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M ⟶ M′
      ------------------
    → `suc M ⟶ `suc M′
\end{code}

## Reflexive and transitive closure

\begin{code}
infix  2 _⟶*_
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3 _∎

data _⟶*_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M ⟶* M

  _⟶⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ⟶ M
    → M ⟶* N
      ---------
    → L ⟶* N

begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A} → (M ⟶* N) → (M ⟶* N)
begin M⟶*N = M⟶*N
\end{code}


## Example reduction sequences

\begin{code}
id : ∀ (A : Type) → ε ⊢ A ⇒ A
id A = ƛ ⌊ Z ⌋

_ : ∀ {A} → id (A ⇒ A) · id A  ⟶* id A
_ =
  begin
    (ƛ ⌊ Z ⌋) · (ƛ ⌊ Z ⌋)
  ⟶⟨ β-⇒ Fun ⟩
    ƛ ⌊ Z ⌋
  ∎

{-

_ : four′ {ε} {`ℕ} ⟶* four {ε} {`ℕ}
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
-}
\end{code}


## Canonical forms

(No longer needed)

data Canonical : Term → Type → Set where

  Zero : 
      ------------------
      Canonical `zero `ℕ

  Suc : ∀ {V}
    → Canonical V `ℕ
      ---------------------
    → Canonical (`suc V) `ℕ
 
  Fun : ∀ {x N A B}
    → (N : ε , A ⊢ B)
      ------------------------
    → Canonical (ƛ N) (A ⇒ B)





## Progress

\begin{code}
data Progress {A} (M : ε ⊢ A) : Set where
  step : ∀ {N : ε ⊢ A}
    → M ⟶ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A} → (M : ε ⊢ A) → Progress M
progress ⌊ () ⌋
progress (ƛ N)                       =  done Fun
progress (L · M) with progress L
...    | step L⟶L′                 =  step (ξ-⇒₁ L⟶L′)
...    | done Fun with progress M
...        | step M⟶M′             =  step (ξ-⇒₂ Fun M⟶M′)
...        | done VM                 =  step (β-⇒ VM)
progress (`zero)                     =  done Zero
progress (`suc M) with progress M
...    | step M⟶M′                 =  step (ξ-ℕ M⟶M′)
...    | done VM                     =  done (Suc VM)
\end{code}


## Normalise

\begin{code}
{-
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
-}
\end{code}


