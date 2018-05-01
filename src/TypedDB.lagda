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
infix  4 μ_

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

  `caseℕ : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      -----------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ----------
    → Γ ⊢ A
\end{code}

Should modify the above to ensure that body of μ is a function.

## Test examples

\begin{code}
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc (`suc `zero)

four : ∀ {Γ} → Γ ⊢ `ℕ
four = `suc (`suc (`suc (`suc `zero)))

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ `caseℕ ⌊ S Z ⌋ ⌊ Z ⌋ (`suc (⌊ S S S Z ⌋ · ⌊ Z ⌋ · ⌊ S Z ⌋))

Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

plusCh : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusCh = ƛ ƛ ƛ ƛ ⌊ S S S Z ⌋ · ⌊ S Z ⌋ · (⌊ S S Z ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)

twoCh : ∀ {Γ A} → Γ ⊢ Ch A
twoCh = ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)

fourCh : ∀ {Γ A} → Γ ⊢ Ch A
fourCh = ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))

fourCh′ : ∀ {Γ A} → Γ ⊢ Ch A
fourCh′ = plusCh · twoCh · twoCh

inc : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
inc = ƛ `suc ⌊ Z ⌋

fromCh : ε ⊢ Ch `ℕ ⇒ `ℕ
fromCh = ƛ ⌊ Z ⌋ · inc · `zero
\end{code}

## Operational semantics

Simultaneous substitution, a la McBride

## Renaming

\begin{code}
ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
ext σ Z      =  Z
ext σ (S x)  =  S (σ x)

rename : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A) → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename σ (⌊ n ⌋)         =  ⌊ σ n ⌋
rename σ (ƛ N)           =  ƛ (rename (ext σ) N)
rename σ (L · M)         =  (rename σ L) · (rename σ M)
rename σ (`zero)         =  `zero
rename σ (`suc M)        =  `suc (rename σ M)
rename σ (`caseℕ L M N)  =  `caseℕ (rename σ L) (rename σ M) (rename (ext σ) N)
rename σ (μ N)           =  μ (rename (ext σ) N)
\end{code}

## Substitution

\begin{code}
exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
exts ρ Z      =  ⌊ Z ⌋
exts ρ (S x)  =  rename S_ (ρ x)

subst : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ⊢ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
subst ρ (⌊ k ⌋)         =  ρ k
subst ρ (ƛ N)           =  ƛ (subst (exts ρ) N)
subst ρ (L · M)         =  (subst ρ L) · (subst ρ M)
subst ρ (`zero)         =  `zero
subst ρ (`suc M)        =  `suc (subst ρ M)
subst ρ (`caseℕ L M N)  =  `caseℕ (subst ρ L) (subst ρ M) (subst (exts ρ) N)
subst ρ (μ N)           =  μ (subst (exts ρ) N)

_[_] : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A → Γ ⊢ B
_[_] {Γ} {A} N M =  subst {Γ , A} {Γ} ρ N
  where
  ρ : ∀ {B} → Γ , A ∋ B → Γ ⊢ B
  ρ Z      =  M
  ρ (S x)  =  ⌊ x ⌋
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

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ⟶ L′
      -----------------
    → L · M ⟶ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M ⟶ M′
      -----------------
    → V · M ⟶ V · M′

  β-⇒ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      ---------------------
    → (ƛ N) · W ⟶ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M ⟶ M′
      -------------------
    → `suc M ⟶ `suc M′

  ξ-caseℕ : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L ⟶ L′
      -------------------------------
    → `caseℕ L M N ⟶ `caseℕ L′ M N

  β-ℕ₁ :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -----------------------
    → `caseℕ `zero M N ⟶ M

  β-ℕ₂ : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      --------------------------------
    → `caseℕ (`suc V) M N ⟶ N [ V ]

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ------------------
    → μ N ⟶ N [ μ N ]
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

_ : plus {ε} · two · two ⟶* four
_ =
    plus · two · two
  ⟶⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ ƛ `caseℕ ⌊ S Z ⌋ ⌊ Z ⌋ (`suc (plus · ⌊ Z ⌋ · ⌊ S Z ⌋))) · two · two
  ⟶⟨ ξ-·₁ (β-⇒ (Suc (Suc Zero))) ⟩
    (ƛ `caseℕ two ⌊ Z ⌋ (`suc (plus · ⌊ Z ⌋ · ⌊ S Z ⌋))) · two
  ⟶⟨ β-⇒ (Suc (Suc Zero)) ⟩
    `caseℕ two two (`suc (plus · ⌊ Z ⌋ · two))
  ⟶⟨ β-ℕ₂ (Suc Zero) ⟩
    `suc (plus · `suc `zero · two)
  ⟶⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ ƛ `caseℕ ⌊ S Z ⌋ ⌊ Z ⌋ (`suc (plus · ⌊ Z ⌋ · ⌊ S Z ⌋)))
      · `suc `zero · two)
  ⟶⟨ ξ-suc (ξ-·₁ (β-⇒ (Suc Zero))) ⟩
    `suc ((ƛ `caseℕ (`suc `zero) ⌊ Z ⌋ (`suc (plus · ⌊ Z ⌋ · ⌊ S Z ⌋))) · two)
  ⟶⟨ ξ-suc (β-⇒ (Suc (Suc Zero))) ⟩
    `suc (`caseℕ (`suc `zero) (two) (`suc (plus · ⌊ Z ⌋ · two)))
  ⟶⟨ ξ-suc (β-ℕ₂ Zero) ⟩
    `suc (`suc (plus · `zero · two))
  ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc (`suc ((ƛ ƛ `caseℕ ⌊ S Z ⌋ ⌊ Z ⌋ (`suc (plus · ⌊ Z ⌋ · ⌊ S Z ⌋)))
      · `zero · two))
  ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (β-⇒ Zero))) ⟩
    `suc (`suc ((ƛ `caseℕ `zero ⌊ Z ⌋ (`suc (plus · ⌊ Z ⌋ · ⌊ S Z ⌋))) · two))
  ⟶⟨ ξ-suc (ξ-suc (β-⇒ (Suc (Suc Zero)))) ⟩
    `suc (`suc (`caseℕ `zero (two) (`suc (plus · ⌊ Z ⌋ · two))))
  ⟶⟨ ξ-suc (ξ-suc β-ℕ₁) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎

_ : fromCh · (plusCh · twoCh · twoCh) ⟶* four
_ =
  begin
    fromCh · (plusCh · twoCh · twoCh)
  ⟶⟨ ξ-·₂ Fun (ξ-·₁ (β-⇒ Fun)) ⟩
    fromCh · ((ƛ ƛ ƛ twoCh · ⌊ S Z ⌋ · (⌊ S (S Z) ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)) · twoCh)
  ⟶⟨ ξ-·₂ Fun (β-⇒ Fun) ⟩
    fromCh · (ƛ ƛ twoCh · ⌊ S Z ⌋ · (twoCh · ⌊ S Z ⌋ · ⌊ Z ⌋))
  ⟶⟨ β-⇒ Fun ⟩
    (ƛ ƛ twoCh · ⌊ S Z ⌋ · (twoCh · ⌊ S Z ⌋ · ⌊ Z ⌋)) · inc · `zero
  ⟶⟨ ξ-·₁ (β-⇒ Fun) ⟩
    (ƛ twoCh · inc · (twoCh · inc · ⌊ Z ⌋)) · `zero
  ⟶⟨ β-⇒ Zero ⟩
    twoCh · inc · (twoCh · inc · `zero)
  ⟶⟨ ξ-·₁ (β-⇒ Fun) ⟩
    (ƛ inc · (inc · ⌊ Z ⌋)) · (twoCh · inc · `zero)
  ⟶⟨ ξ-·₂ Fun (ξ-·₁ (β-⇒ Fun)) ⟩
    (ƛ inc · (inc · ⌊ Z ⌋)) · ((ƛ inc · (inc · ⌊ Z ⌋)) · `zero)
  ⟶⟨ ξ-·₂ Fun (β-⇒ Zero) ⟩
    (ƛ inc · (inc · ⌊ Z ⌋)) · (inc · (inc · `zero))
  ⟶⟨ ξ-·₂ Fun (ξ-·₂ Fun (β-⇒ Zero)) ⟩
    (ƛ inc · (inc · ⌊ Z ⌋)) · (inc · `suc `zero)
  ⟶⟨ ξ-·₂ Fun (β-⇒ (Suc Zero)) ⟩
    (ƛ inc · (inc · ⌊ Z ⌋)) · `suc (`suc `zero)
  ⟶⟨ β-⇒ (Suc (Suc Zero)) ⟩
    inc · (inc · `suc (`suc `zero))
  ⟶⟨ ξ-·₂ Fun (β-⇒ (Suc (Suc Zero))) ⟩
    inc · `suc (`suc (`suc `zero))
  ⟶⟨ β-⇒ (Suc (Suc (Suc Zero))) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎
\end{code}

## Values do not reduce

Values do not reduce.
\begin{code}
Value-lemma : ∀ {Γ A} {M N : Γ ⊢ A} → Value M → ¬ (M ⟶ N)
Value-lemma Fun ()
Value-lemma Zero ()
Value-lemma (Suc VM) (ξ-suc M⟶N)  =  Value-lemma VM M⟶N
\end{code}

As a corollary, terms that reduce are not values.
\begin{code}
⟶-corollary : ∀ {Γ A} {M N : Γ ⊢ A} → (M ⟶ N) → ¬ Value M
⟶-corollary M⟶N VM  =  Value-lemma VM M⟶N
\end{code}


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
progress (ƛ N)                            =  done Fun
progress (L · M) with progress L
...    | step L⟶L′                      =  step (ξ-·₁ L⟶L′)
...    | done Fun with progress M
...        | step M⟶M′                  =  step (ξ-·₂ Fun M⟶M′)
...        | done VM                      =  step (β-⇒ VM)
progress (`zero)                          =  done Zero
progress (`suc M) with progress M
...    | step M⟶M′                      =  step (ξ-suc M⟶M′)
...    | done VM                          =  done (Suc VM)
progress (`caseℕ L M N) with progress L
...    | step L⟶L′                       =  step (ξ-caseℕ L⟶L′)
...    | done Zero                         =  step (β-ℕ₁)
...    | done (Suc VL)                     =  step (β-ℕ₂ VL)
progress (μ N)                             =  step (β-μ)
\end{code}


## Normalise

\begin{code}
Gas : Set
Gas = ℕ

data Normalise {A} (M : ε ⊢ A) : Set where
  normal : ∀ {N : ε ⊢ A}
    → Gas
    → M ⟶* N
      ------------
    → Normalise M

normalise : ∀ {A} → ℕ → (L : ε ⊢ A) → Normalise L
normalise zero    L                         =  normal zero (L ∎)
normalise (suc g) L with progress L
...    | done VL                            =  normal (suc zero) (L ∎)
...    | step {M} L⟶M with normalise g M
...        | normal h M⟶*N                =  normal (suc h) (L ⟶⟨ L⟶M ⟩ M⟶*N)
\end{code}


