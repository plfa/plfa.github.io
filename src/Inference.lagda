---
title     : "Inference: Bidirectional type inference"
layout    : page
permalink : /Inference
---

Given Raw terms and inherently typed terms, specify
an algorithm going from one to the other.

There are *many* ways to do this. Which is best?

First dimension: staged/direct

* Staged: Raw -> Scoped, Scoped -> Typed
* Direct: Raw -> Typed in one fell swoop

Second dimension: derivation/function

* Derviation: Type derivations similar to usual rules, erasure of typing to Typed
* Function: Function to compute Typed term directly

Let's fiddle about with a couple of these to see which is best.

The Agda manual gives a solution for Staged/Function (second half of staged).

  I'm quite keen to try Direct/Derivation.


## Imports

\begin{code}
module Inference where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; foldr; filter; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.String using (String; _≟_; _++_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)
import Collections

pattern [_]       w        =  w ∷ []
pattern [_,_]     w x      =  w ∷ x ∷ []
pattern [_,_,_]   w x y    =  w ∷ x ∷ y ∷ []
pattern [_,_,_,_] w x y z  =  w ∷ x ∷ y ∷ z ∷ []
\end{code}


## Identifiers

\begin{code}
Id : Set
Id = String
\end{code}

### Lists of identifiers

\begin{code}
open Collections (Id) (_≟_)
\end{code}

## First development: Raw

\begin{code}
module Raw where
\end{code}

### Syntax

\begin{code}
  infix   4  _∋_`:_
  infix   4  _⊢_↑_
  infix   4  _⊢_↓_
  infixl  5  _,_`:_
  infix   5  _`:_
  infixr  6  _`→_
  infix   6  `λ_`→_
  infix   6  `μ_`→_
  infixl  9  _·_

  data Type : Set where
    `ℕ   : Type
    _`→_ : Type → Type → Type

  data Ctx : Set where
    ε      : Ctx
    _,_`:_ : Ctx → Id → Type → Ctx

  data Term : Set where
    ⌊_⌋                        : Id → Term
    `λ_`→_                     : Id → Term → Term
    _·_                        : Term → Term → Term
    `zero                      : Term
    `suc                       : Term → Term   
    `case_[`zero`→_|`suc_`→_]  : Term → Term → Id → Term → Term
    `μ_`→_                     : Id → Term → Term
    _`:_                       : Term → Type → Term

\end{code}

### Example terms

\begin{code}
  Ch : Type
  Ch = (`ℕ `→ `ℕ) `→ `ℕ `→ `ℕ

  two : Term
  two = (`λ "s" `→ `λ "z" `→ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)) `: Ch

  plus : Term
  plus = (`λ "m" `→ `λ "n" `→ `λ "s" `→ `λ "z" `→
           ⌊ "m" ⌋ · ⌊ "s" ⌋ · (⌊ "n" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋))
         `: Ch `→ Ch `→ Ch

  norm : Term
  norm = (`λ "m" `→ ⌊ "m" ⌋ · (`λ "x" `→ `suc ⌊ "x" ⌋) · `zero)
         `: Ch `→ `ℕ

  four : Term
  four = norm · (plus · two · two)
\end{code}

### Bidirectional type checking

\begin{code}
  data _∋_`:_ : Ctx → Id → Type → Set where

    Z : ∀ {Γ x A}
        --------------------
      → Γ , x `: A ∋ x `: A

    S : ∀ {Γ w x A B}
      → w ≢ x
      → Γ ∋ w `: B
        --------------------
      → Γ , x `: A ∋ w `: B

  data _⊢_↑_ : Ctx → Term → Type → Set
  data _⊢_↓_ : Ctx → Term → Type → Set

  data _⊢_↑_ where

    Ax : ∀ {Γ A x}
      → Γ ∋ x `: A
        --------------
      → Γ ⊢ ⌊ x ⌋ ↑ A

    _·_ : ∀ {Γ L M A B}
      → Γ ⊢ L ↑ A `→ B
      → Γ ⊢ M ↑ A
        ---------------
      → Γ ⊢ L · M ↑ B

    ↑↓ : ∀ {Γ M A}
      → Γ ⊢ M ↓ A
        ----------------
      → Γ ⊢ M `: A ↑ A

  data _⊢_↓_ where

    ⊢λ : ∀ {Γ x N A B}
      → Γ , x `: A ⊢ N ↓ B
        -----------------------
      → Γ ⊢ `λ x `→ N ↓ A `→ B

    ⊢zero : ∀ {Γ}
        ---------------
      → Γ ⊢ `zero ↓ `ℕ

    ⊢suc : ∀ {Γ M}
      → Γ ⊢ M ↓ `ℕ
        ----------------
      → Γ ⊢ `suc M ↓ `ℕ

    ⊢case : ∀ {Γ L M x N A}
      → Γ ⊢ L ↑ `ℕ
      → Γ ⊢ M ↓ A
      → Γ , x `: A ⊢ N ↓ A
        ------------------------------------------
      → Γ ⊢ `case L [`zero`→ M |`suc x `→ N ] ↓ A

    ⊢μ : ∀ {Γ x N A}
      → Γ , x `: A ⊢ N ↓ A
        -----------------------
      → Γ ⊢ `μ x `→ N ↓ A `→ A

    ↓↑ : ∀ {Γ M A}
      → Γ ⊢ M ↑ A
        ----------
      → Γ ⊢ M ↓ A
\end{code}

## Type checking monad

\begin{code}
  Error : Set
  Error = String

  TC : Set → Set
  TC A = Error ⊎ A

  error : ∀ {A : Set} → Error → TC A
  error = inj₁

  return : ∀ {A : Set} → A → TC A
  return = inj₂

  _>>=_ : ∀ {A B : Set} → TC A → (A → TC B) → TC B
  inj₁ e >>= k  =  inj₁ e
  inj₂ x >>= k  =  k x
\end{code}

## Type inferencer

\begin{code}
  _≟Tp_ : (A B : Type) → Dec (A ≡ B)
  A ≟Tp B = {!!}

  show : Type → String
  show A = {!!}

  data Lookup (Γ : Ctx) (x : Id) : Set where
    ok : ∀ (A : Type) → (Γ ∋ x `: A) → Lookup Γ x
  
  lookup : ∀ (Γ : Ctx) (x : Id) → TC (Lookup Γ x)
  lookup ε x  =
    error ("variable " ++ x ++ " not bound")
  lookup (Γ , x `: A) w with w ≟ x
  ... | yes refl =
    return (ok A Z)
  ... | no w≢ =
    do ok A ⊢x ← lookup Γ w
       return (ok A (S w≢ ⊢x))
    
  data Synth (Γ : Ctx) (M : Term) : Set where
    ok : ∀ (A : Type) → (Γ ⊢ M ↑ A) → Synth Γ M
  
  synth : ∀ (Γ : Ctx) (M : Term) → TC (Synth Γ M)
  inher : ∀ (Γ : Ctx) (M : Term) (A : Type) → TC (Γ ⊢ M ↓ A)

  synth Γ ⌊ x ⌋ =
    do ok A ⊢x ← lookup Γ x
       return (ok A (Ax ⊢x))
  synth Γ (L · M) =
    do ok (A₀ `→ B) ⊢L ← synth Γ L
         where _ → error "application of non-function"
       ok A₁        ⊢M ← synth Γ M
       yes refl        ← return (A₀ ≟Tp A₁)
         where no _ → error "types differ in application"
       return (ok B (⊢L · ⊢M))
  synth Γ (M `: A) =
    do ⊢M ← inher Γ M A
       return (ok A (↑↓ ⊢M))
  synth Γ M =
    error "untypable term"

  inher Γ M A = {!!}

\end{code}

