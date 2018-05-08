---
title     : "Raw: Raw, Scoped, Typed"
layout    : page
permalink : /Raw
---

This version uses raw terms.

The substitution algorithm is based on one by McBride.

## Imports

\begin{code}
module Raw where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; foldr; filter; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.String as String
open import Data.String using (String)
-- open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
-- open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)
import Collections

pattern [_]       w        =  w ∷ []
pattern [_,_]     w x      =  w ∷ x ∷ []
pattern [_,_,_]   w x y    =  w ∷ x ∷ y ∷ []
pattern [_,_,_,_] w x y z  =  w ∷ x ∷ y ∷ z ∷ []
\end{code}

## First development: Raw

\begin{code}
module Raw where
\end{code}

### Syntax

\begin{code}
  infix   6  `λ_`→_
  infixl  9  _·_

  Id : Set
  Id = String

  data Type : Set where
    `ℕ   : Type
    _`→_ : Type → Type → Type

  data Env : Set where
    ε      : Env
    _,_`:_ : Env → Id → Type → Env

  data Term : Set where
    ⌊_⌋              : Id → Term
    `λ_`→_          : Id → Term → Term
    _·_             : Term → Term → Term
    `zero           : Term
    `suc            : Term → Term
\end{code}

### Example terms

\begin{code}
  two : Term
  two = `λ "s" `→ `λ "z" `→ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)

  plus : Term
  plus = `λ "m" `→ `λ "n" `→ `λ "s" `→ `λ "z" `→
           ⌊ "m" ⌋ · ⌊ "s" ⌋ · (⌊ "n" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋)

  norm : Term
  norm = `λ "m" `→ ⌊ "m" ⌋ · (`λ "x" `→ `suc ⌊ "x" ⌋) · `zero
\end{code}

### Lists of identifiers

\begin{code}
  _≟_ : ∀ (x : Id) (y : Id) → Dec (x ≡ y)
  _≟_ = String._≟_

  open Collections.CollectionDec (Id) (_≟_)
\end{code}

### Free variables

\begin{code}
  free : Term → List Id
  free (⌊ x ⌋)                 =  [ x ]
  free (`λ x `→ N)             =  free N \\ x
  free (L · M)                 =  free L ++ free M
  free (`zero)                 =  []
  free (`suc M)                =  free M
\end{code}

### Identifier maps

\begin{code}
  ∅ : Id → Term
  ∅ x = ⌊ x ⌋

  infixl 5 _,_↦_

  _,_↦_ : (Id → Term) → Id → Term → (Id → Term)
  (ρ , x ↦ M) w with w ≟ x
  ...               | yes _   =  M
  ...               | no  _   =  ρ w
\end{code}

### Fresh variables

\begin{code}
  fresh : List Id → Id → Id
  fresh xs₀ y = helper xs₀ (length xs₀) y
    where

    prime : Id → Id
    prime x = x String.++ "′"

    helper : List Id → ℕ → Id → Id
    helper []       _       w                =  w
    helper (x ∷ xs) n       w with w ≟ x
    helper (x ∷ xs) n       w    | no  _     =  helper xs n w
    helper (x ∷ xs) (suc n) w    | yes refl  =  helper xs₀ n (prime w)
    helper (x ∷ xs) zero    w    | yes refl  =  ⊥-elim impossible
      where postulate impossible : ⊥

\end{code}

### Substitution

\begin{code}
  subst : List Id → (Id → Term) → Term → Term
  subst ys ρ ⌊ x ⌋        =  ρ x
  subst ys ρ (`λ x `→ N)  =  `λ y `→ subst (y ∷ ys) (ρ , x ↦ ⌊ y ⌋) N
    where
    y = fresh ys x
  subst ys ρ (L · M)      =  subst ys ρ L · subst ys ρ M
  subst ys ρ (`zero)      =  `zero
  subst ys ρ (`suc M)     =  `suc (subst ys ρ M)
                       
  _[_:=_] : Term → Id → Term → Term
  N [ x := M ]  =  subst (free M ++ (free N \\ x))  (∅ , x ↦ M) N
\end{code}

### Testing substitution

\begin{code}
  _ : fresh [ "y" ] "y" ≡ "y′"
  _ = refl

  _ : fresh [ "z" ] "y" ≡ "y"
  _ = refl

  _ : (⌊ "s" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋) [ "z" := `zero ] ≡ (⌊ "s" ⌋ · ⌊ "s" ⌋ · `zero)
  _ = refl

  _ : (`λ "y" `→ ⌊ "x" ⌋) [ "x" := ⌊ "z" ⌋ ] ≡ (`λ "y" `→ ⌊ "z" ⌋)
  _ = refl

  _ : (`λ "y" `→ ⌊ "x" ⌋) [ "x" := ⌊ "y" ⌋ ] ≡ (`λ "y′" `→ ⌊ "y" ⌋)
  _ = refl

  _ : (⌊ "s" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋) [ "s" := (`λ "m" `→ `suc ⌊ "m" ⌋) ]
                                   [ "z" := `zero ] 
        ≡ (`λ "m" `→ `suc ⌊ "m" ⌋) · (`λ "m" `→ `suc ⌊ "m" ⌋) · `zero
  _ = refl

  _ : subst [] (∅ , "m" ↦ two , "n" ↦ `zero) (⌊ "m" ⌋ · ⌊ "n" ⌋)  ≡ (two · `zero)
  _ = refl
\end{code}

### Values

\begin{code}
  data Value : Term → Set where

    Zero :
        ----------
        Value `zero

    Suc : ∀ {V}
      → Value V
        --------------
      → Value (`suc V)
        
    Fun : ∀ {x N}
        -----------------
      → Value (`λ x `→ N)
\end{code}

### Reduction

\begin{code}
  infix 4 _⟶_

  data _⟶_ : Term → Term → Set where

    ξ-·₁ : ∀ {L L′ M}
      → L ⟶ L′
        ----------------
      → L · M ⟶ L′ · M

    ξ-·₂ : ∀ {V M M′}
      → Value V
      → M ⟶ M′
        ----------------
      → V · M ⟶ V · M′

    β-→ : ∀ {x N V}
      → Value V
        --------------------------------
      → (`λ x `→ N) · V ⟶ N [ x := V ]

    ξ-suc : ∀ {M M′}
      → M ⟶ M′
        ------------------
      → `suc M ⟶ `suc M′
\end{code}

### Reflexive and transitive closure

\begin{code}
  infix  2 _⟶*_
  infix 1 begin_
  infixr 2 _⟶⟨_⟩_
  infix 3 _∎

  data _⟶*_ : Term → Term → Set where

    _∎ : ∀ (M : Term)
        -------------
      → M ⟶* M

    _⟶⟨_⟩_ : ∀ (L : Term) {M N}
      → L ⟶ M
      → M ⟶* N
        ---------
      → L ⟶* N

  begin_ : ∀ {M N} → (M ⟶* N) → (M ⟶* N)
  begin M⟶*N = M⟶*N
\end{code}

### Stuck terms

\begin{code}
  data Stuck : Term → Set where

    st-·₁ : ∀ {L M}
      → Stuck L
        --------------
      → Stuck (L · M)

    st-·₂ : ∀ {V M}
      → Value V
      → Stuck M
        --------------
      → Stuck (V · M)

    st-·-zero : ∀ {M}
       ------------------
      → Stuck (`zero · M)
      
    st-·-suc : ∀ {V M}
      → Value V
        -------------------
      → Stuck (`suc V · M)

    st-suc : ∀ {M}
      → Stuck M
        --------------
      → Stuck (`suc M)
\end{code}

### Progress

\begin{code}
  data Progress (M : Term) : Set where

    step : ∀ {N}
      → M ⟶ N
        -----------
      → Progress M

    done : 
        Value M
        -----------
      → Progress M

    stuck : 
        Stuck M
        -----------
      → Progress M
\end{code}

I can show that every closed term makes progess in the above sense,
and then use that to compute the normal form of a term.

### Closed terms

\begin{code}
  Closed : Term → Set
  Closed M = free M ≡ []

  Ax-lemma : ∀ {x} → ¬ (Closed ⌊ x ⌋)
  Ax-lemma ()

  ·-lemma₁ : ∀ {L M} → Closed (L · M) → Closed L
  ·-lemma₁ r = lemma r
    where
    lemma : ∀ {A : Set} {xs ys : List A} → xs ++ ys ≡ [] → xs ≡ []
    lemma {xs = []}     _   =  refl
    lemma {xs = x ∷ xs} ()

  ·-lemma₂ : ∀ {L M} → Closed (L · M) → Closed M
  ·-lemma₂ r = lemma r
    where
    lemma : ∀ {A : Set} {xs ys : List A} → xs ++ ys ≡ [] → ys ≡ []
    lemma {xs = []}     refl  =  refl
    lemma {xs = x ∷ xs} ()

  suc-lemma : ∀ {M} → Closed (`suc M) → Closed M
  suc-lemma r  =  r
\end{code}

### Progress

\begin{code}
  progress : ∀ (M : Term) → Closed M → Progress M
  progress ⌊ x ⌋ Cx  =  ⊥-elim (Ax-lemma Cx)
  progress (L · M) CLM with progress L (·-lemma₁ {L} {M} CLM)
  ...    | step L⟶L′  =  step (ξ-·₁ L⟶L′)
  ...    | stuck SL     =  stuck (st-·₁ SL)
  ...    | done VL with progress M (·-lemma₂ {L} {M} CLM)
  ...        | step M⟶M′  =  step (ξ-·₂ VL M⟶M′)
  ...        | stuck SM     =  stuck (st-·₂ VL SM)
  ...        | done VM  with VL
  ...            | Zero     =  stuck st-·-zero
  ...            | Suc VL′  =  stuck (st-·-suc VL′)
  ...            | Fun      =  step (β-→ VM)
  progress (`λ x `→ N) CxN  =  done Fun
  progress `zero Cz         =  done Zero
  progress (`suc M) CsM with progress M (suc-lemma {M} CsM)
  ...    | step M⟶M′  =  step (ξ-suc M⟶M′)
  ...    | stuck SM     =  stuck (st-suc SM)
  ...    | done VM      =  done (Suc VM)
\end{code}

### Repeated progress

\begin{code}

\end{code}


## Second development: Scoped

\begin{code}
module Scoped where
\end{code}

## Third development: Typed

\begin{code}
module Typed where
\end{code}

  infix   4  _∋_`:_
  infix   4  _⊢_`:_
  infixl  5  _,_`:_
  infixr  6  _`→_

  data _∋_`:_ : Env → Id → Type → Set where

    Z : ∀ {Γ A x}
        --------------------
      → Γ , x `: A ∋ x `: A

    S : ∀ {Γ A B x w}
      → w ≢ x
      → Γ ∋ w `: B
        --------------------
      → Γ , x `: A ∋ w `: B

  data _⊢_`:_ : Env → Term → Type → Set where

    Ax : ∀ {Γ A x}
      → Γ ∋ x `: A
        --------------
      → Γ ⊢ ` x `: A

    ⊢λ : ∀ {Γ x N A B}
      → Γ , x `: A ⊢ N `: B
        --------------------------
      → Γ ⊢ (`λ x `→ N) `: A `→ B

    _·_ : ∀ {Γ L M A B}
      → Γ ⊢ L `: A `→ B
      → Γ ⊢ M `: A
        ----------------
      → Γ ⊢ L · M `: B

