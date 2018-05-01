---
title     : "Extensions: Extensions to simply-typed lambda calculus"
layout    : page
permalink : /Extensions
---

## Imports

\begin{code}
module Extensions where
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
infixr 6 _`⊎_
infixr 7 _`×_

infix  4 ƛ_
infix  4 μ_
infixl 5 _·_
infix  6 S_

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  _`×_  : Type → Type → Type
  _`⊎_  : Type → Type → Type
  `⊤    : Type
  `⊥    : Type
  `List : Type → Type

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

  `⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
      -----------
    → Γ ⊢ A `× B

  `proj₁ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ A

  `proj₂ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ B

  `inj₁ : ∀ {Γ A B}
    → Γ ⊢ A
      -----------
    → Γ ⊢ A `⊎ B

  `inj₂ : ∀ {Γ A B}
    → Γ ⊢ B
      -----------
    → Γ ⊢ A `⊎ B

  `case⊎ : ∀ {Γ A B C}
    → Γ ⊢ A `⊎ B
    → Γ , A ⊢ C
    → Γ , B ⊢ C
      ----------
    → Γ ⊢ C

  `tt : ∀ {Γ}
      ------
    → Γ ⊢ `⊤

  `case⊥ : ∀ {Γ A}
    → Γ ⊢ `⊥
      -------
    → Γ ⊢ A 

  `[] : ∀ {Γ A}
      ------------
    → Γ ⊢ `List A

  _`∷_ : ∀ {Γ A}
    → Γ ⊢ A
    → Γ ⊢ `List A
      ------------
    → Γ ⊢ `List A

  `caseL : ∀ {Γ A B}
    → Γ ⊢ `List A
    → Γ ⊢ B
    → Γ , A , `List A ⊢ B
      --------------------
    → Γ ⊢ B

  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ----------
    → Γ ⊢ B
\end{code}


## Test examples


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
rename σ `⟨ M , N ⟩      =  `⟨ rename σ M , rename σ N ⟩
rename σ (`proj₁ L)      =  `proj₁ (rename σ L)
rename σ (`proj₂ L)      =  `proj₂ (rename σ L)
rename σ (`inj₁ M)       =  `inj₁ (rename σ M)
rename σ (`inj₂ N)       =  `inj₂ (rename σ N)
rename σ (`case⊎ L M N)  =  `case⊎ (rename σ L) (rename (ext σ) M) (rename (ext σ) N)
rename σ `tt             =  `tt
rename σ (`case⊥ L)      =  `case⊥ (rename σ L)
rename σ `[]             =  `[]
rename σ (M `∷ N)        =  (rename σ M) `∷ (rename σ N)
rename σ (`caseL L M N)  =  `caseL (rename σ L) (rename σ M) (rename (ext (ext σ)) N)
rename σ (`let M N)      =  `let (rename σ M) (rename (ext σ) N) 
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
subst ρ `⟨ M , N ⟩      =  `⟨ subst ρ M , subst ρ N ⟩
subst ρ (`proj₁ L)      =  `proj₁ (subst ρ L)
subst ρ (`proj₂ L)      =  `proj₂ (subst ρ L)
subst ρ (`inj₁ M)       =  `inj₁ (subst ρ M)
subst ρ (`inj₂ N)       =  `inj₂ (subst ρ N)
subst ρ (`case⊎ L M N)  =  `case⊎ (subst ρ L) (subst (exts ρ) M) (subst (exts ρ) N)
subst ρ `tt             =  `tt
subst ρ (`case⊥ L)      =  `case⊥ (subst ρ L)
subst ρ `[]             =  `[]
subst ρ (M `∷ N)        =  (subst ρ M) `∷ (subst ρ N)
subst ρ (`caseL L M N)  =  `caseL (subst ρ L) (subst ρ M) (subst (exts (exts ρ)) N)
subst ρ (`let M N)      =  `let (subst ρ M) (subst (exts ρ) N) 

_[_] : ∀ {Γ A B}
  → Γ , A ⊢ B
  → Γ ⊢ A
  ------------
  → Γ ⊢ B
_[_] {Γ} {A} N V =  subst {Γ , A} {Γ} ρ N
  where
  ρ : ∀ {B} → Γ , A ∋ B → Γ ⊢ B
  ρ Z      =  V
  ρ (S x)  =  ⌊ x ⌋

_[_][_] : ∀ {Γ A B C}
  → Γ , A , B ⊢ C
  → Γ ⊢ A
  → Γ ⊢ B
    ---------------
  → Γ ⊢ C
_[_][_] {Γ} {A} {B} N V W =  subst {Γ , A , B} {Γ} ρ N
  where
  ρ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
  ρ Z          =  W
  ρ (S Z)      =  V
  ρ (S (S x))  =  ⌊ x ⌋
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

  Pair : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      -----------------
    → Value `⟨ V , W ⟩

  Inj₁ : ∀ {Γ A B} {V : Γ ⊢ A}
    → Value V
      ------------------------
    → Value (`inj₁ {B = B} V)

  Inj₂ : ∀ {Γ A B} {W : Γ ⊢ B}
    → Value W
      ------------------------
    → Value (`inj₂ {A = A} W)

  TT : ∀ {Γ}
      -------------------
    → Value (`tt {Γ = Γ})

  Nil : ∀ {Γ A}
      ----------------------------
    → Value (`[] {Γ = Γ} {A = A})

  Cons : ∀ {Γ A} {V : Γ ⊢ A} {W : Γ ⊢ `List A}
    → Value V
    → Value W
      ---------------
    → Value (V `∷ W)
\end{code}

Implicit arguments need to be supplied when they are
not fixed by the given arguments.

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

  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ ⊢ B}
    → M ⟶ M′
      --------------------------
    → `⟨ M , N ⟩ ⟶ `⟨ M′ , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N′ : Γ ⊢ B}
    → Value V
    → N ⟶ N′
      --------------------------
    → `⟨ V , N ⟩ ⟶ `⟨ V , N′ ⟩

  ξ-proj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L ⟶ L′
      -----------------------
    → `proj₁ L ⟶ `proj₁ L′

  ξ-proj₂ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L ⟶ L′
      -----------------------
    → `proj₂ L ⟶ `proj₂ L′

  β-×₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ------------------------
    → `proj₁ `⟨ V , W ⟩ ⟶ V

  β-×₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ------------------------
    → `proj₂ `⟨ V , W ⟩ ⟶ W

  ξ-inj₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A}
    → M ⟶ M′
      -----------------------------
    → `inj₁ {B = B} M ⟶ `inj₁ M′

  ξ-inj₂ : ∀ {Γ A B} {N N′ : Γ ⊢ B}
    → N ⟶ N′
      -----------------------------
    → `inj₂ {A = A} N ⟶ `inj₂ N′

  ξ-case⊎ : ∀ {Γ A B C} {L L′ : Γ ⊢ A `⊎ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → L ⟶ L′
      -------------------------------
    → `case⊎ L M N ⟶ `case⊎ L′ M N

  β-⊎₁ : ∀ {Γ A B C} {V : Γ ⊢ A} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value V
      ---------------------------------
    → `case⊎ (`inj₁ V) M N ⟶ M [ V ] 

  β-⊎₂ : ∀ {Γ A B C} {W : Γ ⊢ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value W
      ---------------------------------
    → `case⊎ (`inj₂ W) M N ⟶ N [ W ]

  ξ-case⊥ : ∀ {Γ A} {L L′ : Γ ⊢ `⊥}
    → L ⟶ L′
      -------------------------------
    → `case⊥ {A = A} L ⟶ `case⊥ L′

  ξ-∷₁ : ∀ {Γ A} {M M′ : Γ ⊢ A} {N : Γ ⊢ `List A}
    → M ⟶ M′
      -------------------
    → M `∷ N ⟶ M′ `∷ N

  ξ-∷₂ : ∀ {Γ A} {V : Γ ⊢ A} {N N′ : Γ ⊢ `List A}
    → Value V
    → N ⟶ N′
      -------------------
    → V `∷ N ⟶ V `∷ N′

  ξ-caseL : ∀ {Γ A B} {L L′ : Γ ⊢ `List A} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
    → L ⟶ L′
      -------------------------------
    → `caseL L M N ⟶ `caseL L′ M N

  β-List₁ : ∀ {Γ A B} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
      ---------------------
    → `caseL `[] M N ⟶ M

  β-List₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ `List A}
    {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
    → Value V
    → Value W
      -------------------------------------
    → `caseL (V `∷ W) M N ⟶ N [ V ][ W ]
  
  ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
    → M ⟶ M′
      -----------------------
    → `let M N ⟶ `let M′ N

  β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
    → Value V
      ---------------------
    → `let V N ⟶ N [ V ] 
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


## Values do not reduce

Values do not reduce.
\begin{code}
Value-lemma : ∀ {Γ A} {M N : Γ ⊢ A} → Value M → ¬ (M ⟶ N)
Value-lemma Fun         ()
Value-lemma Zero        ()
Value-lemma (Suc VM)    (ξ-suc M⟶M′)     =  Value-lemma VM M⟶M′
Value-lemma (Pair VM _) (ξ-⟨,⟩₁ M⟶M′)    =  Value-lemma VM M⟶M′
Value-lemma (Pair _ VN) (ξ-⟨,⟩₂ _ N⟶N′)  =  Value-lemma VN N⟶N′
Value-lemma (Inj₁ VM)   (ξ-inj₁ M⟶M′)    =  Value-lemma VM M⟶M′
Value-lemma (Inj₂ VN)   (ξ-inj₂ N⟶N′)    =  Value-lemma VN N⟶N′
Value-lemma TT          ()
Value-lemma Nil         ()
Value-lemma (Cons VM _) (ξ-∷₁ M⟶M′)      =  Value-lemma VM M⟶M′
Value-lemma (Cons _ VN) (ξ-∷₂ _ N⟶N′)    =  Value-lemma VN N⟶N′
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
progress (ƛ N)                             =  done Fun
progress (L · M) with progress L
...    | step L⟶L′                       =  step (ξ-·₁ L⟶L′)
...    | done Fun with progress M
...        | step M⟶M′                   =  step (ξ-·₂ Fun M⟶M′)
...        | done VM                       =  step (β-⇒ VM)
progress (`zero)                           =  done Zero
progress (`suc M) with progress M
...    | step M⟶M′                       =  step (ξ-suc M⟶M′)
...    | done VM                           =  done (Suc VM)
progress (`caseℕ L M N) with progress L
...    | step L⟶L′                       =  step (ξ-caseℕ L⟶L′)
...    | done Zero                         =  step β-ℕ₁
...    | done (Suc VL)                     =  step (β-ℕ₂ VL)
progress (μ N)                             =  step β-μ
progress `⟨ M , N ⟩ with progress M
...    | step M⟶M′                       =  step (ξ-⟨,⟩₁ M⟶M′)
...    | done VM with progress N
...        | step N⟶N′                   =  step (ξ-⟨,⟩₂ VM N⟶N′)
...        | done VN                       =  done (Pair VM VN)
progress (`proj₁ L) with progress L
...    | step L⟶L′                       =  step (ξ-proj₁ L⟶L′)
...    | done (Pair VM VN)                 =  step (β-×₁ VM VN)
progress (`proj₂ L) with progress L
...    | step L⟶L′                       =  step (ξ-proj₂ L⟶L′)
...    | done (Pair VM VN)                 =  step (β-×₂ VM VN)
progress (`inj₁ M) with progress M
...    | step M⟶M′                       =  step (ξ-inj₁ M⟶M′)
...    | done VM                           =  done (Inj₁ VM)
progress (`inj₂ N) with progress N
...    | step N⟶N′                       =  step (ξ-inj₂ N⟶N′)
...    | done VN                           =  done (Inj₂ VN)
progress (`case⊎ L M N) with progress L
...    | step L⟶L′                       =  step (ξ-case⊎ L⟶L′)
...    | done (Inj₁ VV)                    =  step (β-⊎₁ VV)
...    | done (Inj₂ VW)                    =  step (β-⊎₂ VW)
progress (`tt)                             =  done TT
progress (`case⊥ {A = A} L) with progress L
...    | step L⟶L′                       =  step (ξ-case⊥ {A = A} L⟶L′)
...    | done ()
progress (`[])                             =  done Nil
progress (M `∷ N) with progress M
...    | step M⟶M′                       =  step (ξ-∷₁ M⟶M′)
...    | done VM with progress N
...        | step N⟶N′                   =  step (ξ-∷₂ VM N⟶N′)
...        | done VN                       =  done (Cons VM VN)
progress (`caseL L M N) with progress L
...    | step L⟶L′                       =  step (ξ-caseL L⟶L′)
...    | done Nil                          =  step β-List₁
...    | done (Cons VV VW)                 =  step (β-List₂ VV VW)
progress (`let M N) with progress M
...    | step M⟶M′                       =  step (ξ-let M⟶M′)
...    | done VM                           =  step (β-let VM)
\end{code}


## Normalise

\begin{code}
Gas : Set
Gas = ℕ

data Normalise {A} (M : ε ⊢ A) : Set where
  normal : ∀ {N : ε ⊢ A}
    → Gas
    → M ⟶* N
      -----------
    → Normalise M

normalise : ∀ {A} → ℕ → (L : ε ⊢ A) → Normalise L
normalise zero    L                         =  normal zero (L ∎)
normalise (suc g) L with progress L
...    | done VL                            =  normal (suc zero) (L ∎)
...    | step {M} L⟶M with normalise g M
...        | normal h M⟶*N                =  normal (suc h) (L ⟶⟨ L⟶M ⟩ M⟶*N)
\end{code}


