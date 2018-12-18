---
title     : "Exam: TSPL Mock Exam file"
layout    : page
permalink : /Exam/
---


\begin{code}
module Exam where
\end{code}

**IMPORTANT** For ease of marking, when modifying the given code please write

    -- begin
    -- end

before and after code you add, to indicate your changes.

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String)
open import Data.String.Unsafe using (_≟_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (Decidable)
\end{code}

## Problem 1

\begin{code}
module Problem1 where

  open import Function using (_∘_)
\end{code}

Remember to indent all code by two spaces.

### (a)

### (b)

### (c)


## Problem 2

Remember to indent all code by two spaces.

\begin{code}
module Problem2 where
\end{code}

### Infix declarations

\begin{code}
  infix  4 _⊢_
  infix  4 _∋_
  infixl 5 _,_

  infixr 7 _⇒_

  infix  5 ƛ_
  infix  5 μ_
  infixl 7 _·_
  infix  8 `suc_
  infix  9 `_
  infix  9 S_
  infix  9 #_ 
\end{code}

### Types and contexts

\begin{code}
  data Type : Set where
    _⇒_   : Type → Type → Type
    `ℕ    : Type

  data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context
\end{code}

### Variables and the lookup judgment

\begin{code}
  data _∋_ : Context → Type → Set where

    Z : ∀ {Γ A}
        ----------
      → Γ , A ∋ A

    S_ : ∀ {Γ A B}
      → Γ ∋ A
        ---------
      → Γ , B ∋ A
\end{code}

### Terms and the typing judgment

\begin{code}
  data _⊢_ : Context → Type → Set where

    `_ : ∀ {Γ} {A}
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

    `suc_ : ∀ {Γ}
      → Γ ⊢ `ℕ
        -------
      → Γ ⊢ `ℕ

    case : ∀ {Γ A}
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

### Abbreviating de Bruijn indices

\begin{code}
  lookup : Context → ℕ → Type
  lookup (Γ , A) zero     =  A
  lookup (Γ , _) (suc n)  =  lookup Γ n
  lookup ∅       _        =  ⊥-elim impossible
    where postulate impossible : ⊥

  count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
  count {Γ , _} zero     =  Z
  count {Γ , _} (suc n)  =  S (count n)
  count {∅}     _        =  ⊥-elim impossible
    where postulate impossible : ⊥

  #_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
  # n  =  ` count n
\end{code}

### Renaming

\begin{code}
  ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
      -----------------------------------
    → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
  ext ρ Z      =  Z
  ext ρ (S x)  =  S (ρ x)

  rename : ∀ {Γ Δ}
    → (∀ {A} → Γ ∋ A → Δ ∋ A)
      ------------------------
    → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
  rename ρ (` x)          =  ` (ρ x)
  rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
  rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
  rename ρ (`zero)        =  `zero
  rename ρ (`suc M)       =  `suc (rename ρ M)
  rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
  rename ρ (μ N)          =  μ (rename (ext ρ) N)
\end{code}

### Simultaneous Substitution

\begin{code}
  exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
      ----------------------------------
    → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
  exts σ Z      =  ` Z
  exts σ (S x)  =  rename S_ (σ x)

  subst : ∀ {Γ Δ}
    → (∀ {A} → Γ ∋ A → Δ ⊢ A)
      ------------------------
    → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
  subst σ (` k)          =  σ k
  subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
  subst σ (L · M)        =  (subst σ L) · (subst σ M)
  subst σ (`zero)        =  `zero
  subst σ (`suc M)       =  `suc (subst σ M)
  subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
  subst σ (μ N)          =  μ (subst (exts σ) N)
\end{code}

### Single substitution

\begin{code}
  _[_] : ∀ {Γ A B}
          → Γ , B ⊢ A
          → Γ ⊢ B 
            ---------
          → Γ ⊢ A
  _[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
    where
    σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
    σ Z      =  M
    σ (S x)  =  ` x
\end{code}

### Values

\begin{code}
  data Value : ∀ {Γ A} → Γ ⊢ A → Set where

    V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
        ---------------------------
      → Value (ƛ N)

    V-zero : ∀ {Γ}
        -----------------
      → Value (`zero {Γ})

    V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
      → Value V
        --------------
      → Value (`suc V)
\end{code}

### Reduction

\begin{code}
  infix 2 _—→_

  data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

    ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
      → L —→ L′
        -----------------
      → L · M —→ L′ · M

    ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
      → Value V
      → M —→ M′
        --------------
      → V · M —→ V · M′

    β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
      → Value W
        -------------------
      → (ƛ N) · W —→ N [ W ]

    ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
      → M —→ M′
        ----------------
      → `suc M —→ `suc M′

    ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      → L —→ L′
        --------------------------
      → case L M N —→ case L′ M N

    β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
        -------------------
      → case `zero M N —→ M

    β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      → Value V
        -----------------------------
      → case (`suc V) M N —→ N [ V ]

    β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
        ---------------
      → μ N —→ N [ μ N ]
\end{code}


### Reflexive and transitive closure

\begin{code}
  infix  2 _—↠_
  infix  1 begin_
  infixr 2 _—→⟨_⟩_
  infix  3 _∎

  data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

    _∎ : ∀ {Γ A} (M : Γ ⊢ A)
        --------
      → M —↠ M

    _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
      → L —→ M
      → M —↠ N
        ---------
      → L —↠ N

  begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A}
    → M —↠ N
      ------
    → M —↠ N
  begin M—↠N = M—↠N
\end{code}


### Progress

\begin{code}
  data Progress {A} (M : ∅ ⊢ A) : Set where

    step : ∀ {N : ∅ ⊢ A}
      → M —→ N
        -------------
      → Progress M

    done :
        Value M
        ----------
      → Progress M

  progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
  progress (` ())
  progress (ƛ N)                          =  done V-ƛ
  progress (L · M) with progress L
  ...    | step L—→L′                     =  step (ξ-·₁ L—→L′)
  ...    | done V-ƛ with progress M
  ...        | step M—→M′                 =  step (ξ-·₂ V-ƛ M—→M′)
  ...        | done VM                    =  step (β-ƛ VM)
  progress (`zero)                        =  done V-zero
  progress (`suc M) with progress M
  ...    | step M—→M′                     =  step (ξ-suc M—→M′)
  ...    | done VM                        =  done (V-suc VM)
  progress (case L M N) with progress L
  ...    | step L—→L′                     =  step (ξ-case L—→L′)
  ...    | done V-zero                    =  step (β-zero)
  ...    | done (V-suc VL)                =  step (β-suc VL)
  progress (μ N)                          =  step (β-μ)
\end{code}

### Evaluation

\begin{code}
  data Gas : Set where
    gas : ℕ → Gas

  data Finished {Γ A} (N : Γ ⊢ A) : Set where

     done :
         Value N
         ----------
       → Finished N

     out-of-gas :
         ----------
         Finished N

  data Steps : ∀ {A} → ∅ ⊢ A → Set where

    steps : ∀ {A} {L N : ∅ ⊢ A}
      → L —↠ N
      → Finished N
        ----------
      → Steps L

  eval : ∀ {A}
    → Gas
    → (L : ∅ ⊢ A)
      -----------
    → Steps L
  eval (gas zero)    L                     =  steps (L ∎) out-of-gas
  eval (gas (suc m)) L with progress L
  ... | done VL                            =  steps (L ∎) (done VL)
  ... | step {M} L—→M with eval (gas m) M
  ...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
\end{code}

## Problem 3

Remember to indent all code by two spaces.

\begin{code}
module Problem3 where
\end{code}

### Imports

\begin{code}
  import plfa.DeBruijn as DB
\end{code}

### Syntax

\begin{code}
  infix   4  _∋_⦂_
  infix   4  _⊢_↑_
  infix   4  _⊢_↓_
  infixl  5  _,_⦂_

  infix   5  ƛ_⇒_
  infix   5  μ_⇒_
  infix   6  _↑
  infix   6  _↓_
  infixl  7  _·_
  infix   8  `suc_
  infix   9  `_
\end{code}

### Types

\begin{code}
  data Type : Set where
    _⇒_   : Type → Type → Type
    `ℕ    : Type
\end{code}

### Identifiers 

\begin{code}
  Id : Set
  Id = String
\end{code}

### Contexts

\begin{code}
  data Context : Set where
    ∅     : Context
    _,_⦂_ : Context → Id → Type → Context
\end{code}

### Terms

\begin{code}
  data Term⁺ : Set
  data Term⁻ : Set

  data Term⁺ where
    `_                        : Id → Term⁺
    _·_                       : Term⁺ → Term⁻ → Term⁺
    _↓_                       : Term⁻ → Type → Term⁺

  data Term⁻ where
    ƛ_⇒_                     : Id → Term⁻ → Term⁻
    `zero                    : Term⁻
    `suc_                    : Term⁻ → Term⁻
    `case_[zero⇒_|suc_⇒_]    : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
    μ_⇒_                     : Id → Term⁻ → Term⁻
    _↑                       : Term⁺ → Term⁻
\end{code}

### Lookup 

\begin{code}
  data _∋_⦂_ : Context → Id → Type → Set where

    Z : ∀ {Γ x A}
        --------------------
      → Γ , x ⦂ A ∋ x ⦂ A

    S : ∀ {Γ x y A B}
      → x ≢ y
      → Γ ∋ x ⦂ A
        -----------------
      → Γ , y ⦂ B ∋ x ⦂ A
\end{code}

### Bidirectional type checking

\begin{code}
  data _⊢_↑_ : Context → Term⁺ → Type → Set
  data _⊢_↓_ : Context → Term⁻ → Type → Set

  data _⊢_↑_ where

    ⊢` : ∀ {Γ A x}
      → Γ ∋ x ⦂ A
        -----------
      → Γ ⊢ ` x ↑ A

    _·_ : ∀ {Γ L M A B}
      → Γ ⊢ L ↑ A ⇒ B
      → Γ ⊢ M ↓ A
        -------------
      → Γ ⊢ L · M ↑ B

    ⊢↓ : ∀ {Γ M A}
      → Γ ⊢ M ↓ A
        ---------------
      → Γ ⊢ (M ↓ A) ↑ A

  data _⊢_↓_ where

    ⊢ƛ : ∀ {Γ x N A B}
      → Γ , x ⦂ A ⊢ N ↓ B
        -------------------
      → Γ ⊢ ƛ x ⇒ N ↓ A ⇒ B

    ⊢zero : ∀ {Γ}
        --------------
      → Γ ⊢ `zero ↓ `ℕ

    ⊢suc : ∀ {Γ M}
      → Γ ⊢ M ↓ `ℕ
        ---------------
      → Γ ⊢ `suc M ↓ `ℕ

    ⊢case : ∀ {Γ L M x N A}
      → Γ ⊢ L ↑ `ℕ
      → Γ ⊢ M ↓ A
      → Γ , x ⦂ `ℕ ⊢ N ↓ A
        -------------------------------------
      → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓ A

    ⊢μ : ∀ {Γ x N A}
      → Γ , x ⦂ A ⊢ N ↓ A
        -----------------
      → Γ ⊢ μ x ⇒ N ↓ A

    ⊢↑ : ∀ {Γ M A B}
      → Γ ⊢ M ↑ A
      → A ≡ B
        -------------
      → Γ ⊢ (M ↑) ↓ B
\end{code}


### Type equality

\begin{code}
  _≟Tp_ : (A B : Type) → Dec (A ≡ B)
  `ℕ      ≟Tp `ℕ              =  yes refl
  `ℕ      ≟Tp (A ⇒ B)         =  no λ()
  (A ⇒ B) ≟Tp `ℕ              =  no λ()
  (A ⇒ B) ≟Tp (A′ ⇒ B′)
    with A ≟Tp A′ | B ≟Tp B′
  ...  | no A≢    | _         =  no λ{refl → A≢ refl}
  ...  | yes _    | no B≢     =  no λ{refl → B≢ refl}
  ...  | yes refl | yes refl  =  yes refl
\end{code}

### Prerequisites

\begin{code}
  dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
  dom≡ refl = refl

  rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
  rng≡ refl = refl

  ℕ≢⇒ : ∀ {A B} → `ℕ ≢ A ⇒ B
  ℕ≢⇒ ()
\end{code}


### Unique lookup

\begin{code}
  uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
  uniq-∋ Z Z                 =  refl
  uniq-∋ Z (S x≢y _)         =  ⊥-elim (x≢y refl)
  uniq-∋ (S x≢y _) Z         =  ⊥-elim (x≢y refl)
  uniq-∋ (S _ ∋x) (S _ ∋x′)  =  uniq-∋ ∋x ∋x′
\end{code}

### Unique synthesis

\begin{code}
  uniq-↑ : ∀ {Γ M A B} → Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B
  uniq-↑ (⊢` ∋x) (⊢` ∋x′)       =  uniq-∋ ∋x ∋x′
  uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′)  =  rng≡ (uniq-↑ ⊢L ⊢L′)
  uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)       =  refl 
\end{code}

## Lookup type of a variable in the context

\begin{code}
  ext∋ : ∀ {Γ B x y}
    → x ≢ y
    → ¬ ∃[ A ]( Γ ∋ x ⦂ A )
      -----------------------------
    → ¬ ∃[ A ]( Γ , y ⦂ B ∋ x ⦂ A )
  ext∋ x≢y _  ⟨ A , Z ⟩       =  x≢y refl
  ext∋ _   ¬∃ ⟨ A , S _ ⊢x ⟩  =  ¬∃ ⟨ A , ⊢x ⟩

  lookup : ∀ (Γ : Context) (x : Id)
      -----------------------
    → Dec (∃[ A ](Γ ∋ x ⦂ A))
  lookup ∅ x                        =  no  (λ ())
  lookup (Γ , y ⦂ B) x with x ≟ y
  ... | yes refl                    =  yes ⟨ B , Z ⟩
  ... | no x≢y with lookup Γ x
  ...             | no  ¬∃          =  no  (ext∋ x≢y ¬∃)
  ...             | yes ⟨ A , ⊢x ⟩  =  yes ⟨ A , S x≢y ⊢x ⟩
\end{code}

### Promoting negations

\begin{code}
  ¬arg : ∀ {Γ A B L M}
    → Γ ⊢ L ↑ A ⇒ B
    → ¬ Γ ⊢ M ↓ A
      -------------------------
    → ¬ ∃[ B′ ](Γ ⊢ L · M ↑ B′)
  ¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′

  ¬switch : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≢ B
      ---------------
    → ¬ Γ ⊢ (M ↑) ↓ B
  ¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = A≢B A′≡B
\end{code}


## Synthesize and inherit types

\begin{code}
  synthesize : ∀ (Γ : Context) (M : Term⁺)
      -----------------------
    → Dec (∃[ A ](Γ ⊢ M ↑ A))

  inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
      ---------------
    → Dec (Γ ⊢ M ↓ A)

  synthesize Γ (` x) with lookup Γ x
  ... | no  ¬∃              =  no  (λ{ ⟨ A , ⊢` ∋x ⟩ → ¬∃ ⟨ A , ∋x ⟩ })
  ... | yes ⟨ A , ∋x ⟩      =  yes ⟨ A , ⊢` ∋x ⟩
  synthesize Γ (L · M) with synthesize Γ L
  ... | no  ¬∃              =  no  (λ{ ⟨ _ , ⊢L  · _  ⟩  →  ¬∃ ⟨ _ , ⊢L ⟩ })
  ... | yes ⟨ `ℕ ,    ⊢L ⟩  =  no  (λ{ ⟨ _ , ⊢L′ · _  ⟩  →  ℕ≢⇒ (uniq-↑ ⊢L ⊢L′) })
  ... | yes ⟨ A ⇒ B , ⊢L ⟩ with inherit Γ M A
  ...    | no  ¬⊢M          =  no  (¬arg ⊢L ¬⊢M)
  ...    | yes ⊢M           =  yes ⟨ B , ⊢L · ⊢M ⟩  
  synthesize Γ (M ↓ A) with inherit Γ M A
  ... | no  ¬⊢M             =  no  (λ{ ⟨ _ , ⊢↓ ⊢M ⟩  →  ¬⊢M ⊢M })
  ... | yes ⊢M              =  yes ⟨ A , ⊢↓ ⊢M ⟩

  inherit Γ (ƛ x ⇒ N) `ℕ      =  no  (λ())
  inherit Γ (ƛ x ⇒ N) (A ⇒ B) with inherit (Γ , x ⦂ A) N B
  ... | no ¬⊢N                =  no  (λ{ (⊢ƛ ⊢N)  →  ¬⊢N ⊢N })
  ... | yes ⊢N                =  yes (⊢ƛ ⊢N)
  inherit Γ `zero `ℕ          =  yes ⊢zero
  inherit Γ `zero (A ⇒ B)     =  no  (λ())
  inherit Γ (`suc M) `ℕ with inherit Γ M `ℕ
  ... | no ¬⊢M                =  no  (λ{ (⊢suc ⊢M)  →  ¬⊢M ⊢M })
  ... | yes ⊢M                =  yes (⊢suc ⊢M)
  inherit Γ (`suc M) (A ⇒ B)  =  no  (λ())
  inherit Γ (`case L [zero⇒ M |suc x ⇒ N ]) A with synthesize Γ L
  ... | no ¬∃                 =  no  (λ{ (⊢case ⊢L  _ _) → ¬∃ ⟨ `ℕ , ⊢L ⟩})
  ... | yes ⟨ _ ⇒ _ , ⊢L ⟩    =  no  (λ{ (⊢case ⊢L′ _ _) → ℕ≢⇒ (uniq-↑ ⊢L′ ⊢L) })   
  ... | yes ⟨ `ℕ ,    ⊢L ⟩ with inherit Γ M A
  ...    | no ¬⊢M             =  no  (λ{ (⊢case _ ⊢M _) → ¬⊢M ⊢M })
  ...    | yes ⊢M with inherit (Γ , x ⦂ `ℕ) N A
  ...       | no ¬⊢N          =  no  (λ{ (⊢case _ _ ⊢N) → ¬⊢N ⊢N })
  ...       | yes ⊢N          =  yes (⊢case ⊢L ⊢M ⊢N)
  inherit Γ (μ x ⇒ N) A with inherit (Γ , x ⦂ A) N A
  ... | no ¬⊢N                =  no  (λ{ (⊢μ ⊢N) → ¬⊢N ⊢N })
  ... | yes ⊢N                =  yes (⊢μ ⊢N)
  inherit Γ (M ↑) B with synthesize Γ M
  ... | no  ¬∃                =  no  (λ{ (⊢↑ ⊢M _) → ¬∃ ⟨ _ , ⊢M ⟩ })
  ... | yes ⟨ A , ⊢M ⟩ with A ≟Tp B
  ...   | no  A≢B             =  no  (¬switch ⊢M A≢B)
  ...   | yes A≡B             =  yes (⊢↑ ⊢M A≡B)
\end{code}

