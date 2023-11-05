---
title     : "Assignment4: TSPL Assignment 4"
permalink : /TSPL/2023/Assignment4/
---

```
module Assignment4 where
```

## YOUR NAME AND EMAIL GOES HERE


## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using Gradescope. Go to the course page under Learn.
Select "Assessment", then select "Assignment Submission".
Please ensure your files execute correctly under Agda!

**IMPORTANT** For ease of marking, when modifying the given code please write

    -- begin
    -- end

before and after code you add, to indicate your changes.
Full credit may not be awarded if you fail to mark changes clearly.


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

Furthermore, you are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself, or your group in the case of group practicals).


## More

```agda
module More where
```


### Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Decidable using (True; toWitness)
```

### Syntax

```agda
  infix  4 _⊢_
  infix  4 _∋_
  infixl 5 _,_

  infixr 7 _⇒_
  infixr 9 _`×_

  infix  5 ƛ_
  infix  5 μ_
  infixl 7 _·_
  infixl 8 _`*_
  infix  8 `suc_
  infix  9 `_
  infix  9 S_
  infix  9 #_
```

### Types

```agda
  data Type : Set where
    `ℕ    : Type
    _⇒_   : Type → Type → Type
    Nat   : Type
    _`×_  : Type → Type → Type
```

### Contexts

```agda
  data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context
```

### Variables and the lookup judgment

```agda
  data _∋_ : Context → Type → Set where

    Z : ∀ {Γ A}
        ---------
      → Γ , A ∋ A

    S_ : ∀ {Γ A B}
      → Γ ∋ B
        ---------
      → Γ , A ∋ B
```

### Terms and the typing judgment

```agda
  data _⊢_ : Context → Type → Set where

    -- variables

    `_ : ∀ {Γ A}
      → Γ ∋ A
        -----
      → Γ ⊢ A

    -- functions

    ƛ_  :  ∀ {Γ A B}
      → Γ , A ⊢ B
        ---------
      → Γ ⊢ A ⇒ B

    _·_ : ∀ {Γ A B}
      → Γ ⊢ A ⇒ B
      → Γ ⊢ A
        ---------
      → Γ ⊢ B

    -- naturals

    `zero : ∀ {Γ}
        ------
      → Γ ⊢ `ℕ

    `suc_ : ∀ {Γ}
      → Γ ⊢ `ℕ
        ------
      → Γ ⊢ `ℕ

    case : ∀ {Γ A}
      → Γ ⊢ `ℕ
      → Γ ⊢ A
      → Γ , `ℕ ⊢ A
        -----
      → Γ ⊢ A

    -- fixpoint

    μ_ : ∀ {Γ A}
      → Γ , A ⊢ A
        ----------
      → Γ ⊢ A

    -- primitive numbers

    con : ∀ {Γ}
      → ℕ
        -------
      → Γ ⊢ Nat

    _`*_ : ∀ {Γ}
      → Γ ⊢ Nat
      → Γ ⊢ Nat
        -------
      → Γ ⊢ Nat

    -- let

    `let : ∀ {Γ A B}
      → Γ ⊢ A
      → Γ , A ⊢ B
        ----------
      → Γ ⊢ B

    -- products

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

    -- alternative formulation of products

    case× : ∀ {Γ A B C}
      → Γ ⊢ A `× B
      → Γ , A , B ⊢ C
        --------------
      → Γ ⊢ C
```

### Abbreviating de Bruijn indices

```agda
  length : Context → ℕ
  length ∅        =  zero
  length (Γ , _)  =  suc (length Γ)

  lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
  lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
  lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p

  count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
  count {_ , _} {zero}    (s≤s z≤n)  =  Z
  count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

  #_ : ∀ {Γ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length Γ)}
      --------------------------------
    → Γ ⊢ lookup (toWitness n∈Γ)
  #_ n {n∈Γ}  =  ` count (toWitness n∈Γ)
```

## Renaming

```agda
  ext : ∀ {Γ Δ}
    → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
      ---------------------------------
    → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
  ext ρ Z      =  Z
  ext ρ (S x)  =  S (ρ x)

  rename : ∀ {Γ Δ}
    → (∀ {A} → Γ ∋ A → Δ ∋ A)
      -----------------------
    → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
  rename ρ (` x)          =  ` (ρ x)
  rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
  rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
  rename ρ (`zero)        =  `zero
  rename ρ (`suc M)       =  `suc (rename ρ M)
  rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
  rename ρ (μ N)          =  μ (rename (ext ρ) N)
  rename ρ (con n)        =  con n
  rename ρ (M `* N)       =  rename ρ M `* rename ρ N
  rename ρ (`let M N)     =  `let (rename ρ M) (rename (ext ρ) N)
  rename ρ `⟨ M , N ⟩     =  `⟨ rename ρ M , rename ρ N ⟩
  rename ρ (`proj₁ L)     =  `proj₁ (rename ρ L)
  rename ρ (`proj₂ L)     =  `proj₂ (rename ρ L)
  rename ρ (case× L M)    =  case× (rename ρ L) (rename (ext (ext ρ)) M)
```

## Simultaneous Substitution

```agda
  exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
  exts σ Z      =  ` Z
  exts σ (S x)  =  rename S_ (σ x)

  subst : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ⊢ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
  subst σ (` k)          =  σ k
  subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
  subst σ (L · M)        =  (subst σ L) · (subst σ M)
  subst σ (`zero)        =  `zero
  subst σ (`suc M)       =  `suc (subst σ M)
  subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
  subst σ (μ N)          =  μ (subst (exts σ) N)
  subst σ (con n)        =  con n
  subst σ (M `* N)       =  subst σ M `* subst σ N
  subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)
  subst σ `⟨ M , N ⟩     =  `⟨ subst σ M , subst σ N ⟩
  subst σ (`proj₁ L)     =  `proj₁ (subst σ L)
  subst σ (`proj₂ L)     =  `proj₂ (subst σ L)
  subst σ (case× L M)    =  case× (subst σ L) (subst (exts (exts σ)) M)
```

## Single and double substitution

```agda
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

  _[_][_] : ∀ {Γ A B C}
    → Γ , A , B ⊢ C
    → Γ ⊢ A
    → Γ ⊢ B
      -------------
    → Γ ⊢ C
  _[_][_] {Γ} {A} {B} N V W =  subst {Γ , A , B} {Γ} σ N
    where
    σ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
    σ Z          =  W
    σ (S Z)      =  V
    σ (S (S x))  =  ` x
```

## Values

```agda
  data Value : ∀ {Γ A} → Γ ⊢ A → Set where

    -- functions

    V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
        ---------------------------
      → Value (ƛ N)

    -- naturals

    V-zero : ∀ {Γ}
        -----------------
      → Value (`zero {Γ})

    V-suc_ : ∀ {Γ} {V : Γ ⊢ `ℕ}
      → Value V
        --------------
      → Value (`suc V)

    -- primitives

    V-con : ∀ {Γ n}
        -----------------
      → Value (con {Γ} n)

    -- products

    V-⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V
      → Value W
        ----------------
      → Value `⟨ V , W ⟩
```

Implicit arguments need to be supplied when they are
not fixed by the given arguments.

## Reduction

```agda
  infix 2 _—→_

  data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

    -- functions

    ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
      → L —→ L′
        ---------------
      → L · M —→ L′ · M

    ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
      → Value V
      → M —→ M′
        ---------------
      → V · M —→ V · M′

    β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
      → Value V
        --------------------
      → (ƛ N) · V —→ N [ V ]

    -- naturals

    ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
      → M —→ M′
        -----------------
      → `suc M —→ `suc M′

    ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      → L —→ L′
        -------------------------
      → case L M N —→ case L′ M N

    β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
        -------------------
      → case `zero M N —→ M

    β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      → Value V
        ----------------------------
      → case (`suc V) M N —→ N [ V ]

    -- fixpoint

    β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
        ----------------
      → μ N —→ N [ μ N ]

    -- primitive numbers

    ξ-*₁ : ∀ {Γ} {L L′ M : Γ ⊢ Nat}
      → L —→ L′
        -----------------
      → L `* M —→ L′ `* M

    ξ-*₂ : ∀ {Γ} {V M M′ : Γ ⊢ Nat}
      → Value V
      → M —→ M′
        -----------------
      → V `* M —→ V `* M′

    δ-* : ∀ {Γ c d}
        ---------------------------------
      → con {Γ} c `* con d —→ con (c * d)

    -- let

    ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
      → M —→ M′
        ---------------------
      → `let M N —→ `let M′ N

    β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
      → Value V
        -------------------
      → `let V N —→ N [ V ]

    -- products

    ξ-⟨,⟩₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ ⊢ B}
      → M —→ M′
        -------------------------
      → `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

    ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N′ : Γ ⊢ B}
      → Value V
      → N —→ N′
        -------------------------
      → `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

    ξ-proj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
      → L —→ L′
        ---------------------
      → `proj₁ L —→ `proj₁ L′

    ξ-proj₂ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
      → L —→ L′
        ---------------------
      → `proj₂ L —→ `proj₂ L′

    β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V
      → Value W
        ----------------------
      → `proj₁ `⟨ V , W ⟩ —→ V

    β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V
      → Value W
        ----------------------
      → `proj₂ `⟨ V , W ⟩ —→ W

    -- alternative formulation of products

    ξ-case× : ∀ {Γ A B C} {L L′ : Γ ⊢ A `× B} {M : Γ , A , B ⊢ C}
      → L —→ L′
        -----------------------
      → case× L M —→ case× L′ M

    β-case× : ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {M : Γ , A , B ⊢ C}
      → Value V
      → Value W
        ----------------------------------
      → case× `⟨ V , W ⟩ M —→ M [ V ][ W ]
```

## Reflexive and transitive closure

```agda
  infix  2 _—↠_
  infix  1 begin_
  infixr 2 _—→⟨_⟩_
  infix  3 _∎

  data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

    _∎ : (M : Γ ⊢ A)
        ------
      → M —↠ M

    step—→ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
      → M —↠ N
      → L —→ M
        ------
      → L —↠ N

  pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

  begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
    → M —↠ N
      ------
    → M —↠ N
  begin M—↠N = M—↠N
```


## Progress

```agda
  data Progress {A} (M : ∅ ⊢ A) : Set where

    step : ∀ {N : ∅ ⊢ A}
      → M —→ N
        ----------
      → Progress M

    done :
        Value M
        ----------
      → Progress M

  progress : ∀ {A}
    → (M : ∅ ⊢ A)
      -----------
    → Progress M
  progress (` ())
  progress (ƛ N)                              =  done V-ƛ
  progress (L · M) with progress L
  ...    | step L—→L′                         =  step (ξ-·₁ L—→L′)
  ...    | done V-ƛ with progress M
  ...        | step M—→M′                     =  step (ξ-·₂ V-ƛ M—→M′)
  ...        | done VM                        =  step (β-ƛ VM)
  progress (`zero)                            =  done V-zero
  progress (`suc M) with progress M
  ...    | step M—→M′                         =  step (ξ-suc M—→M′)
  ...    | done VM                            =  done (V-suc VM)
  progress (case L M N) with progress L
  ...    | step L—→L′                         =  step (ξ-case L—→L′)
  ...    | done V-zero                        =  step β-zero
  ...    | done (V-suc VL)                    =  step (β-suc VL)
  progress (μ N)                              =  step β-μ
  progress (con n)                            =  done V-con
  progress (L `* M) with progress L
  ...    | step L—→L′                         =  step (ξ-*₁ L—→L′)
  ...    | done V-con with progress M
  ...        | step M—→M′                     =  step (ξ-*₂ V-con M—→M′)
  ...        | done V-con                     =  step δ-*
  progress (`let M N) with progress M
  ...    | step M—→M′                         =  step (ξ-let M—→M′)
  ...    | done VM                            =  step (β-let VM)
  progress `⟨ M , N ⟩ with progress M
  ...    | step M—→M′                         =  step (ξ-⟨,⟩₁ M—→M′)
  ...    | done VM with progress N
  ...        | step N—→N′                     =  step (ξ-⟨,⟩₂ VM N—→N′)
  ...        | done VN                        =  done (V-⟨ VM , VN ⟩)
  progress (`proj₁ L) with progress L
  ...    | step L—→L′                         =  step (ξ-proj₁ L—→L′)
  ...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₁ VM VN)
  progress (`proj₂ L) with progress L
  ...    | step L—→L′                         =  step (ξ-proj₂ L—→L′)
  ...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₂ VM VN)
  progress (case× L M) with progress L
  ...    | step L—→L′                         =  step (ξ-case× L—→L′)
  ...    | done (V-⟨ VM , VN ⟩)               =  step (β-case× VM VN)
```


## Evaluation

```agda
  record Gas : Set where
    constructor gas
    field
      amount : ℕ

  data Finished {Γ A} (N : Γ ⊢ A) : Set where

     done :
         Value N
         ----------
       → Finished N

     out-of-gas :
         ----------
         Finished N

  data Steps {A} : ∅ ⊢ A → Set where

    steps : {L N : ∅ ⊢ A}
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
```


## Examples

```agda
  cube : ∅ ⊢ Nat ⇒ Nat
  cube = ƛ (# 0 `* # 0 `* # 0)

  _ : cube · con 2 —↠ con 8
  _ =
    begin
      cube · con 2
    —→⟨ β-ƛ V-con ⟩
      con 2 `* con 2 `* con 2
    —→⟨ ξ-*₁ δ-* ⟩
      con 4 `* con 2
    —→⟨ δ-* ⟩
      con 8
    ∎

  exp10 : ∅ ⊢ Nat ⇒ Nat
  exp10 = ƛ (`let (# 0 `* # 0)
              (`let (# 0 `* # 0)
                (`let (# 0 `* # 2)
                  (# 0 `* # 0))))

  _ : exp10 · con 2 —↠ con 1024
  _ =
    begin
      exp10 · con 2
    —→⟨ β-ƛ V-con ⟩
      `let (con 2 `* con 2) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
    —→⟨ ξ-let δ-* ⟩
      `let (con 4) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
    —→⟨ β-let V-con ⟩
      `let (con 4 `* con 4) (`let (# 0 `* con 2) (# 0 `* # 0))
    —→⟨ ξ-let δ-* ⟩
      `let (con 16) (`let (# 0 `* con 2) (# 0 `* # 0))
    —→⟨ β-let V-con ⟩
      `let (con 16 `* con 2) (# 0 `* # 0)
    —→⟨ ξ-let δ-* ⟩
      `let (con 32) (# 0 `* # 0)
    —→⟨ β-let V-con ⟩
      con 32 `* con 32
    —→⟨ δ-* ⟩
      con 1024
    ∎

  swap× : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
  swap× = ƛ `⟨ `proj₂ (# 0) , `proj₁ (# 0) ⟩

  _ : swap× · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
  _ =
    begin
      swap× · `⟨ con 42 , `zero ⟩
    —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
      `⟨ `proj₂ `⟨ con 42 , `zero ⟩ , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
    —→⟨ ξ-⟨,⟩₁ (β-proj₂ V-con V-zero) ⟩
      `⟨ `zero , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
    —→⟨ ξ-⟨,⟩₂ V-zero (β-proj₁ V-con V-zero) ⟩
      `⟨ `zero , con 42 ⟩
    ∎

  swap×-case : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
  swap×-case = ƛ case× (# 0) `⟨ # 0 , # 1 ⟩

  _ : swap×-case · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
  _ =
    begin
       swap×-case · `⟨ con 42 , `zero ⟩
     —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
       case× `⟨ con 42 , `zero ⟩ `⟨ # 0 , # 1 ⟩
     —→⟨ β-case× V-con V-zero ⟩
       `⟨ `zero , con 42 ⟩
     ∎
```

#### Exercise `More` (recommended and practice)

Formalise the remaining constructs defined in this chapter.
Make your changes in this file.
Evaluate each example, applied to data as needed,
to confirm it returns the expected answer:

  * sums (recommended)
  * unit type (practice)
  * an alternative formulation of unit type (practice)
  * empty type (recommended)
  * lists (practice)

Please delimit any code you add as follows:

    -- begin
    -- end


## Bisimulation

(No recommended exercises for this chapter.)

#### Exercise `~val⁻¹` (practice)

Show that this also holds in the reverse direction: if `M ~ M†`
and `Value M†` then `Value M`.

```agda
-- Your code goes here
```

#### Exercise `sim⁻¹` (practice)

Show that we also have a simulation in the other direction, and hence that we have
a bisimulation.

#### Exercise `products` (practice)

Show that the two formulations of products in
Chapter [More][plfa.More]
are in bisimulation.  The only constructs you need to include are
variables, and those connected to functions and products.
In this case, the simulation is _not_ lock-step.



## Inference

```
module Inference where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Data.String using (String; _≟_)
  open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Decidable using (False; toWitnessFalse)
  import plfa.part2.More as DB
```

## Syntax

```agda
  infix   4  _∋_⦂_
  infix   4  _⊢_↑_
  infix   4  _⊢_↓_
  infixl  5  _,_⦂_

  infixr  7  _⇒_

  infix   5  ƛ_⇒_
  infix   5  μ_⇒_
  infix   6  _↑
  infix   6  _↓_
  infixl  7  _·_
  infix   8  `suc_
  infix   9  `_
```

Identifiers, types, and contexts are as before:
```agda
  Id : Set
  Id = String

  data Type : Set where
    `ℕ    : Type
    _⇒_   : Type → Type → Type

  data Context : Set where
    ∅     : Context
    _,_⦂_ : Context → Id → Type → Context
```

The syntax of terms is defined by mutual recursion.
```agda
  data Term⁺ : Set
  data Term⁻ : Set

  data Term⁺ where
    `_                       : Id → Term⁺
    _·_                      : Term⁺ → Term⁻ → Term⁺
    _↓_                      : Term⁻ → Type → Term⁺

  data Term⁻ where
    ƛ_⇒_                     : Id → Term⁻ → Term⁻
    `zero                    : Term⁻
    `suc_                    : Term⁻ → Term⁻
    `case_[zero⇒_|suc_⇒_]    : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
    μ_⇒_                     : Id → Term⁻ → Term⁻
    _↑                       : Term⁺ → Term⁻
```

## Example terms

```agda
  two : Term⁻
  two = `suc (`suc `zero)

  plus : Term⁺
  plus = (μ "p" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
            `case (` "m") [zero⇒ ` "n" ↑
                          |suc "m" ⇒ `suc (` "p" · (` "m" ↑) · (` "n" ↑) ↑) ])
              ↓ (`ℕ ⇒ `ℕ ⇒ `ℕ)

  2+2 : Term⁺
  2+2 = plus · two · two

  Ch : Type
  Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

  twoᶜ : Term⁻
  twoᶜ = (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)

  plusᶜ : Term⁺
  plusᶜ = (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
             ` "m" · (` "s" ↑) · (` "n" · (` "s" ↑) · (` "z" ↑) ↑) ↑)
               ↓ (Ch ⇒ Ch ⇒ Ch)

  sucᶜ : Term⁻
  sucᶜ = ƛ "x" ⇒ `suc (` "x" ↑)

  2+2ᶜ : Term⁺
  2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```

## Bidirectional type checking

The typing rules for variables:
```agda
  data _∋_⦂_ : Context → Id → Type → Set where

    Z : ∀ {Γ x A}
        -----------------
      → Γ , x ⦂ A ∋ x ⦂ A

    S : ∀ {Γ x y A B}
      → x ≢ y
      → Γ ∋ x ⦂ A
        -----------------
      → Γ , y ⦂ B ∋ x ⦂ A
```

The judgments for synthesizing
and inheriting types are mutually recursive:
```agda
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
```


#### Exercise `bidirectional-mul` (recommended) {#bidirectional-mul}

Rewrite your definition of multiplication from
Chapter [Lambda](/Lambda/), decorated to support inference.

```agda
  -- Your code goes here
```


#### Exercise `bidirectional-products` (recommended) {#bidirectional-products}

Extend the bidirectional type rules to include products from
Chapter [More](/More/).  Please delimit any code you add as follows:

    -- begin
    -- end

#### Exercise `bidirectional-rest` (stretch) {#bidirectional-rest}

Extend the bidirectional type rules to include the rest of the constructs from
Chapter [More](/More/). Please delimit any code you add as follows:

    -- begin
    -- end


## Prerequisites

Type equality.
```agda
  _≟Tp_ : (A B : Type) → Dec (A ≡ B)
  `ℕ      ≟Tp `ℕ              =  yes refl
  `ℕ      ≟Tp (A ⇒ B)         =  no λ()
  (A ⇒ B) ≟Tp `ℕ              =  no λ()
  (A ⇒ B) ≟Tp (A′ ⇒ B′)
    with A ≟Tp A′ | B ≟Tp B′
  ...  | no A≢    | _         =  no λ{refl → A≢ refl}
  ...  | yes _    | no B≢     =  no λ{refl → B≢ refl}
  ...  | yes refl | yes refl  =  yes refl
```

The domain and range of equal function types are equal:
```agda
  dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
  dom≡ refl = refl

  rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
  rng≡ refl = refl
```

The types `` `ℕ `` and `A ⇒ B` are not equal:
```agda
  ℕ≢⇒ : ∀ {A B} → `ℕ ≢ A ⇒ B
  ℕ≢⇒ ()
```


## Unique types

Looking up a type in the context is unique.
```agda
  uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
  uniq-∋ Z Z                 =  refl
  uniq-∋ Z (S x≢y _)         =  ⊥-elim (x≢y refl)
  uniq-∋ (S x≢y _) Z         =  ⊥-elim (x≢y refl)
  uniq-∋ (S _ ∋x) (S _ ∋x′)  =  uniq-∋ ∋x ∋x′
```

Synthesizing a type is also unique.
```agda
  uniq-↑ : ∀ {Γ M A B} → Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B
  uniq-↑ (⊢` ∋x) (⊢` ∋x′)       =  uniq-∋ ∋x ∋x′
  uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′)  =  rng≡ (uniq-↑ ⊢L ⊢L′)
  uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)       =  refl
```


## Lookup type of a variable in the context

```agda
  ext∋ : ∀ {Γ B x y}
    → x ≢ y
    → ¬ (∃[ A ] Γ ∋ x ⦂ A)
      ----------------------------
    → ¬ (∃[ A ] Γ , y ⦂ B ∋ x ⦂ A)
  ext∋ x≢y _  ⟨ A , Z ⟩       =  x≢y refl
  ext∋ _   ¬∃ ⟨ A , S _ ∋x ⟩  =  ¬∃ ⟨ A , ∋x ⟩
```

```agda
  lookup : ∀ (Γ : Context) (x : Id)
           ------------------------
         → Dec (∃[ A ] Γ ∋ x ⦂ A)
  lookup ∅ x                        =  no  (λ ())
  lookup (Γ , y ⦂ B) x with x ≟ y
  ... | yes refl                    =  yes ⟨ B , Z ⟩
  ... | no x≢y with lookup Γ x
  ...             | no  ¬∃          =  no  (ext∋ x≢y ¬∃)
  ...             | yes ⟨ A , ∋x ⟩  =  yes ⟨ A , S x≢y ∋x ⟩
```


## Promoting negations

```agda
  ¬arg : ∀ {Γ A B L M}
    → Γ ⊢ L ↑ A ⇒ B
    → ¬ Γ ⊢ M ↓ A
      --------------------------
    → ¬ (∃[ B′ ] Γ ⊢ L · M ↑ B′)
  ¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′
```

```agda
  ¬switch : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≢ B
      ---------------
    → ¬ Γ ⊢ (M ↑) ↓ B
  ¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = A≢B A′≡B
```


## Synthesize and inherit types

```agda
  synthesize : ∀ (Γ : Context) (M : Term⁺)
               ---------------------------
             → Dec (∃[ A ] Γ ⊢ M ↑ A )

  inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
      ---------------
    → Dec (Γ ⊢ M ↓ A)
```

Synthesis.
```agda
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
```

Inheritance:
```agda
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
```

## Testing the example terms

```
  S′ : ∀ {Γ x y A B}
     → {x≢y : False (x ≟ y)}
     → Γ ∋ x ⦂ A
       ------------------
     → Γ , y ⦂ B ∋ x ⦂ A

  S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x
```

Typing two plus two on naturals:
```agda
  ⊢2+2 : ∅ ⊢ 2+2 ↑ `ℕ
  ⊢2+2 =
    (⊢↓
     (⊢μ
      (⊢ƛ
       (⊢ƛ
        (⊢case (⊢` (S′ Z)) (⊢↑ (⊢` Z) refl)
         (⊢suc
          (⊢↑
           (⊢`
            (S′
             (S′
              (S′ Z)))
            · ⊢↑ (⊢` Z) refl
            · ⊢↑ (⊢` (S′ Z)) refl)
           refl))))))
     · ⊢suc (⊢suc ⊢zero)
     · ⊢suc (⊢suc ⊢zero))

  _ : synthesize ∅ 2+2 ≡ yes ⟨ `ℕ , ⊢2+2 ⟩
  _ = refl
```

Typing two plus two with Church numerals:
```agda
  ⊢2+2ᶜ : ∅ ⊢ 2+2ᶜ ↑ `ℕ
  ⊢2+2ᶜ =
    ⊢↓
    (⊢ƛ
     (⊢ƛ
      (⊢ƛ
       (⊢ƛ
        (⊢↑
         (⊢`
          (S′
           (S′
            (S′ Z)))
          · ⊢↑ (⊢` (S′ Z)) refl
          ·
          ⊢↑
          (⊢`
           (S′
            (S′ Z))
           · ⊢↑ (⊢` (S′ Z)) refl
           · ⊢↑ (⊢` Z) refl)
          refl)
         refl)))))
    ·
    ⊢ƛ
    (⊢ƛ
     (⊢↑
      (⊢` (S′ Z) ·
       ⊢↑ (⊢` (S′ Z) · ⊢↑ (⊢` Z) refl)
       refl)
      refl))
    ·
    ⊢ƛ
    (⊢ƛ
     (⊢↑
      (⊢` (S′ Z) ·
       ⊢↑ (⊢` (S′ Z) · ⊢↑ (⊢` Z) refl)
       refl)
      refl))
    · ⊢ƛ (⊢suc (⊢↑ (⊢` Z) refl))
    · ⊢zero

  _ : synthesize ∅ 2+2ᶜ ≡ yes ⟨ `ℕ , ⊢2+2ᶜ ⟩
  _ = refl
```

## Testing the error cases

Unbound variable:
  ```agda
  _ : synthesize ∅ ((ƛ "x" ⇒ ` "y" ↑) ↓ (`ℕ ⇒ `ℕ)) ≡ no _
  _ = refl
```

Argument in application is ill typed:
```agda
  _ : synthesize ∅ (plus · sucᶜ) ≡ no _
  _ = refl
```

Function in application is ill typed:
```agda
  _ : synthesize ∅ (plus · sucᶜ · two) ≡ no _
  _ = refl
```

Function in application has type natural:
```agda
  _ : synthesize ∅ ((two ↓ `ℕ) · two) ≡ no _
  _ = refl
```

Abstraction inherits type natural:
```agda
  _ : synthesize ∅ (twoᶜ ↓ `ℕ) ≡ no _
  _ = refl
```

Zero inherits a function type:
```agda
  _ : synthesize ∅ (`zero ↓ `ℕ ⇒ `ℕ) ≡ no _
  _ = refl
```

Successor inherits a function type:
```agda
  _ : synthesize ∅ (two ↓ `ℕ ⇒ `ℕ) ≡ no _
  _ = refl
```

Successor of an ill-typed term:
```agda
  _ : synthesize ∅ (`suc twoᶜ ↓ `ℕ) ≡ no _
  _ = refl
```

Case of a term with a function type:
```agda
  _ : synthesize ∅
        ((`case (twoᶜ ↓ Ch) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
  _ = refl
```

Case of an ill-typed term:
```agda
  _ : synthesize ∅
        ((`case (twoᶜ ↓ `ℕ) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
  _ = refl
```

Inherited and synthesised types disagree in a switch:
```agda
  _ : synthesize ∅ (((ƛ "x" ⇒ ` "x" ↑) ↓ `ℕ ⇒ (`ℕ ⇒ `ℕ))) ≡ no _
  _ = refl
```


## Erasure

Erase a type:
```agda
  ∥_∥Tp : Type → DB.Type
  ∥ `ℕ ∥Tp             =  DB.`ℕ
  ∥ A ⇒ B ∥Tp          =  ∥ A ∥Tp DB.⇒ ∥ B ∥Tp
```

Erase a context:
```agda
  ∥_∥Cx : Context → DB.Context
  ∥ ∅ ∥Cx              =  DB.∅
  ∥ Γ , x ⦂ A ∥Cx      =  ∥ Γ ∥Cx DB., ∥ A ∥Tp
```

Erase a lookup judgment:
```agda
  ∥_∥∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ∥ Γ ∥Cx DB.∋ ∥ A ∥Tp
  ∥ Z ∥∋               =  DB.Z
  ∥ S x≢ ∋x ∥∋         =  DB.S ∥ ∋x ∥∋
```

Erase a typing judgment.
```agda
  ∥_∥⁺ : ∀ {Γ M A} → Γ ⊢ M ↑ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp
  ∥_∥⁻ : ∀ {Γ M A} → Γ ⊢ M ↓ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp

  ∥ ⊢` ⊢x ∥⁺           =  DB.` ∥ ⊢x ∥∋
  ∥ ⊢L · ⊢M ∥⁺         =  ∥ ⊢L ∥⁺ DB.· ∥ ⊢M ∥⁻
  ∥ ⊢↓ ⊢M ∥⁺           =  ∥ ⊢M ∥⁻

  ∥ ⊢ƛ ⊢N ∥⁻           =  DB.ƛ ∥ ⊢N ∥⁻
  ∥ ⊢zero ∥⁻           =  DB.`zero
  ∥ ⊢suc ⊢M ∥⁻         =  DB.`suc ∥ ⊢M ∥⁻
  ∥ ⊢case ⊢L ⊢M ⊢N ∥⁻  =  DB.case ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁻ ∥ ⊢N ∥⁻
  ∥ ⊢μ ⊢M ∥⁻           =  DB.μ ∥ ⊢M ∥⁻
  ∥ ⊢↑ ⊢M refl ∥⁻      =  ∥ ⊢M ∥⁺
```

Erasure of the type derivations in
this chapter yield the corresponding intrinsically-typed terms
from the earlier chapter:
```agda
  _ : ∥ ⊢2+2 ∥⁺ ≡ DB.2+2
  _ = refl

  _ : ∥ ⊢2+2ᶜ ∥⁺ ≡ DB.2+2ᶜ
  _ = refl
```


#### Exercise `inference-multiplication` (recommended)

Apply inference to your decorated definition of multiplication from
exercise [`bidirectional-mul`](/Inference/#bidirectional-mul), and show that
erasure of the inferred typing yields your definition of
multiplication from Chapter [DeBruijn](/DeBruijn/).

```agda
-- Your code goes here
```

#### Exercise `inference-products` (recommended)

Using your rules from exercise
[`bidirectional-products`](/Inference/#bidirectional-products), extend
bidirectional inference to include products. Also extend erasure.
Please delimit any code you add as follows:

    -- begin
    -- end


#### Exercise `inference-rest` (stretch)

Using your rules from exercise
[`bidirectional-rest`](/Inference/#bidirectional-rest), extend
bidirectional inference to include the rest of the constructs from
Chapter [More](/More/). Also extend erasure.
Please delimit any code you add as follows:

    -- begin
    -- end


## Untyped

```
module Untyped where
```

## Imports

```agda
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
```


```
  open import plfa.part2.Untyped
    hiding ()
```

#### Exercise (`Type≃⊤`) (practice)

Show that `Type` is isomorphic to `⊤`, the unit type.

```agda
  -- Your code goes here
```

#### Exercise (`Context≃ℕ`) (practice)

Show that `Context` is isomorphic to `ℕ`.

```agda
  -- Your code goes here
```

#### Exercise (`variant-1`) (practice)

How would the rules change if we want call-by-value where terms
normalise completely?  Assume that `β` should not permit reduction
unless both terms are in normal form.

```agda
  -- Your code goes here
```

#### Exercise (`variant-2`) (practice)

How would the rules change if we want call-by-value where terms
do not reduce underneath lambda?  Assume that `β`
permits reduction when both terms are values (that is, lambda
abstractions).  What would `2+2ᶜ` reduce to in this case?

```agda
  -- Your code goes here
```


#### Exercise `plus-eval` (practice)

Use the evaluator to confirm that `plus · two · two` and `four`
normalise to the same term.

```agda
  -- Your code goes here
```

#### Exercise `multiplication-untyped` (recommended)

Use the encodings above to translate your definition of
multiplication from previous chapters with the Scott
representation and the encoding of the fixpoint operator.
Confirm that two times two is four.

```agda
  -- Your code goes here
```

#### Exercise `encode-more` (stretch)

Along the lines above, encode all of the constructs of
Chapter [More](/More/),
save for primitive numbers, in the untyped lambda calculus.

```agda
  -- Your code goes here
```
