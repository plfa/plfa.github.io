---
title     : "Exam: TSPL Exam file"
permalink : /TSPL/2022/Exam/
---


```agda
module Exam where
```

**IMPORTANT** For ease of marking, when modifying the given code please write

    -- begin
    -- end

before and after code you add, to indicate your changes.

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤?_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
```

## Problem 1

```agda
module Problem1 where

  open import Function using (_∘_)
```

Remember to indent all code by two spaces.

### (a)

### (b)


## Problem 2

Remember to indent all code by two spaces.

```agda
module Problem2 where
```

### Infix declarations

```agda
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
```

### Types and contexts

```agda
  data Type : Set where
    _⇒_   : Type → Type → Type
    `ℕ    : Type

  data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context
```

### Variables and the lookup judgment

```agda
  data _∋_ : Context → Type → Set where

    Z : ∀ {Γ A}
        ----------
      → Γ , A ∋ A

    S_ : ∀ {Γ A B}
      → Γ ∋ A
        ---------
      → Γ , B ∋ A
```

### Terms and the typing judgment

```agda
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
```

### Renaming

```agda
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
```

### Simultaneous Substitution

```agda
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
```

### Single and double substitution

```agda
  _[_] : ∀ {Γ A B}
          → Γ , A ⊢ B
          → Γ ⊢ A
            ---------
          → Γ ⊢ B
  _[_] {Γ} {A} {B} N V =  subst {Γ , A} {Γ} σ {B} N
    where
    σ : ∀ {B} → Γ , A ∋ B → Γ ⊢ B
    σ Z      =  V
    σ (S x)  =  ` x

  _[_][_] : ∀ {Γ A B C}
          → Γ , A , B ⊢ C
          → Γ ⊢ A
          → Γ ⊢ B
            ---------
          → Γ ⊢ C
  _[_][_] {Γ} {A} {B} {C} N V W =  subst {Γ , A , B} {Γ} σ {C} N
    where
    σ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
    σ Z          =  W
    σ (S Z)      =  V
    σ (S (S x))  =  ` x
```

### Values

```agda
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
```

### Reduction

```agda
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
```


### Reflexive and transitive closure

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


### Progress

```agda
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
```

### Evaluation

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
```

### Example

Here is a term (in extrinsic style) to add two numbers.

    plus = μ "plus" ⇒ ƛ "m" ⇒ ƛ n ⇒
              case ` "m" [zero⇒ ` "n" |suc "m" ⇒ ` "plus" · ` "m" · ` "n" ]

Here is a sample reduction demonstrating that two plus two is four.

```agda
  pattern two = `suc `suc `zero
  pattern plus = μ ƛ ƛ (case (` S Z) (` Z) (`suc (` S S S Z · ` Z · ` S Z)))

  2+2 : ∅ ⊢ `ℕ
  2+2 = plus · two · two

  _ : 2+2 —↠ `suc `suc `suc `suc `zero
  _ =
    begin
      plus · two · two
    —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
      (ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z))) · two · two
    —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
      (ƛ case two (` Z) (`suc (plus · ` Z · ` S Z))) · two
    —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
      case two two (`suc (plus · ` Z · two))
    —→⟨ β-suc (V-suc V-zero) ⟩
      `suc (plus · `suc `zero · two)
    —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
      `suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
        · `suc `zero · two)
    —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
      `suc ((ƛ case (`suc `zero) (` Z) (`suc (plus · ` Z · ` S Z))) · two)
    —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
      `suc (case (`suc `zero) (two) (`suc (plus · ` Z · two)))
    —→⟨ ξ-suc (β-suc V-zero) ⟩
      `suc (`suc (plus · `zero · two))
    —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
      `suc (`suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
        · `zero · two))
    —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
      `suc (`suc ((ƛ case `zero (` Z) (`suc (plus · ` Z · ` S Z))) · two))
    —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
      `suc (`suc (case `zero (two) (`suc (plus · ` Z · two))))
    —→⟨ ξ-suc (ξ-suc β-zero) ⟩
     `suc (`suc (`suc (`suc `zero)))
    ∎
```




## Problem 3

Remember to indent all code by two spaces.

```agda
module Problem3 where
```

### Syntax

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

### Types

```agda
  data Type : Set where
    _⇒_   : Type → Type → Type
    `ℕ    : Type
```

### Identifiers

```agda
  Id : Set
  Id = String
```

### Contexts

```agda
  data Context : Set where
    ∅     : Context
    _,_⦂_ : Context → Id → Type → Context
```

### Terms

```agda
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
```

### Lookup

```agda
  data _∋_⦂_ : Context → Id → Type → Set where

    Z : ∀ {Γ x A}
        --------------------
      → Γ , x ⦂ A ∋ x ⦂ A

    S : ∀ {Γ x y A B}
      → x ≢ y
      → Γ ∋ x ⦂ A
        -----------------
      → Γ , y ⦂ B ∋ x ⦂ A
```

### Bidirectional type checking

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


### Type equality

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

### Prerequisites

```agda
  dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
  dom≡ refl = refl

  rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
  rng≡ refl = refl

  ℕ≢⇒ : ∀ {A B} → `ℕ ≢ A ⇒ B
  ℕ≢⇒ ()
```


### Unique lookup

```agda
  uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
  uniq-∋ Z Z                 =  refl
  uniq-∋ Z (S x≢y _)         =  ⊥-elim (x≢y refl)
  uniq-∋ (S x≢y _) Z         =  ⊥-elim (x≢y refl)
  uniq-∋ (S _ ∋x) (S _ ∋x′)  =  uniq-∋ ∋x ∋x′
```

### Unique synthesis

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
  ext∋ _   ¬∃ ⟨ A , S _ ⊢x ⟩  =  ¬∃ ⟨ A , ⊢x ⟩

  lookup :
      ∀ (Γ : Context) (x : Id)
      -----------------------
    → Dec (∃[ A ] Γ ∋ x ⦂ A)
  lookup ∅ x                        =  no  (λ ())
  lookup (Γ , y ⦂ B) x with x ≟ y
  ... | yes refl                    =  yes ⟨ B , Z ⟩
  ... | no x≢y with lookup Γ x
  ...             | no  ¬∃          =  no  (ext∋ x≢y ¬∃)
  ...             | yes ⟨ A , ⊢x ⟩  =  yes ⟨ A , S x≢y ⊢x ⟩
```

### Promoting negations

```agda
  ¬arg : ∀ {Γ A B L M}
    → Γ ⊢ L ↑ A ⇒ B
    → ¬ (Γ ⊢ M ↓ A)
      --------------------------
    → ¬ (∃[ B′ ] Γ ⊢ L · M ↑ B′)
  ¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′

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
      -----------------------
    → Dec (∃[ A ] Γ ⊢ M ↑ A )

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
```

### Example

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
```

A smart constructor, to make it easier to access a variable.
```
  S′ : ∀ {Γ x y A B}
     → {x≢y : False (x ≟ y)}
     → Γ ∋ x ⦂ A
       ------------------
     → Γ , y ⦂ B ∋ x ⦂ A

  S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x
```

Here is the result of typing two plus two on naturals:
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
```

We confirm that synthesis on the relevant term returns
natural as the type and the above derivation:
```agda
  _ : synthesize ∅ 2+2 ≡ yes ⟨ `ℕ , ⊢2+2 ⟩
  _ = refl
```
