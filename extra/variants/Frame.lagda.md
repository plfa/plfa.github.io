PCF with frames

Philip Wadler, 2 Aug 2022

```
module variants.Frame where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst; inspect)
     renaming ([_] to [[_]])
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
```

## Types

```
infixr 7 _⇒_
infix  8 `ℕ

data Type : Set where
  `ℕ : Type
  _⇒_ : Type → Type → Type

variable
  A B C : Type
```

* Type environments

```
infixl 6 _▷_

data Env : Set where
  ∅   : Env
  _▷_ : Env → Type → Env

variable
  Γ Δ : Env

infix  4 _∋_
infix  9 S_

data _∋_ : Env → Type → Set where

  Z :
      Γ ▷ A ∋ A

  S_ :
      Γ ∋ A
      ---------
    → Γ ▷ B ∋ A

variable
  x y : Γ ∋ A
```

## Terms

```
infix  4  _⊢_
infix  5  ƛ_
infix  5  μ_
infixl 6  _·_
infix  7  `suc_
infix  8  `_

data _⊢_ : Env → Type → Set where

  `_ :
      Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_ :
      Γ ▷ A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ :
      Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  `zero :
      ------
      Γ ⊢ `ℕ

  `suc_ :
      Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case :
      Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ ▷ `ℕ ⊢ A
      -----------
    → Γ ⊢ A

  μ_ :
     Γ ▷ A ⊢ A
     ---------
   → Γ ⊢ A

variable
  L M N V W : Γ ⊢ A
```

## Type class to convert naturals to an arbitrary type

```
variable
  n : ℕ

record OfNat (A : Set) (n : ℕ) : Set where
  field
    ofNat : A

open OfNat {{...}} public

instance
  OfNat-Z : OfNat (Γ ▷ A ∋ A) 0
  ofNat {{OfNat-Z}} = Z

instance
  OfNat-S : {{OfNat (Γ ∋ A) n}} → OfNat (Γ ▷ B ∋ A) (suc n)
  ofNat {{OfNat-S}} = S ofNat

#_ : ∀ {Γ : Env} {A : Type} (n : ℕ) → {{OfNat (Γ ∋ A) n}} → Γ ⊢ A
# n  =  ` ofNat
```

Testing!

```
_ : Γ ▷ `ℕ ⊢ `ℕ
_ = # 0

_ : Γ ▷ `ℕ ⇒ `ℕ ▷ `ℕ ⊢ `ℕ ⇒ `ℕ
_ = # 1

```

## Renaming maps, substitution maps, term maps

```
infix 4 _→ᴿ_
infix 4 _→ˢ_
infix 4 _→ᵀ_

_→ᴿ_ : Env → Env → Set
Γ →ᴿ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

_→ˢ_ : Env → Env → Set
Γ →ˢ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

_→ᵀ_ : Env → Env → Set
Γ →ᵀ Δ = ∀ {A} → Γ ⊢ A → Δ ⊢ A

variable
  ρ : Γ →ᴿ Δ
  σ : Γ →ˢ Δ
  θ : Γ →ᵀ Δ
```


## Renaming

```
ren▷ :
    (Γ →ᴿ Δ)
    ------------------
  → (Γ ▷ A) →ᴿ (Δ ▷ A)
ren▷ ρ Z      =  Z
ren▷ ρ (S x)  =  S (ρ x)

ren :
    (Γ →ᴿ Δ)
    --------
  → (Γ →ᵀ Δ)
ren ρ (` x)          =  ` (ρ x)
ren ρ (ƛ N)          =  ƛ (ren (ren▷ ρ) N)
ren ρ (L · M)        =  (ren ρ L) · (ren ρ M)
ren ρ `zero          =  `zero
ren ρ (`suc M)       =  `suc (ren ρ M)
ren ρ (case L M N)   =  case (ren ρ L) (ren ρ M) (ren (ren▷ ρ) N)
ren ρ (μ M)          =  μ (ren (ren▷ ρ) M)

lift : Γ →ᵀ (Γ ▷ A)
lift = ren S_
```

## Substitution

```
sub▷ :
    (Γ →ˢ Δ)
    ------------------
  → (Γ ▷ A) →ˢ (Δ ▷ A)
sub▷ σ Z      =  ` Z
sub▷ σ (S x)  =  lift (σ x)

sub :
    (Γ →ˢ Δ)
    --------
  → (Γ →ᵀ Δ)
sub σ (` x)          =  σ x
sub σ (ƛ N)          =  ƛ (sub (sub▷ σ) N)
sub σ (L · M)        =  (sub σ L) · (sub σ M)
sub σ `zero          =  `zero
sub σ (`suc M)       =  `suc (sub σ M)
sub σ (case L M N)   =  case (sub σ L) (sub σ M) (sub (sub▷ σ) N)
sub σ (μ M)          =  μ (sub (sub▷ σ) M)
```

Special case of substitution, used in beta rule
```
σ₀ :
    Γ ⊢ A
    ------------
  → (Γ ▷ A) →ˢ Γ
σ₀ M Z      =  M
σ₀ M (S x)  =  ` x

_[_] :
    Γ ▷ A ⊢ B
  → Γ ⊢ A
    ---------
  → Γ ⊢ B
_[_] N M =  sub (σ₀ M) N
```

## Values

```
data Value : (Γ ⊢ A) → Set where

  ƛ_ :
      (N : Γ ▷ A ⊢ B)
      ---------------
    → Value (ƛ N)

  `zero :
      Value {Γ} `zero

  `suc_ :
      Value V
      --------------
    → Value (`suc V)

  μ_ :
      (N : Γ ▷ A ⊢ A)
      ---------------
    → Value (μ N)

variable
  v : Value V
  w : Value W
```


Extract term from evidence that it is a value.
```
value : ∀ {Γ A} {V : Γ ⊢ A}
  → (v : Value V)
    -------------
  → Γ ⊢ A
value {V = V} v  =  V
```


Renaming preserves values
(not needed, but I wanted to check that automatic generalisation works)
```
ren-val :
    (ρ : Γ →ᴿ Δ)
  → Value V
    ------------------
  → Value (ren ρ V)
-- ren-val ρ (ƛ N)    =

ren-val ρ (ƛ N)     = ƛ (ren (ren▷ ρ) N)
ren-val ρ `zero     = `zero
ren-val ρ (`suc M)  = `suc (ren-val ρ M)
ren-val ρ (μ M)     = μ (ren (ren▷ ρ) M)
```

## Evaluation frames

```
infix  6 □·_
infix  6 _·□
infix  7 `suc□
infix  7 case□
infix  9 _⟦_⟧

data _⊢_=>_ : Env → Type → Type → Set where

  □·_ :
      Γ ⊢ A
      ---------------
    → Γ ⊢ A ⇒ B => B

  _·□ :
      {V : Γ ⊢ A ⇒ B}
    → Value V
      ----------
    → Γ ⊢ A => B

  `suc□ :
      -------------
      Γ ⊢ `ℕ => `ℕ

  case□ :
      Γ ⊢ A
    → Γ ▷ `ℕ ⊢ A
      -----------
    → Γ ⊢ `ℕ => A
```

The plug function inserts an expression into the hole of a frame.
```
_⟦_⟧ :
    Γ ⊢ A => B
  → Γ ⊢ A
    ----------
  → Γ ⊢ B
(□· M) ⟦ L ⟧        =  L · M
(v ·□) ⟦ M ⟧        =  value v · M
(`suc□) ⟦ M ⟧       =  `suc M
(case□ M N) ⟦ L ⟧   =  case L M N
```

## Reduction

```
infix 2 _—→_

data _—→_ : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  β-ƛ :
      Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  β-zero :
      ------------------
      case `zero M N —→ M

  β-suc :
      Value V
      ---------------------------
    → case (`suc V) M N —→ N [ V ]

  μ-· :
     Value V
     ----------------------------
   → (μ N) · V —→ (N [ μ N ]) · V

  μ-case :
     ---------------------------------------
     case (μ L) M N —→ case (L [ μ L ]) M N

  ξ-refl :
      {M′ N′ : Γ ⊢ B}
    → (E : Γ ⊢ A => B)
    → M′ ≡ E ⟦ M ⟧
    → N′ ≡ E ⟦ N ⟧
    → M —→ N
      --------
    → M′ —→ N′
```

Notation
```
pattern ξ E M—→N = ξ-refl E refl refl M—→N
```

## Reflexive and transitive closure of reduction

```
infix  1 begin_
infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Γ ⊢ A → Γ ⊢ A → Set where

  _∎ :
      (M : Γ ⊢ A)
      -----------
    → M —↠ M

  _—→⟨_⟩_ :
      (L : Γ ⊢ A)
    → {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : (M —↠ N) → (M —↠ N)
begin M—↠N = M—↠N
```

## Irreducible terms

Values are irreducible.  The auxiliary definition rearranges the
order of the arguments because it works better for Agda.
```
value-irreducible : Value V → ¬ (V —→ M)
value-irreducible v V—→M  =  nope V—→M v
  where
  nope : V —→ M → Value V → ⊥
  nope (β-ƛ v) ()
  nope (ξ `suc□ V—→M) (`suc w)  =  nope V—→M w
```

Variables are irreducible.
```
variable-irreducible :
    ------------
    ¬ (` x —→ M)
variable-irreducible (ξ-refl (□· M) () e x—→)
variable-irreducible (ξ-refl (v ·□) () e x—→)
variable-irreducible (ξ-refl `suc□ () e x—→)
variable-irreducible (ξ-refl (case□ M N) () e x—→)
```

## Progress

Every term that is well typed and closed is either
blame or a value or takes a reduction step.

```
data Progress : (∅ ⊢ A) → Set where

  step :
      L —→ M
      ----------
    → Progress L

  done :
      Value V
      ----------
    → Progress V

progress :
    (M : ∅ ⊢ A)
    -----------
  → Progress M

progress (ƛ N)                           =  done (ƛ N)
progress (L · M) with progress L
... | step L—→L′                         =  step (ξ (□· M) L—→L′)
... | done v with progress M
...     | step (M—→M′)                   =  step (ξ (v ·□) M—→M′)
...     | done w with v
...         | (ƛ N)                      =  step ((β-ƛ w))
...         | (μ N)                      =  step ((μ-· w))
progress `zero                           =  done `zero
progress (`suc M) with progress M
... | step (M—→M′)                       =  step (ξ (`suc□) M—→M′)
... | done v                             =  done (`suc v)
progress (case L M N) with progress L
... | step (L—→L′)                       =  step (ξ (case□ M N) L—→L′)
... | done v with v
...     | `zero                          =  step (β-zero)
...     | (`suc v)                       =  step ((β-suc v))
...     | (μ N)                          =  step (μ-case)
progress (μ N)                           =  done (μ N)
```


## Evaluation

Gas is specified by a natural number:
```
record Gas : Set where
  constructor gas
  field
    amount : ℕ
```
When our evaluator returns a term `N`, it will either give evidence that
`N` is a value, or indicate that blame occurred or it ran out of gas.
```
data Finished : (∅ ⊢ A) → Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N
```
Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished:
```
data Steps : ∅ ⊢ A → Set where

  steps :
      L —↠ M
    → Finished M
      ----------
    → Steps L
```
The evaluator takes gas and a term and returns the corresponding steps:
```
eval :
    Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero) L          =  steps (L ∎) out-of-gas
eval (gas (suc m)) L
    with progress L
... | done v               =  steps (L ∎) (done v)
... | step {M = M} L—→M
    with eval (gas m) M
... | steps M—↠N fin       =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```

# Example

Computing two plus two on naturals:
```agda
two : Γ ⊢ `ℕ
two = `suc `suc `zero

plus : Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∅ ⊢ `ℕ
2+2 = plus · two · two
```

Next, a sample reduction demonstrating that two plus two is four:
```agda
_ : 2+2 —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  —→⟨ ξ (□· two) (μ-· (`suc (`suc `zero))) ⟩
    (ƛ ƛ case (# 1) (# 0) (`suc (plus · # 0 · # 1))) · two · two
  —→⟨ ξ (□· two) (β-ƛ (`suc (`suc `zero))) ⟩
    (ƛ case two (# 0) (`suc (plus · # 0 · # 1))) · two
  —→⟨ β-ƛ (`suc (`suc `zero)) ⟩
    case two two (`suc (plus · # 0 · two))
  —→⟨ β-suc (`suc `zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ `suc□ (ξ (□· two) (μ-· (`suc `zero))) ⟩
    `suc ((ƛ ƛ case (# 1) (# 0) (`suc (plus · # 0 · # 1))) · `suc `zero · two)
  —→⟨ ξ `suc□ (ξ (□· two) (β-ƛ (`suc `zero))) ⟩
    `suc ((ƛ case (`suc `zero) (# 0) (`suc (plus · # 0 · # 1))) · two)
  —→⟨ ξ `suc□ (β-ƛ (`suc (`suc `zero))) ⟩
    `suc case (`suc `zero) two (`suc (plus · # 0 · two))
  —→⟨ ξ `suc□ (β-suc `zero) ⟩
    `suc `suc (plus · `zero · two)
  —→⟨ ξ `suc□ (ξ `suc□ (ξ (□· two) (μ-· `zero))) ⟩
    `suc `suc ((ƛ ƛ case (# 1) (# 0) (`suc (plus · # 0 · # 1))) · `zero · two)
  —→⟨ ξ `suc□ (ξ `suc□ (ξ (□· two) (β-ƛ `zero))) ⟩
    `suc `suc ((ƛ case `zero (# 0) (`suc (plus · # 0 · # 1))) · two)
  —→⟨ ξ `suc□ (ξ `suc□ (β-ƛ (`suc (`suc `zero)))) ⟩
    `suc `suc (case `zero (two) (`suc (plus · # 0 · two)))
  —→⟨ ξ `suc□ (ξ `suc□ β-zero) ⟩
    `suc `suc `suc `suc `zero
  ∎
```
