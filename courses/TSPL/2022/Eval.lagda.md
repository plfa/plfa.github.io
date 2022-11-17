---
title     : "Simply typed lambda calculus with evaluation contexts"
permalink : /TSPL/2022/Eval/
---

Siek, Thiemann, and Wadler
10 November 2022

```
module Eval where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
```

## Types

```
infixr 7 _⇒_
infix  8 `ℕ

data Type : Set where
  `ℕ : Type
  _⇒_ : Type → Type → Type
```

* Contexts and Variables

```
infixl 6 _▷_

data Context : Set where
  ∅   : Context
  _▷_ : Context → Type → Context

infix  4 _∋_
infix  9 S_

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ----------
    → Γ ▷ A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ ▷ B ∋ A
```

## Terms

```
infix  4 _⊢_
infixl 6 _·_
infix  8 `_

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
    → Γ ▷ A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  `zero : ∀ {Γ}
      ---------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ ▷ `ℕ ⊢ A
      ----------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ ▷ A ⊢ A
      ---------
    → Γ ⊢ A
```

### Test examples

First, computing two plus two on naturals:
```agda
pattern two = `suc `suc `zero
pattern plus = μ ƛ ƛ (case (` S Z) (` Z) (`suc (` S S S Z · ` Z · ` S Z)))

2+2 : ∅ ⊢ `ℕ
2+2 = plus · two · two
```

Next, computing two plus two on Church numerals:
```agda
pattern twoᶜ = ƛ ƛ (` S Z · (` S Z · ` Z))
pattern plusᶜ = ƛ ƛ ƛ ƛ (` S S S Z · ` S Z · (` S S Z · ` S Z · ` Z))
pattern sucᶜ = ƛ `suc (` Z)

2+2ᶜ : ∅ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```


## Renaming maps, substitution maps, term maps

```
_→ʳ_ : Context → Context → Set
Γ →ʳ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

_→ˢ_ : Context → Context → Set
Γ →ˢ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

_→ᵗ_ : Context → Context → Set
Γ →ᵗ Δ = ∀ {A} → Γ ⊢ A → Δ ⊢ A
```


## Renaming

Extension of renaming maps
```
ren▷ : ∀ {Γ Δ A}
  → (Γ →ʳ Δ)
    ----------------------------
  → ((Γ ▷ A) →ʳ (Δ ▷ A))
ren▷ ρ Z      =  Z
ren▷ ρ (S x)  =  S (ρ x)

ren : ∀ {Γ Δ}
  → (Γ →ʳ Δ)
    --------
  → (Γ →ᵗ Δ)
ren ρ (` x)          = ` (ρ x)
ren ρ (ƛ N)          =  ƛ (ren (ren▷ ρ) N)
ren ρ (L · M)        =  (ren ρ L) · (ren ρ M)
ren ρ `zero          = `zero
ren ρ (`suc M)       = `suc (ren ρ M)
ren ρ (case L M N)   = case (ren ρ L) (ren ρ M) (ren (ren▷ ρ) N)
ren ρ (μ N)          = μ (ren (ren▷ ρ) N)

lift : ∀ {Γ : Context} {A : Type} → Γ →ᵗ (Γ ▷ A)
lift = ren S_
```

## Substitution

```
sub▷ : ∀ {Γ Δ A}
  → (Γ →ˢ Δ)
    --------------------------
  → ((Γ ▷ A) →ˢ (Δ ▷ A))
sub▷ σ Z      =  ` Z
sub▷ σ (S x)  =  lift (σ x)

sub : ∀ {Γ Δ : Context}
  → (Γ →ˢ Δ)
    --------
  → (Γ →ᵗ Δ)
sub σ (` x)          =  σ x
sub σ (ƛ  N)         =  ƛ (sub (sub▷ σ) N)
sub σ (L · M)        =  (sub σ L) · (sub σ M)
sub ρ `zero          = `zero
sub ρ (`suc M)       = `suc (sub ρ M)
sub ρ (case L M N)   = case (sub ρ L) (sub ρ M) (sub (sub▷ ρ) N)
sub ρ (μ N)          = μ (sub (sub▷ ρ) N)
```

Special case of substitution, used in beta rule
```
σ₀ : ∀ {Γ A} → (M : Γ ⊢ A) → (Γ ▷ A) →ˢ Γ
σ₀ M Z      =  M
σ₀ M (S x)  =  ` x

_[_] : ∀ {Γ A B}
        → Γ ▷ A ⊢ B
        → Γ ⊢ A
          ---------
        → Γ ⊢ B
_[_] {Γ} {A} N M =  sub {Γ ▷ A} {Γ} (σ₀ M) N
```

## Values

```
data Value {Γ} : ∀ {A} → Γ ⊢ A → Set where

  ƛ_ : ∀{A B}
    → (N : Γ ▷ A ⊢ B)
      ---------------
    → Value (ƛ N)

  `zero :
      -----------
      Value `zero

  `suc_ : ∀ {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)
```


Extract term from evidence that it is a value.
```
value : ∀ {Γ A} {V : Γ ⊢ A}
  → (v : Value V)
    -------------
  → Γ ⊢ A
value {V = V} v  =  V
```

## Frames (aka Evaluation Contexts)

Here is how evaluation contexts are written informally:

    E ::= □ | E · M | V · E | `suc E | `case E M N

    M —→ M′
    ------------- ξ
    E[M] —→ E[M′]

Since now values uniquely dermine the underlying term, we can now write, for instance

    (ƛ N) ·[ E ]

instead of

    _·[_] { ƛ N } V-ƛ E

```
infix  4 _⊢_==>_
infix  6 [_]·_
infix  6 _·[_]
infix  6 `suc[_]
infix  6 case[_]
infix  7 _⟦_⟧

data _⊢_==>_ (Γ : Context) (C : Type) : Type → Set where

  □ : Γ ⊢ C ==> C

  [_]·_ : ∀ {A B}
    → Γ ⊢ C ==> (A ⇒ B)
    → Γ ⊢ A
      ---------------
    → Γ ⊢ C ==> B

  _·[_] : ∀ {A B}{V : Γ ⊢ A ⇒ B}
    → Value V
    → Γ ⊢ C ==> A
      -----------
    → Γ ⊢ C ==> B

  `suc[_] :
      Γ ⊢ C ==> `ℕ
      ------------
    → Γ ⊢ C ==> `ℕ

  case[_] : ∀ {A}
    → Γ ⊢ C ==> `ℕ
    → Γ ⊢ A
    → Γ ▷ `ℕ ⊢ A
      -----------
    → Γ ⊢ C ==> A
```

The plug function inserts an expression into the hole of a frame.
```
_⟦_⟧ : ∀{Γ A B}
  → Γ ⊢ A ==> B
  → Γ ⊢ A
    -----
  → Γ ⊢ B
□ ⟦ M ⟧                 =  M
([ E ]· M) ⟦ L ⟧        =  E ⟦ L ⟧ · M
(v ·[ E ]) ⟦ M ⟧        =  value v · E ⟦ M ⟧
(`suc[ E ]) ⟦ M ⟧       =  `suc (E ⟦ M ⟧)
(case[ E ] M N) ⟦ L ⟧   =  case (E ⟦ L ⟧) M N
```

## Reduction

```
infix 2 _↦_ _—→_

data _↦_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  β-λ : ∀ {Γ A B} {N : Γ ▷ A ⊢ B} {W : Γ ⊢ A}
    → Value W
      -------------------
    → (ƛ N) · W ↦ N [ W ]

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ▷ `ℕ ⊢ A}
      ------------------
    → case `zero M N ↦ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ ▷ `ℕ ⊢ A}
    → Value V
      ---------------------------
    → case (`suc V) M N ↦ N [ V ]

  β-μ : ∀ {Γ A} {N : Γ ▷ A ⊢ A}
      ---------------
    → μ N ↦ N [ μ N ]



data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξξ : ∀ {Γ A B} {M N : Γ ⊢ A} {M′ N′ : Γ ⊢ B}
    → ( E : Γ ⊢ A ==> B)
    → M′ ≡ E ⟦ M ⟧
    → N′ ≡ E ⟦ N ⟧
    → M ↦ N
      --------
    → M′ —→ N′
```

Notation
```
pattern ξ E M—→N = ξξ E refl refl M—→N
```

## Reflexive and transitive closure of reduction

```
infix  1 begin_
infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀{Γ A} → Γ ⊢ A → Γ ⊢ A → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A} → (M —↠ N) → (M —↠ N)
begin M—↠N = M—↠N
```

## Irreducible terms

Values are irreducible.  The auxiliary definition rearranges the
order of the arguments because it works better for Agda.
```
value-irreducible : ∀ {Γ A} {V M : Γ ⊢ A}
  → Value V
    ----------
  → ¬ (V —→ M)
value-irreducible v V—→M = nope V—→M v
   where
   nope : ∀ {Γ A} {V M : Γ ⊢ A}
     → V —→ M
     → Value V
       -------
     → ⊥
   nope (ξ □ (β-λ v)) ()
   nope (ξ □ β-zero) ()
   nope (ξ □ (β-suc x)) ()
   nope (ξ □ β-μ) ()
   nope (ξ `suc[ E ] V↦M) (`suc v)  =  nope (ξ E V↦M) v
```

```
redex : ∀{Γ A} (M : Γ ⊢ A) → Set
redex M = ∃[ N ] (M ↦ N)
```

## Progress

Every term that is well typed and closed is either
blame or a value or takes a reduction step.

```
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
progress (ƛ N)                           =  done (ƛ N)
progress (L · M) with progress L
... | step (ξ E L↦L′)                    =  step (ξ ([ E ]· M) L↦L′)
... | done (ƛ N) with progress M
...     | step (ξ E M↦M′)                =  step (ξ ((ƛ N) ·[ E ]) M↦M′)
...     | done w                         =  step (ξ □ (β-λ w))
progress `zero                           =  done `zero
progress (`suc M) with progress M
... | step (ξ E M↦M′)                    =  step (ξ (`suc[ E ]) M↦M′)
... | done v                             =  done (`suc v)
progress (case L M N) with progress L
... | step (ξ E L↦L′)                    =  step (ξ (case[ E ] M N) L↦L′)
... | done `zero                         =  step (ξ □ β-zero)
... | done (`suc v)                      =  step (ξ □ (β-suc v))
progress (μ M)                           =  step (ξ □ β-μ)
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
`N` is a value, or indicate that it ran out of gas.
```
data Finished {A} : (∅ ⊢ A) → Set where

   done : ∀ {N : ∅ ⊢ A}
     → Value N
       ----------
     → Finished N

   out-of-gas : {N : ∅ ⊢ A}
       ----------
     → Finished N
```
Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished:
```
data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
```
The evaluator takes gas and a term and returns the corresponding steps:
```
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

```
_ : 2+2 —↠ `suc `suc `suc `suc `zero
_ =
  begin
    2+2
  —→⟨ ξ ([ [ □ ]· two ]· two) β-μ ⟩
    (ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z))) · two · two
  —→⟨ ξ ([ □ ]· two) (β-λ (`suc (`suc `zero))) ⟩
    (ƛ case two (` Z) (`suc (plus · ` Z · ` S Z))) · two
  —→⟨ ξ □ (β-λ (`suc (`suc `zero))) ⟩
    case two two (`suc (plus · ` Z · two))
  —→⟨ ξ □ (β-suc (`suc `zero)) ⟩
    `suc (plus · (`suc `zero) · two)
  —→⟨ ξ `suc[ [ [ □ ]· (`suc `zero) ]· two ] β-μ ⟩
    `suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z))) · (`suc `zero) · two)
  —→⟨ ξ `suc[ [ □ ]· two ] (β-λ (`suc `zero)) ⟩
    `suc ((ƛ case (`suc `zero) (` Z) (`suc (plus · ` Z · ` S Z))) · two)
  —→⟨ ξ `suc[ □ ] (β-λ (`suc (`suc `zero))) ⟩
    `suc (case (`suc `zero) two (`suc (plus · ` Z · two)))
  —→⟨ ξ `suc[ □ ] (β-suc `zero) ⟩
    `suc `suc (plus · `zero · two)
  —→⟨ ξ `suc[ `suc[ [ [ □ ]· `zero ]· two ] ] β-μ ⟩
    `suc `suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z))) · `zero · two)
  —→⟨ ξ `suc[ `suc[ [ □ ]· two ] ] (β-λ `zero) ⟩
    `suc `suc ((ƛ case `zero (` Z) (`suc (plus · ` Z · ` S Z))) · two)
  —→⟨ ξ `suc[ `suc[ □ ] ] (β-λ (`suc (`suc `zero))) ⟩
    `suc `suc (case `zero two (`suc (plus · ` Z · two)))
  —→⟨ ξ `suc[ `suc[ □ ] ] β-zero ⟩
    `suc `suc two
  ∎

_ : 2+2ᶜ —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ ([ [ [ □ ]· twoᶜ ]· sucᶜ ]· `zero) (β-λ (ƛ ƛ (` S Z · (` S Z · ` Z)))) ⟩
    (ƛ ƛ ƛ (twoᶜ · ` S Z · (` S (S Z) · ` S Z · ` Z))) · twoᶜ · sucᶜ · `zero
  —→⟨ ξ ([ [ □ ]· sucᶜ ]· `zero) (β-λ (ƛ ƛ (` S Z · (` S Z · ` Z)))) ⟩
    (ƛ ƛ (twoᶜ · ` S Z · (twoᶜ · ` S Z · ` Z))) · sucᶜ · `zero
  —→⟨ ξ ([ □ ]· `zero) (β-λ (ƛ (`suc (` Z)))) ⟩
    (ƛ (twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` Z))) · `zero
  —→⟨ ξ □ (β-λ `zero) ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ ([ □ ]· (twoᶜ · sucᶜ · `zero)) (β-λ (ƛ (`suc (` Z)))) ⟩
    (ƛ (sucᶜ · (sucᶜ · ` Z))) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ ((ƛ (sucᶜ · (sucᶜ · ` Z))) ·[ [ □ ]· `zero ]) (β-λ (ƛ (`suc (` Z)))) ⟩
    (ƛ (sucᶜ · (sucᶜ · ` Z))) · ((ƛ (sucᶜ · (sucᶜ · ` Z))) · `zero)
  —→⟨ ξ ((ƛ (sucᶜ · (sucᶜ · ` Z))) ·[ □ ]) (β-λ `zero) ⟩
    (ƛ (sucᶜ · (sucᶜ · ` Z))) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ ((ƛ (sucᶜ · (sucᶜ · ` Z))) ·[ (ƛ (`suc (` Z))) ·[ □ ] ]) (β-λ `zero) ⟩
    (ƛ (sucᶜ · (sucᶜ · ` Z))) · (sucᶜ · (`suc `zero))
  —→⟨ ξ ((ƛ (sucᶜ · (sucᶜ · ` Z))) ·[ □ ]) (β-λ (`suc `zero)) ⟩
    (ƛ (sucᶜ · (sucᶜ · ` Z))) · two
  —→⟨ ξ □ (β-λ (`suc (`suc `zero))) ⟩
    sucᶜ · (sucᶜ · two)
  —→⟨ ξ ((ƛ (`suc (` Z))) ·[ □ ]) (β-λ (`suc (`suc `zero))) ⟩
    sucᶜ · (`suc two)
  —→⟨ ξ □ (β-λ (`suc (`suc (`suc `zero)))) ⟩
    (`suc (`suc two))
  ∎
```
