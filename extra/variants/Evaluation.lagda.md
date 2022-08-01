STLC with Nested evaluation contexts

Siek, Thiemann, and Wadler

```
module variants.Evaluation where

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
```

## Terms

```
infix   4 _⊢_
infix   5 ƛ_
infix   5 μ_
infixl  6 _·_
infix   7 `suc
infix   8 `_

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

  `suc :
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

## Renaming maps, substitution maps, term maps

```
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

  `suc :
      Value V
      --------------
    → Value (`suc V)

  μ_ :
      (N : Γ ▷ A ⊢ B)
      ---------------
    → Value (ƛ N)

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

## Evaluation contexts

```
infix  6 [_]·_
infix  6 _·[_]
infix  7 `suc[_]
infix  7 case[_]
infix  9 _⟦_⟧

data _⊢_=>_ : Env → Type → Type → Set where

  □ : Γ ⊢ C => C

  [_]·_ :
      Γ ⊢ C => (A ⇒ B)
    → Γ ⊢ A
      ---------------
    → Γ ⊢ C => B

  _·[_] :
      {V : Γ ⊢ A ⇒ B}
    → Value V
    → Γ ⊢ C => A
      ----------------
    → Γ ⊢ C => B

  `suc[_] :
      Γ ⊢ C => `ℕ
      -----------
    → Γ ⊢ C => `ℕ

  case[_] :
      Γ ⊢ C => `ℕ
    → Γ ⊢ A
    → Γ ▷ `ℕ ⊢ A
      -----------
    → Γ ⊢ C => A
```

The plug function inserts an expression into the hole of a frame.
```
_⟦_⟧ :
    Γ ⊢ A => B
  → Γ ⊢ A
    ----------
  → Γ ⊢ B
□ ⟦ M ⟧                 =  M
([ E ]· M) ⟦ L ⟧        =  E ⟦ L ⟧ · M
(v ·[ E ]) ⟦ M ⟧        =  value v · E ⟦ M ⟧
(`suc[ E ]) ⟦ M ⟧       =  `suc (E ⟦ M ⟧)
(case[ E ] M N) ⟦ L ⟧   =  case (E ⟦ L ⟧) M N
```

Composition of two frames
```
_∘_ :
    Γ ⊢ B => C
  → Γ ⊢ A => B
    ----------
  → Γ ⊢ A => C
□ ∘ F                 =  F
([ E ]· M) ∘ F        =  [ E ∘ F ]· M
(v ·[ E ]) ∘ F        =  v ·[ E ∘ F ]
(`suc[ E ]) ∘ F       =  `suc[ E ∘ F ]
(case[ E ] M N) ∘ F   =  case[ E ∘ F ] M N
```

Composition and plugging
```
∘-lemma : 
    (E : Γ ⊢ B => C)
  → (F : Γ ⊢ A => B)
  → (P : Γ ⊢ A)
    -----------------------------
  → E ⟦ F ⟦ P ⟧ ⟧ ≡ (E ∘ F) ⟦ P ⟧
∘-lemma □ F P                                         =  refl
∘-lemma ([ E ]· M) F P         rewrite ∘-lemma E F P  =  refl
∘-lemma (v ·[ E ]) F P         rewrite ∘-lemma E F P  =  refl
∘-lemma (`suc[ E ]) F P        rewrite ∘-lemma E F P  =  refl
∘-lemma (case[ E ] M N) F P    rewrite ∘-lemma E F P  =  refl
```

## Reduction

```
infix 2 _↦_ _—→_

data _↦_ : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  β-ƛ :
      Value V
      --------------------
    → (ƛ N) · V ↦ N [ V ]

  β-zero :
      ------------------
      case `zero M N ↦ M

  β-suc :
      Value V
      ---------------------------
    → case (`suc V) M N ↦ N [ V ]

  β-μ :
     Value V
     -------------------------
   → (μ N) · V ↦ (N [ μ N ]) · V

data _—→_ : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-refl : 
      {M′ N′ : Γ ⊢ B}
    → (E : Γ ⊢ A => B)
    → M′ ≡ E ⟦ M ⟧
    → N′ ≡ E ⟦ N ⟧
    → M ↦ N
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
value-irreducible : ∀ {Γ A} {V M : Γ ⊢ A} → Value V → ¬ (V —→ M)
value-irreducible v V—→M  =  nope V—→M v
   where
   nope : ∀ {Γ A} {V M : Γ ⊢ A} → V —→ M → Value V → ⊥
   nope (ξ `suc[ E ] (β-ƛ v))   (`suc w)  =  nope (ξ E (β-ƛ v)) w
   nope (ξ `suc[ E ] β-zero)    (`suc w)  =  nope (ξ E β-zero) w
   nope (ξ `suc[ E ] (β-suc v)) (`suc w)  =  nope (ξ E (β-suc v)) w
   nope (ξ `suc[ E ] (β-μ v))   (`suc w)  =  nope (ξ E (β-μ v)) w
```

-- Variables are irreducible.
-- ```
-- variable-irreducible : ∀ {Γ A} {x : Γ ∋ A} {N : Γ ⊢ A}
--     ------------
--   → ¬ (` x —→ N)
-- variable-irreducible (ξ □ ())
-- ```

-- Boxes are irreducible (at the top level)
-- ```
-- box-irreducible : ∀ {Γ G} {M : Γ ⊢ G} {N : Γ ⊢ ★}
--   → (g : Ground G)
--     --------------
--   → ¬ (M ⇑ g ↦ N)
-- box-irreducible g ()
-- ```

-- Blame is irreducible.
-- ```
-- blame-irreducible : ∀ {Γ A} {M′ : Γ ⊢ A}  → ¬ (blame —→ M′)
-- blame-irreducible (ξ □ ())
-- ```

-- ## Progress

-- Every term that is well typed and closed is either
-- blame or a value or takes a reduction step.

-- ```
-- data Progress {A} : (∅ ⊢ A) → Set where

--   blame : ∀ {B}
--    → (E : Frame ∅ B A)
--      ---------------------
--    → Progress (E ⟦ blame ⟧)

--   step : ∀ {M N : ∅ ⊢ A}
--     → M —→ N
--       ----------
--     → Progress M

--   done : ∀ {M : ∅ ⊢ A}
--     → Value M
--       ----------
--     → Progress M

-- progress± : ∀ {A B} {V : ∅ ⊢ A}
--   → (v : Value V)
--   → (±p : A => B)
--     --------------------
--   → ∃[ M ](V ⟨ ±p ⟩ ↦ M)
-- progress± v ±p with split ±p in e
-- progress± v     _ | id                   =  _ , ident e v
-- progress± (ƛ _) _ | _ ⇒ _                =  _ , wrap e
-- progress± v       (+ _ ⇑ g) | other      =  _ , expand v g
-- progress± (v ⇑ g) (- _ ⇑ h) | other
--     with ground g ≡? ground h
-- ... | yes refl rewrite uniqueG g h       =  _ , collapse v h
-- ... | no  G≢H                            =  _ , collide v g h G≢H

-- progress : ∀ {A}
--   → (M : ∅ ⊢ A)
--     -----------
--   → Progress M

-- progress (ƛ N)                           =  done (ƛ N)
-- progress (L · M) with progress L
-- ... | blame E                            =  blame ([ E ]· M)
-- ... | step (ξ E L↦L′)                    =  step (ξ ([ E ]· M) L↦L′)
-- ... | done (ƛ N) with progress M
-- ...     | blame E                        =  blame ((ƛ N) ·[ E ])
-- ...     | step (ξ E M↦M′)                =  step (ξ ((ƛ N) ·[ E ]) M↦M′)
-- ...     | done w                         =  step (ξ □ (β w))
-- progress ($ k)                           =  done ($ k)
-- progress (L ⦅ _⊕_ ⦆ M) with progress L
-- ... | blame E                            =  blame ([ E ]⦅ _⊕_ ⦆ M)
-- ... | step (ξ E L↦L′)                    =  step (ξ ([ E ]⦅ _⊕_ ⦆ M) L↦L′)
-- ... | done ($ k) with progress M
-- ...     | blame E                        =  blame (($ k) ⦅ _⊕_ ⦆[ E ])
-- ...     | step (ξ E M↦M′)                =  step (ξ (($ k) ⦅ _⊕_ ⦆[ E ]) M↦M′)
-- ...     | done ($ k′)                    =  step (ξ □ δ)
-- progress (M ⇑ g) with progress M
-- ... | blame E                            =  blame ([ E ]⇑ g)
-- ... | step (ξ E M↦M′)                    =  step (ξ ([ E ]⇑ g) M↦M′)
-- ... | done v                             =  done (v ⇑ g)
-- progress (M ⟨ ±p ⟩) with progress M
-- ... | blame E                            =  blame ([ E ]⟨ ±p ⟩)
-- ... | step (ξ E M↦M′)                    =  step (ξ ([ E ]⟨ ±p ⟩) M↦M′)
-- ... | done v with progress± v ±p
-- ...     | _ , V⟨±p⟩↦N                    =  step (ξ □ V⟨±p⟩↦N)
-- progress blame                           =  blame □
-- ```


-- ## Evaluation

-- Gas is specified by a natural number:
-- ```
-- record Gas : Set where
--   constructor gas
--   field
--     amount : ℕ
-- ```
-- When our evaluator returns a term `N`, it will either give evidence that
-- `N` is a value, or indicate that blame occurred or it ran out of gas.
-- ```
-- data Finished {A} : (∅ ⊢ A) → Set where

--    done : ∀ {N : ∅ ⊢ A}
--      → Value N
--        ----------
--      → Finished N

--    blame : ∀ {B}
--      → (E : Frame ∅ B A)
--        ---------------------
--      → Finished (E ⟦ blame ⟧)

--    out-of-gas : {N : ∅ ⊢ A}
--        ----------
--      → Finished N
-- ```
-- Given a term `L` of type `A`, the evaluator will, for some `N`, return
-- a reduction sequence from `L` to `N` and an indication of whether
-- reduction finished:
-- ```
-- data Steps {A} : ∅ ⊢ A → Set where

--   steps : {L N : ∅ ⊢ A}
--     → L —↠ N
--     → Finished N
--       ----------
--     → Steps L
-- ```
-- The evaluator takes gas and a term and returns the corresponding steps:
-- ```
-- eval : ∀ {A}
--   → Gas
--   → (L : ∅ ⊢ A)
--     -----------
--   → Steps L
-- eval (gas zero) L          =  steps (L ∎) out-of-gas
-- eval (gas (suc m)) L
--     with progress L
-- ... | done v               =  steps (L ∎) (done v)
-- ... | blame E              =  steps (L ∎) (blame E)
-- ... | step {L} {M} L—→M
--     with eval (gas m) M
-- ... | steps M—↠N fin       =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
-- ```

-- ## Type erasure

-- ```
-- infix 6 _≤★

-- pattern  _≤★ ι   =  id ⇑ ($ ι)
-- pattern  ★⇒★≤★   =  id ⇑ ★⇒★

-- infix  6 _·★_
-- infix  6 _⦅_⦆★_
-- infix  8 $★_

-- pattern  ƛ★_ N          =  (ƛ N) ⟨ + ★⇒★≤★ ⟩
-- pattern  _·★_ L M       =  (L ⟨ - ★⇒★≤★ ⟩) · M
-- pattern  $★_ {ι = ι} k  =  $ k ⇑ $ ι
-- pattern  _⦅_⦆★_ {ι = ι} {ι′} {ι″} M _⊕_ N
--   =  ((M ⟨ - ι ≤★ ⟩) ⦅ _⊕_ ⦆ (N ⟨ - ι′ ≤★ ⟩)) ⟨ + ι″ ≤★ ⟩

-- data Static : ∀ {Γ A} → (Γ ⊢ A) → Set where

--   `_ : ∀ {Γ A}
--     → (x : Γ ∋ A)
--       ------------
--     → Static (` x)

--   ƛ_ : ∀ {Γ A B} {N : Γ ▷ A ⊢ B}
--     → Static N
--       ------------
--     → Static (ƛ N)

--   _·_ : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
--     → Static L
--     → Static M
--       --------------
--     → Static (L · M)

--   $_ : ∀ {Γ ι}
--     → (k : rep ι)
--       -------------------
--     → Static {Γ = Γ} ($ k)

--   _⦅_⦆_ : ∀ {Γ ι ι′ ι″} {M : Γ ⊢ $ ι} {N : Γ ⊢ $ ι′}
--     → Static M
--     → (_⊕_ : rep ι → rep ι′ → rep ι″)
--     → Static N
--       --------------------
--     → Static (M ⦅ _⊕_ ⦆ N)

-- static : ∀ {Γ A} {M : Γ ⊢ A}
--   → (m : Static M)
--     -------------
--   → Γ ⊢ A
-- static {M = M} m  =  M

-- ⌈_⌉ᴳ : Env → Env
-- ⌈ ∅ ⌉ᴳ = ∅
-- ⌈ Γ ▷ A ⌉ᴳ = ⌈ Γ ⌉ᴳ ▷ ★

-- ⌈_⌉ˣ : ∀ {Γ A} → (Γ ∋ A) → (⌈ Γ ⌉ᴳ ∋ ★)
-- ⌈ Z ⌉ˣ          = Z
-- ⌈ S x ⌉ˣ        = S ⌈ x ⌉ˣ

-- ⌈_⌉ : ∀ {Γ A} {M : Γ ⊢ A} → Static M → (⌈ Γ ⌉ᴳ ⊢ ★)
-- ⌈ ` x ⌉          =  ` ⌈ x ⌉ˣ
-- ⌈ ƛ N ⌉          =  ƛ★ ⌈ N ⌉
-- ⌈ L · M ⌉        =  ⌈ L ⌉ ·★ ⌈ M ⌉
-- ⌈ $ k ⌉          =  $★ k
-- ⌈ M ⦅ _⊕_ ⦆ N ⌉  =  ⌈ M ⌉ ⦅ _⊕_ ⦆★ ⌈ N ⌉
-- ```

-- ## Examples

-- The following abbreviations cause Agda to produce more readable output
-- when using `eval`.  In particular, the specialised `$ℕ★_`, `$𝔹★_`, and
-- `_⦅_⦆ℕ★_` lead to more readable results than the generic `$★_` and
-- `_⦅_⦆★_`.  After the output is produced, rewriting `ℕ★` and `𝔹★`
-- yields the more generic operators, which are fine for input.

-- ```
-- pattern  $ℕ      =  $ ′ℕ
-- pattern  $𝔹      =  $ ′𝔹
-- pattern  ℕ≤★     =  id ⇑ $ℕ
-- pattern  𝔹≤★     =  id ⇑ $𝔹
-- pattern  ℕ⇒ℕ≤★   =  ℕ≤★ ⇒ ℕ≤★ ⇑ ★⇒★

-- infix  6 _⦅_⦆ℕ★_
-- infix  8 $ℕ★_
-- infix  8 $𝔹★_

-- pattern  $ℕ★_ k          =  $ k ⇑ $ℕ
-- pattern  $𝔹★_ k          =  $ k ⇑ $𝔹
-- pattern  _⦅_⦆ℕ★_ M _⊕_ N
--   =  ((M ⟨ - ℕ≤★ ⟩) ⦅ _⊕_ ⦆ (N ⟨ - ℕ≤★ ⟩)) ⟨ + ℕ≤★ ⟩

-- inc     :  ∅ ⊢ $ℕ ⇒ $ℕ
-- inc     =  ƛ (` Z ⦅ _+_ ⦆ $ 1)

-- Inc     :  Static inc
-- Inc     =  ƛ (` Z ⦅ _+_ ⦆ $ 1)

-- inc★    :  ∅ ⊢ ★
-- inc★    =  ⌈ Inc ⌉

-- inc★′   :  ∅ ⊢ ★
-- inc★′   =  inc ⟨ + ℕ⇒ℕ≤★ ⟩

-- inc2—↠3  : inc · ($ 2) —↠ $ 3
-- inc2—↠3  =
--   begin
--     (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · $ 2
--   —→⟨ ξ □ (β ($ 2)) ⟩
--     $ 2 ⦅ _+_ ⦆ $ 1
--   —→⟨ ξ □ δ ⟩ $ 3
--   ∎

-- inc★2★—↠3★  : inc★ ·★ ($★ 2) —↠ $★ 3
-- inc★2★—↠3★  =
--   begin
--     (ƛ★ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ·★ $ℕ★ 2
--   —→⟨ ξ ([ [ □ ]⟨ - ★⇒★≤★ ⟩ ]· $ℕ★ 2) (expand (ƛ _) ★⇒★) ⟩
--     ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⟨ + id ⟩ ⇑ ★⇒★) ·★ $ℕ★ 2
--   —→⟨ ξ ([ [ [ □ ]⇑ ★⇒★ ]⟨ - ★⇒★≤★ ⟩ ]· $ℕ★ 2) (ident refl (ƛ _)) ⟩
--     ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⇑ ★⇒★) ·★ $ℕ★ 2
--   —→⟨ ξ ([ □ ]· $ℕ★ 2) (collapse (ƛ _) ★⇒★) ⟩
--     ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⟨ - id ⟩) · $ℕ★ 2
--   —→⟨ ξ ([ □ ]· $ℕ★ 2) (ident refl (ƛ _)) ⟩
--     (ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) · $ℕ★ 2
--   —→⟨ ξ □ (β ($ℕ★ 2)) ⟩
--     $ℕ★ 2 ⦅ _+_ ⦆ℕ★ $ℕ★ 1
--   —→⟨ ξ [ [ □ ]⦅ _+_ ⦆ ($ℕ★ 1 ⟨ - ℕ≤★ ⟩) ]⟨ + ℕ≤★ ⟩ (collapse ($ 2) $ℕ) ⟩
--     ($ 2 ⟨ - id ⟩) ⦅ _+_ ⦆ ($ℕ★ 1 ⟨ - ℕ≤★ ⟩) ⟨ + ℕ≤★ ⟩
--   —→⟨ ξ [ [ □ ]⦅ _+_ ⦆ ($ℕ★ 1 ⟨ - ℕ≤★ ⟩) ]⟨ + ℕ≤★ ⟩ (ident refl ($ 2)) ⟩
--     $ 2 ⦅ _+_ ⦆ ($ℕ★ 1 ⟨ - ℕ≤★ ⟩) ⟨ + ℕ≤★ ⟩
--   —→⟨ ξ [ $ 2 ⦅ _+_ ⦆[ □ ] ]⟨ + ℕ≤★ ⟩ (collapse ($ 1) $ℕ) ⟩
--     $ 2 ⦅ _+_ ⦆ ($ 1 ⟨ - id ⟩) ⟨ + ℕ≤★ ⟩
--   —→⟨ ξ [ $ 2 ⦅ _+_ ⦆[ □ ] ]⟨ + ℕ≤★ ⟩ (ident refl ($ 1)) ⟩
--     $ 2 ⦅ _+_ ⦆ $ 1 ⟨ + ℕ≤★ ⟩ —→⟨ ξ [ □ ]⟨ + ℕ≤★ ⟩ δ ⟩
--     $ 3 ⟨ + ℕ≤★ ⟩
--   —→⟨ ξ □ (expand ($ 3) $ℕ) ⟩
--     $ 3 ⟨ + id ⟩ ⇑ $ℕ
--   —→⟨ ξ ([ □ ]⇑ $ℕ) (ident refl ($ 3)) ⟩
--     $ℕ★ 3
--   ∎

-- inc★′2★—↠3★  : inc★′ ·★ ($★ 2) —↠ $★ 3
-- inc★′2★—↠3★  =
--   begin
--     ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) ⟨ + ℕ⇒ℕ≤★ ⟩) ·★ $ℕ★ 2
--   —→⟨ ξ ([ [ □ ]⟨ - ★⇒★≤★ ⟩ ]· $ℕ★ 2) (expand (ƛ _) ★⇒★) ⟩
--     ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) ⟨ + ℕ≤★ ⇒ ℕ≤★ ⟩ ⇑ ★⇒★) ·★ $ℕ★ 2
--   —→⟨ ξ ([ [ [ □ ]⇑ ★⇒★ ]⟨ - ★⇒★≤★ ⟩ ]· $ℕ★ 2) (wrap refl) ⟩
--     ((ƛ ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) · (` Z ⟨ - ℕ≤★ ⟩) ⟨ + ℕ≤★ ⟩)) ⇑ ★⇒★) ·★ $ℕ★ 2
--   —→⟨ ξ ([ □ ]· $ℕ★ 2) (collapse (ƛ _) ★⇒★) ⟩
--     ((ƛ ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) · (` Z ⟨ - ℕ≤★ ⟩) ⟨ + ℕ≤★ ⟩)) ⟨ - id ⟩) · $ℕ★ 2
--   —→⟨ ξ ([ □ ]· $ℕ★ 2) (ident refl (ƛ _)) ⟩
--     (ƛ ((ƛ (` Z ⦅ _+_ ⦆ $ 1)) · (` Z ⟨ - ℕ≤★ ⟩) ⟨ + ℕ≤★ ⟩)) · $ℕ★ 2
--   —→⟨ ξ □ (β ($ℕ★ 2)) ⟩
--     (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · ($ℕ★ 2 ⟨ - ℕ≤★ ⟩) ⟨ + ℕ≤★ ⟩
--   —→⟨ ξ [ (ƛ (` Z ⦅ _+_ ⦆ $ 1)) ·[ □ ] ]⟨ + ℕ≤★ ⟩ (collapse ($ 2) $ℕ) ⟩
--     (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · ($ 2 ⟨ - id ⟩) ⟨ + ℕ≤★ ⟩
--   —→⟨ ξ [ (ƛ (` Z ⦅ _+_ ⦆ $ 1)) ·[ □ ] ]⟨ + ℕ≤★ ⟩ (ident refl ($ 2)) ⟩
--     (ƛ (` Z ⦅ _+_ ⦆ $ 1)) · $ 2 ⟨ + ℕ≤★ ⟩
--   —→⟨ ξ [ □ ]⟨ + ℕ≤★ ⟩ (β ($ 2)) ⟩
--     $ 2 ⦅ _+_ ⦆ $ 1 ⟨ + ℕ≤★ ⟩
--   —→⟨ ξ [ □ ]⟨ + ℕ≤★ ⟩ δ ⟩
--     $ 3 ⟨ + ℕ≤★ ⟩
--   —→⟨ ξ □ (expand ($ 3) $ℕ) ⟩
--     $ 3 ⟨ + id ⟩ ⇑ $ℕ
--   —→⟨ ξ ([ □ ]⇑ $ℕ) (ident refl ($ 3)) ⟩
--     $ℕ★ 3
--   ∎

-- inc★true★—↠blame : inc★ ·★ ($★ true) —↠
--   ([ [ □ ]⦅ _+_ ⦆ ($ℕ★ 1 ⟨ - ℕ≤★ ⟩) ]⟨ + ℕ≤★ ⟩) ⟦ blame ⟧
-- inc★true★—↠blame =
--   begin
--     (ƛ★ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ·★ $𝔹★ true
--   —→⟨ ξ ([ [ □ ]⟨ - ★⇒★≤★ ⟩ ]· $𝔹★ true) (expand (ƛ _) ★⇒★) ⟩
--     ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⟨ + id ⟩ ⇑ ★⇒★) ·★ $𝔹★ true
--   —→⟨ ξ ([ [ [ □ ]⇑ ★⇒★ ]⟨ - ★⇒★≤★ ⟩ ]· $𝔹★ true) (ident refl (ƛ _)) ⟩
--     ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⇑ ★⇒★) ·★ $𝔹★ true
--   —→⟨ ξ ([ □ ]· $𝔹★ true) (collapse (ƛ _) ★⇒★) ⟩
--     ((ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) ⟨ - id ⟩) · $𝔹★ true
--   —→⟨ ξ ([ □ ]· $𝔹★ true) (ident refl (ƛ _)) ⟩
--     (ƛ (` Z ⦅ _+_ ⦆ℕ★ $ℕ★ 1)) · $𝔹★ true
--   —→⟨ ξ □ (β ($𝔹★ true)) ⟩
--     $𝔹★ true ⦅ _+_ ⦆ℕ★ $ℕ★ 1
--   —→⟨ ξ [ [ □ ]⦅ _+_ ⦆ ($ℕ★ 1 ⟨ - ℕ≤★ ⟩) ]⟨ + ℕ≤★ ⟩ (collide ($ true) $𝔹 $ℕ (λ())) ⟩
--     blame ⦅ _+_ ⦆ ($ℕ★ 1 ⟨ - ℕ≤★ ⟩) ⟨ + ℕ≤★ ⟩
--   ∎
-- ```
