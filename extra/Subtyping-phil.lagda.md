---
title     : "Subtyping: Records"
permalink : /Subtyping/
---

Version with explicit passing of list elements (as well as
explicit passing of evidence that the element is in the list).
Slightly longer, but seems to avoid an annoying bug that
complicated the previous version.


```agda
module Subtyping-phil where
```

## Imports

```agda
open import Agda.Primitive using (lzero; lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
-- open import Data.List.Relation.Unary.All using (All; []; _∷_)
-- open import Data.List.Relation.Unary.Any using (Any; here; there)
-- open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_; _+_)
open import Data.Nat.Properties
    using (m+n≤o⇒m≤o; m+n≤o⇒n≤o; n≤0⇒n≡0; ≤-pred; ≤-refl; ≤-trans; m≤m+n;
           m≤n+m)
open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_)
open import Data.Product using (_×_; Σ; ∃; _,_; Σ-syntax; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
```

## Operators

First, we get all our infix declarations out of the way.
We list separately operators for judgments, types, and terms:
```agda
infix  4 _∈_

infix  4 _⊢_
infix  4 _∋_
infixl 5 _▷_

infix  5 _<:_
infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infix  6 _↑_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
```

## Properties of lists

Since we will be working with records indexed by lists of field names,
we will need some properties of lists.

A list is distinct if the location of each element in the list is
unique.

The definition of `_∈_` in the standard library is quite general,
so we define for ourselves the special case we require.

```agda
data _∈_ {X : Set} : X → List X → Set where

  here : ∀ {x : X} {xs : List X}
      ------------
    → x ∈ (x ∷ xs)

  there : ∀ {x y : X} {xs : List X}
    → x ∈ xs
      ------------
    → x ∈ (y ∷ xs)
```

```agda
distinct : ∀ {X : Set} (xs : List X) → Set
distinct {X} xs  =  ∀ (x : X) (x∈xs : x ∈ xs) (x∈xs′ : x ∈ xs) → x∈xs ≡ x∈xs′
```

One list is a subset of another if every value that is an element of
the first is also an element of the second.
```agda
_⊆_ : ∀ {X} (xs ys : List X) → Set
xs ⊆ ys  =  ∀ {x} → x ∈ xs → x ∈ ys
```

Subset is reflexive and transitive.
```agda
⊆-refl : ∀ {X} (xs : List X) → xs ⊆ xs
⊆-refl xs  =  id

⊆-trans : ∀ {X} {xs ys zs : List X}
  → xs ⊆ ys
  → ys ⊆ zs
    -------
  → xs ⊆ zs
⊆-trans xs⊆ys ys⊆zs =  ys⊆zs ∘ xs⊆ys
```

## Finite maps, dependent finite maps

These are here out of interest, they are not needed for what follows,
as instead `Type* as` and `Γ ⊢* AS` are defined directly.

We consider maps indexed by the elements of a list with a fixed target
type.  The particular case of interest will be `AS : Type* as`, where
we define

  Type* as = Map as Type

with `as` a list of field names, and `AS : Type* as` a map of types.

We also consider dependent maps, which are indexed by the elements of
a list and where the target is a map of sets indexed by the same
list. The particular case of interest will be `MS : Γ ⊢* AS`, where

    Γ ⊢* AS = dMap as (map (Γ ⊢_) AS)

with `as` a list of field names, and `AS` is a map of types, and
where `map` applies a function to a map to yield another map.

```agda
Map : ∀ {ℓ} {X : Set} (xs : List X) (Y : Set ℓ) → Set ℓ
Map {ℓ} {X} xs Y = ∀ (x : X) → (x ∈ xs) → Y

map : ∀ {ℓ} {X : Set} {xs : List X} {Y : Set} {Z : Set ℓ}
  → (Y → Z) → Map xs Y → Map xs Z
map f YS x x∈xs = f (YS x x∈xs)

dMap : ∀ {X : Set} (xs : List X) (YS : Map xs Set) → Set
dMap {X} xs YS = ∀ (x : X) → (x∈xs : x ∈ xs) → YS x x∈xs
```


## Record Fields

```agda
Field : Set
Field = String
```

## Types

```agda
data Type : Set

Type* : List Field → Set
Type* as = ∀ (a : Field) → (a ∈ as) → Type

data Type where
  _⇒_   : Type → Type → Type
  `ℕ    : Type
  ⦗_⦂_⦘ :  (as : List Field) → (AS : Type* as) → {distinct as} → Type
```

In addition to function types `A ⇒ B` and natural numbers `ℕ`, we
have the record type `⦗ as ⦂ AS ⦘{d}`, where `as` is list of field names
and `AS` is a map of types indexed by `as`, and `d` is a proof that the
field names in `as` are distinct.


## Subtyping

The subtyping relation, written `A <: B`, defines when an implicit
cast is allowed via the subsumption rule. We also define a four-place
relation `as ⦂ AS <: bs ⦂ BS` that captures a key part of the subtyping
rule for records.

```agda
data _<:_ : Type → Type → Set

_⦂_<:_⦂_ : ∀ (as : List Field) (AS : Type* as)
             (bs : List Field) (BS : Type* bs) → Set
as ⦂ AS <: bs ⦂ BS
  = ∀ a → (a∈as : a ∈ as) → (a∈bs : a ∈ bs) → AS a a∈as <: BS a a∈bs

data _<:_ where

  <:-ℕ : `ℕ <: `ℕ

  <:-⇒ : ∀{A A′ B B′ : Type}
    → A′ <: A
    → B <: B′
      ----------------
    → A ⇒ B <: A′ ⇒ B′

  <:-⦗⦘ : ∀ {as : List Field}{AS : Type* as}{d : distinct as}
            {bs : List Field}{BS : Type* bs}{e : distinct bs}
    → bs ⊆ as
    → as ⦂ AS <: bs ⦂ BS
      --------------------------------
    → ⦗ as ⦂ AS ⦘{d} <: ⦗ bs ⦂ BS ⦘{e}
```

## Subtyping is Reflexive

```
<:-refl : ∀ (A : Type) → A <: A
<:-refl `ℕ                =  <:-ℕ
<:-refl (A ⇒ B)           =  <:-⇒ (<:-refl A) (<:-refl B)
<:-refl (⦗ as ⦂ AS ⦘{d})  =  <:-⦗⦘ as⊆as AS<:AS
  where
  as⊆as : as ⊆ as
  as⊆as = ⊆-refl as

  AS<:AS : as ⦂ AS <: as ⦂ AS
  AS<:AS a a∈as a∈as′ with d a a∈as a∈as′
  ... | refl = <:-refl (AS a a∈as)
```

The application of distinct is used to show that any two pieces
of evidence that `a` is in `as`, namely `a∈as` and `a∈as′`,
must be the same, after which reflexivity can be applied to
show that `AS a∈as <: AS a∈as`.

The proof is greatly simplified compared to Jeremy's proof, which uses
induction over the size of a type rather than structural induction.
I was surprised the first time I realised that Agda could show
termination `<:-refl`, and that it can recognise that `AS a∈as`
plays the role of a substructure of `⦗ as ⦂ AS ⦘{d}`.


## Subtyping is transitive

```agda
<:-trans : ∀{A B C}
    → A <: B
    → B <: C
      ------
    → A <: C
<:-trans <:-ℕ <:-ℕ
  = <:-ℕ
<:-trans (<:-⇒ A₁<:B₁ A₂<:B₂) (<:-⇒ B₁<:C₁ B₂<:C₂)
  = <:-⇒ (<:-trans B₁<:C₁ A₁<:B₁) (<:-trans A₂<:B₂ B₂<:C₂)
<:-trans {⦗ as ⦂ AS ⦘{d} } {⦗ bs ⦂ BS ⦘{e} } {⦗ cs ⦂ CS ⦘{f}}
    (<:-⦗⦘ bs⊆as AS<:BS) (<:-⦗⦘ cs⊆bs BS<:CS) =
    <:-⦗⦘ cs⊆as AS<:CS
    where
    cs⊆as : cs ⊆ as
    cs⊆as = ⊆-trans cs⊆bs bs⊆as

    AS<:CS : as ⦂ AS <: cs ⦂ CS
    AS<:CS a a∈as a∈cs with cs⊆bs a∈cs
    ... | a∈bs =
      <:-trans (AS<:BS a a∈as a∈bs) (BS<:CS a a∈bs a∈cs)
```
In the final clause, we are given evidence that `a ∈ as` and `a ∈ cs`,
and we use the fact that `cs ⊆ bs` to convert the second of these into
evidence that `a ∈ bs`.

## Contexts and variables

Contexts and variables are exactly as in Chapter [DeBruijn](/DeBruijn/).

```agda
data Context : Set where
  ∅   : Context
  _▷_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ ▷ A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ ▷ B ∋ A
```

## Terms

Terms are copied from Chapter [DeBruijn](/DeBruijn/), with additional
constructs to build a record `⦗as ⦂ MS⦘`, select a field from a record
`M # a∈as`, and to upcast via a subtyping judgement `M ↑ A<:B`.  In
the first of these, the indexed record of terms `MS` has type `dMap as
(map (Γ ⊢_) AS)`, which ensures that given evidence `a∈as` of the
judgement `a ∈ as` we have that `MS a∈as : Γ ⊢ AS a∈as`.  In the
second of these, rather than indexing on the name of a field `a`, we
index on evidence `a∈as` of the judgement `a ∈ as` that field `a`
appears in the list of fields `as`. In the third, we supply evidence
`A<:B` of the judgement `A <: B` that `A` is a subtype of `B`.

```agda
data _⊢_ : Context → Type → Set
_⊢*_ : ∀ {as} → Context → Type* as → Set

data _⊢_ where

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

  ⦗_⦂_⦘ : ∀ {Γ}
    → (as : List Field)
    → {AS : Type* as}
    → (MS : Γ ⊢* AS)
    → {d : distinct as}
      --------------------
    → Γ ⊢ ⦗ as ⦂ AS ⦘{ d }

  _#_ : ∀ {Γ a as}
    → {AS : Type* as}
    → {d : distinct as}
    → (M : Γ ⊢ ⦗ as ⦂ AS ⦘{ d })
    → (a∈as : a ∈ as)
      --------------------------
    → Γ ⊢ AS a a∈as

  _↑_ : ∀ {Γ A B}
    → Γ ⊢ A
    → A <: B
      ------
    → Γ ⊢ B

_⊢*_ {as} Γ AS = ∀ (a : Field) → (a∈as : a ∈ as) → Γ ⊢ AS a a∈as
```
The right-hand side of `Γ ⊢* AS` is equivalent to `dMap as (map (Γ ⊢_) AS)`.


## Renaming and Substitution

Copied from Chapter [DeBruijn](/DeBruijn/), with extra cases for records.

```agda
ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ ▷ B ∋ A → Δ ▷ B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```

```agda
rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)

rename* : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------------------------------
  → (∀ {as} {AS : Type* as} → Γ ⊢* AS → Δ ⊢* AS)

rename ρ (` x)             =  ` (ρ x)
rename ρ (ƛ N)             =  ƛ (rename (ext ρ) N)
rename ρ (L · M)           =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)           =  `zero
rename ρ (`suc M)          =  `suc (rename ρ M)
rename ρ (case L M N)      =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N)             =  μ (rename (ext ρ) N)
rename ρ (⦗ as ⦂ MS ⦘{d})  =  ⦗ as ⦂ rename* ρ MS ⦘{d}
rename ρ (M # a∈as)        =  rename ρ M # a∈as
rename ρ (M ↑ A<:B)        =  rename ρ M ↑ A<:B

rename* ρ MS a a∈as        =  rename ρ (MS a a∈as)
```

```agda
exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ---------------------------------
  → (∀ {A B} → Γ ▷ B ∋ A → Δ ▷ B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)
```

```agda
subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)

subst* : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    -----------------------------------------------
  → (∀ {as} {AS : Type* as} → Γ ⊢* AS → Δ ⊢* AS)

subst σ (` k)             =  σ k
subst σ (ƛ N)             =  ƛ (subst (exts σ) N)
subst σ (L · M)           =  (subst σ L) · (subst σ M)
subst σ (`zero)           =  `zero
subst σ (`suc M)          =  `suc (subst σ M)
subst σ (case L M N)      =  case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)             =  μ (subst (exts σ) N)
subst ρ (⦗ as ⦂ MS ⦘{d})  =  ⦗ as ⦂ subst* ρ MS ⦘{d}
subst ρ (M # a∈as)        =  subst ρ M # a∈as
subst ρ (M ↑ A<:B)        =  subst ρ M ↑ A<:B

subst* ρ MS a a∈as        =  subst ρ (MS a a∈as)
```

```agda
_[_] : ∀ {Γ A B}
  → Γ ▷ B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ ▷ B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ ▷ B ∋ A → Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x
```

## Values

Keeping Jeremy's notion of lazy records for now.  We need one more
value form, to assert that a subsumptions is a value if its contained
term is a value.

```agda
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ ▷ A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)

  V-⦗⦘ : ∀ {Γ} {as} {AS : Type* as} {MS : Γ ⊢* AS} {d : distinct as}
      -----------------------------------------------------------------
    → Value (⦗ as ⦂ MS ⦘{d})
```

## Reduction

Reduction is as in Chapter [DeBruijn](/DeBruijn/), with five new
rules, `ξ-#`, `β-#`, `ξ-<:`, `β-<:-ℕ`, `β-<:-⇒`, and `β-<:-⦗⦘` The
last four of these don't appear in Jeremy's development, a difference
between the extrinsic and intrinsic approaches.

```agda
coerce : ∀ {Γ as bs} {AS : Type* as} {BS : Type* bs}
           → (bs ⊆ as)
           → (as ⦂ AS <: bs ⦂ BS)
           → (Γ ⊢* AS)
             ---------
           → (Γ ⊢* BS)
coerce bs⊆as AS<:BS MS a a∈bs = MS a a∈as ↑ AS<:BS a a∈as a∈bs
  where
  a∈as = bs⊆as a∈bs

infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ ▷ A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ ▷ `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ▷ `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ ▷ `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  β-μ : ∀ {Γ A} {N : Γ ▷ A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]

  ξ-# : ∀ {Γ as a} {AS : Type* as} {d : distinct as}
          {M M′ : Γ ⊢ ⦗ as ⦂ AS ⦘{d}} {a∈as : a ∈ as}
    → M —→ M′
      ---------------------
    → M # a∈as —→ M′ # a∈as

  β-# : ∀ {Γ as a} {AS : Type* as} {d : distinct as}
          {MS : Γ ⊢* AS} {a∈as : a ∈ as} {M : Γ ⊢ AS a a∈as}
    → MS a a∈as ≡ M
      --------------------------
    → ⦗ as ⦂ MS ⦘{d} # a∈as —→ M

  ξ-<: : ∀ {Γ A B} {M M′ : Γ ⊢ A} {A<:B : A <: B}
    → M —→ M′
      ---------------------
    → M ↑ A<:B —→ M′ ↑ A<:B

  β-<:-ℕ : ∀ {Γ} {M : Γ ⊢ `ℕ}
    → Value M
      -------------
    → M ↑ <:-ℕ —→ M

  β-<:-⇒ : ∀ {Γ A B A′ B′} {M : Γ ⊢ A ⇒ B}
             {A′<:A : A′ <: A} {B<:B′ : B <: B′}
    → Value M
      -----------------------------------------------------------------
    → M ↑ (<:-⇒ A′<:A B<:B′) —→ ƛ (rename S_ M · (` Z ↑ A′<:A) ↑ B<:B′)

  β-<:-⦗⦘ : ∀ {Γ as bs} {AS : Type* as} {BS : Type* bs}
              {bs⊆as : bs ⊆ as} {AS<:BS : as ⦂ AS <: bs ⦂ BS}
              {MS : Γ ⊢* AS} {NS : Γ ⊢* BS} {d : distinct as} {e : distinct bs}
    → coerce bs⊆as AS<:BS MS ≡ NS
      --------------------------------------------------------
    → ⦗ as ⦂ MS ⦘{d} ↑ (<:-⦗⦘ bs⊆as AS<:BS) —→ ⦗ bs ⦂ NS ⦘{e}
```

## Progress {#subtyping-progress}

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
```

The statement and proof of progress is much as before,
appropriately annotated.  We no longer need
to explicitly refer to the Canonical Forms lemma, since it
is built-in to the definition of value:
```agda
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
progress (⦗ as ⦂ MS ⦘{d})               =  done V-⦗⦘
progress (M # a∈as) with progress M
...    | step M—→M′                     =  step (ξ-# M—→M′)
...    | done V-⦗⦘                      =  step (β-# refl)
progress (M ↑ A<:B) with progress M
...    | step M—→M′                     =  step (ξ-<: M—→M′)
...    | done VM with VM | A<:B
...        | V-ℕ  | <:-ℕ                =  step (β-<:-ℕ VM)
...        | V-⇒  | <:-⇒ A′<:A B<:B′    =  step (β-<:-⇒ VM)
...        | V-⦗⦘ | <:-⦗⦘ bs⊆as AS<:BS  =  step (β-<:-⦗⦘ refl)
```

## Reflexive and transitive closure

The reflexive and transitive closure is exactly as before.
We simply cut-and-paste the previous definition:
```agda
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```


## Evaluation

```agda
record Gas : Set where
  constructor gas
  field
    amount : ℕ
```

```agda
data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N
```

```agda
data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
```

The evaluator takes gas and a term and returns the corresponding steps:
```agda
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

## Reify and Reflect

These are here out of interest, they are not needed for what follows.

```agda
rep* : ∀ (as : List Field) → Set
rep* [] =  ⊤
rep* (a ∷ as)  =  Type × rep* as

next* : ∀ {a} {as} → Type* (a ∷ as) → Type* as
next* AS a a∈as = AS a (there a∈as)

reify* : ∀ (as : List Field) → Type* as → rep* as
reify* [] AS = tt
reify* (a ∷ as) AS = AS a here , reify* as (next* AS)

reflect* : ∀ (as : List Field) → rep* as → Type* as
reflect* [] tt a ()
reflect* (a ∷ as) (A , AT) .a here  =  A
reflect* (_ ∷ as) (A , AT) a (there a∈as)  =  reflect* as AT a a∈as

rep⊢* : ∀ (as : List Field) → Context → (rep* as) → Set
rep⊢* [] Γ tt =  ⊤
rep⊢* (a ∷ as) Γ (A , AT)  = Γ ⊢ A × rep⊢* as Γ AT

next⊢* : ∀ {a} {as} {Γ} {AS : Type* (a ∷ as)} → Γ ⊢* AS → Γ ⊢* next* AS
next⊢* MS a a∈as = MS a (there a∈as)

reify⊢* : ∀ (as : List Field) → (Γ : Context) → (AS : Type* as) → Γ ⊢* AS → rep⊢* as Γ (reify* as AS)
reify⊢* [] Γ AS MS = tt
reify⊢* (a ∷ as) Γ AS MS = MS a here , reify⊢* as Γ (next* AS) (next⊢* MS)

reflect⊢* : ∀ (as : List Field) → (Γ : Context) → (AT : rep* as) → (MT : rep⊢* as Γ AT) → Γ ⊢* reflect* as AT
reflect⊢* [] Γ tt tt a ()
reflect⊢* (a ∷ as) Γ (A , AT) (M , MT) .a here  =  M
reflect⊢* (_ ∷ as) Γ (A , AT) (M , MT) a (there a∈as)  =  reflect⊢* as Γ AT MT a a∈as
```

## Extracting evidence from a decision procedure

```agda
evidence : ∀ {P : Set} (Q : Dec P) → True Q → P
evidence (yes p) tt  =  p
evidence (no ¬p) ()
```


## Example

```agda
xy : List Field
xy = "x" ∷ "y" ∷ []

dxy : distinct xy
dxy ."x" here here = refl
dxy ."x" here (there (there ()))
dxy ."y" (there here) (there here) = refl

xyz : List Field
xyz = "x" ∷ "y" ∷ "z" ∷ []

dxyz : distinct xyz
dxyz ."x" here here = refl
dxyz ."x" here (there (there (there ())))
dxyz ."y" (there here) (there here) = refl
dxyz ."y" (there here) (there (there (there ())))
dxyz ."z" (there (there here)) (there (there here)) = refl

xy⊆xyz : xy ⊆ xyz
xy⊆xyz here = here
xy⊆xyz (there here) = there here

AS2 : Type* xy
AS2 ."x" here = `ℕ
AS2 ."y" (there here) = `ℕ

MS2 : ∅ ⊢* AS2
MS2 ."x" here = `zero
MS2 ."y" (there here) = `suc `zero

AS3 : Type* xyz
AS3 ."x" here = `ℕ
AS3 ."y" (there here) = `ℕ
AS3 ."z" (there (there here)) = `ℕ

MS3 : ∅ ⊢* AS3
MS3 ."x" here = `zero
MS3 ."y" (there here) = `suc `zero
MS3 ."z" (there (there here)) = `suc `suc `zero

Pt2 : Type
Pt2 = ⦗ xy ⦂ AS2 ⦘{dxy}

Pt3 : Type
Pt3 = ⦗ xyz ⦂ AS3 ⦘{dxyz}

xyz⦂AS3<:xy⦂AS2 : xyz ⦂ AS3 <: xy ⦂ AS2
xyz⦂AS3<:xy⦂AS2 ."x" here here = <:-ℕ
xyz⦂AS3<:xy⦂AS2 ."x" here (there (there ()))
xyz⦂AS3<:xy⦂AS2 ."y" (there here) (there here) = <:-ℕ
xyz⦂AS3<:xy⦂AS2 ."z" (there (there here)) (there (there ()))
xyz⦂AS3<:xy⦂AS2 _ (there (there (there ())))

Pt3<:Pt2 : Pt3 <: Pt2
Pt3<:Pt2 = <:-⦗⦘ xy⊆xyz xyz⦂AS3<:xy⦂AS2

M₀ : ∅ ⊢ Pt2 ⇒ `ℕ
M₀ = ƛ ((` Z) # here)

M₁ : ∅ ⊢ Pt3
M₁ = ⦗ xyz ⦂ MS3 ⦘

M₂ : ∅ ⊢ `ℕ
M₂ = M₀ · (M₁ ↑ Pt3<:Pt2)

_ : M₂ —↠ `zero
_ =
  begin
    ((ƛ ((` Z) # here)) · (⦗ xyz ⦂ MS3 ⦘ ↑ <:-⦗⦘ xy⊆xyz xyz⦂AS3<:xy⦂AS2))
  —→⟨ ξ-·₂ V-ƛ (β-<:-⦗⦘ refl) ⟩
    (ƛ ((` Z) # here)) · ⦗ xy ⦂ (λ a a∈bs → MS3 a (xy⊆xyz a∈bs) ↑ xyz⦂AS3<:xy⦂AS2 a (xy⊆xyz a∈bs) a∈bs) ⦘
  —→⟨ β-ƛ V-⦗⦘ ⟩
    (⦗ xy ⦂ (λ a a∈bs → MS3 a (xy⊆xyz a∈bs) ↑ xyz⦂AS3<:xy⦂AS2 a (xy⊆xyz a∈bs) a∈bs) ⦘ # here)
  —→⟨ β-# refl ⟩
    `zero ↑ <:-ℕ
  —→⟨ β-<:-ℕ V-zero ⟩
    `zero
  ∎

M₃ : ∅ ⊢ `ℕ
M₃ = (M₀ ↑ <:-⇒ Pt3<:Pt2 <:-ℕ) · M₁

_ : M₃ —↠ `zero
_ =
  begin
    ((ƛ ((` Z) # here)) ↑ <:-⇒ (<:-⦗⦘ xy⊆xyz xyz⦂AS3<:xy⦂AS2) <:-ℕ) · ⦗ xyz ⦂ MS3 ⦘
  —→⟨ ξ-·₁ (β-<:-⇒ V-ƛ) ⟩
   (ƛ (ƛ ((` Z) # here)) · (` Z ↑ <:-⦗⦘ xy⊆xyz xyz⦂AS3<:xy⦂AS2) ↑ <:-ℕ) · ⦗ xyz ⦂ MS3 ⦘
  —→⟨ β-ƛ V-⦗⦘ ⟩
   ((ƛ ((` Z) # here)) · (⦗ xyz ⦂ MS3 ⦘ ↑ <:-⦗⦘ xy⊆xyz xyz⦂AS3<:xy⦂AS2)) ↑ <:-ℕ
  —→⟨ ξ-<: (ξ-·₂ V-ƛ (β-<:-⦗⦘ refl)) ⟩
   (ƛ ((` Z) # here)) · ⦗ xy ⦂ (λ a a∈bs → MS3 a (xy⊆xyz a∈bs) ↑ xyz⦂AS3<:xy⦂AS2 a (xy⊆xyz a∈bs) a∈bs) ⦘ ↑ <:-ℕ
  —→⟨ ξ-<: (β-ƛ V-⦗⦘) ⟩
    (⦗ xy ⦂ (λ a a∈bs → MS3 a (xy⊆xyz a∈bs) ↑ xyz⦂AS3<:xy⦂AS2 a (xy⊆xyz a∈bs) a∈bs) ⦘ # here) ↑ <:-ℕ
  —→⟨ ξ-<: (β-# refl) ⟩
    (`zero ↑ <:-ℕ) ↑ <:-ℕ
  —→⟨ ξ-<: (β-<:-ℕ V-zero) ⟩
    `zero ↑ <:-ℕ
  —→⟨ β-<:-ℕ V-zero ⟩
    `zero
  ∎

```

-- -- -- #### Exercise `intrinsic-records` (stretch)

-- -- -- Formulate the language of this chapter, STLC with records, using
-- -- -- intrinsically typed terms. This requires taking an algorithmic approach
-- -- -- to the type system, which means that there is no subsumption rule and
-- -- -- instead subtyping is used in the elimination rules. For example,
-- -- -- the rule for function application would be:

-- -- --     _·_ : ∀ {Γ A B C}
-- -- --       → Γ ⊢ A ⇒ B
-- -- --       → Γ ⊢ C
-- -- --       → C <: A
-- -- --         -------
-- -- --       → Γ ⊢ B

-- -- -- #### Exercise `type-check-records` (practice)

-- -- -- Write a recursive function whose input is a `Term` and whose output
-- -- -- is a typing derivation for that term, if one exists.

-- -- --     type-check : (M : Term) → (Γ : Context) → Maybe (Σ[ A ∈ Type ] Γ ⊢ M ⦂ A)

-- -- -- #### Exercise `variants` (recommended)

-- -- -- Add variants to the language of this chapter and update the proofs of
-- -- -- progress and preservation. The variant type is a generalization of a
-- -- -- sum type, similar to the way the record type is a generalization of
-- -- -- product. The following summarizes the treatment of variants in the
-- -- -- book Types and Programming Languages. A variant type is traditionally
-- -- -- written:

-- -- --     〈l₁:A₁, ..., lᵤ:Aᵤ〉

-- -- -- The term for introducing a variant is

-- -- --     〈l=t〉

-- -- -- and the term for eliminating a variant is

-- -- --     case L of 〈l₁=x₁〉 ⇒ M₁ | ... | 〈lᵤ=xᵤ〉 ⇒ Mᵤ

-- -- -- The typing rules for these terms are

-- -- --     (T-Variant)
-- -- --     Γ ⊢ Mⱼ : Aⱼ
-- -- --     ---------------------------------
-- -- --     Γ ⊢ 〈lⱼ=Mⱼ〉 : 〈l₁=A₁, ... , lᵤ=Aᵤ〉


-- -- --     (T-Case)
-- -- --     Γ ⊢ L : 〈l₁=A₁, ... , lᵤ=Aᵤ〉
-- -- --     ∀ i ∈ 1..u,   Γ,xᵢ:Aᵢ ⊢ Mᵢ : B
-- -- --     ---------------------------------------------------
-- -- --     Γ ⊢ case L of 〈l₁=x₁〉 ⇒ M₁ | ... | 〈lᵤ=xᵤ〉 ⇒ Mᵤ  : B

-- -- -- The non-algorithmic subtyping rules for variants are

-- -- --     (S-VariantWidth)
-- -- --     ------------------------------------------------------------
-- -- --     〈l₁=A₁, ..., lᵤ=Aᵤ〉   <:   〈l₁=A₁, ..., lᵤ=Aᵤ, ..., lᵤ₊ₓ=Aᵤ₊ₓ〉

-- -- --     (S-VariantDepth)
-- -- --     ∀ i ∈ 1..u,    Aᵢ <: Bᵢ
-- -- --     ---------------------------------------------
-- -- --     〈l₁=A₁, ..., lᵤ=Aᵤ〉   <:   〈l₁=B₁, ..., lᵤ=Bᵤ〉

-- -- --     (S-VariantPerm)
-- -- --     ∀i∈1..u, ∃j∈1..u, kⱼ = lᵢ and Aⱼ = Bᵢ
-- -- --     ----------------------------------------------
-- -- --     〈k₁=A₁, ..., kᵤ=Aᵤ〉   <:   〈l₁=B₁, ..., lᵤ=Bᵤ〉

-- -- -- Come up with an algorithmic subtyping rule for variant types.

-- -- -- #### Exercise `<:-alternative` (stretch)

-- -- -- Revise this formalisation of records with subtyping (including proofs
-- -- -- of progress and preservation) to use the non-algorithmic subtyping
-- -- -- rules for Chapter 15 of Types and Programming Languages, which we list here:

-- -- --     (S-RcdWidth)
-- -- --     -------------------------------------------------------------------------
-- -- --     ⦗ l₁ ⦂ A₁, ..., lᵤ ⦂ Aᵤ, ..., lᵤ₊ₓ ⦂ Aᵤ₊ₓ ⦘ < ⦂  ⦗ l₁ ⦂ A₁, ..., lᵤ ⦂ Aᵤ ⦘

-- -- --     (S-RcdDepth)
-- -- --         ∀i∈1..u, Aᵢ <: Bᵢ
-- -- --     ------------------------------------------------------
-- -- --     ⦗ l₁ ⦂ A₁, ..., lᵤ ⦂ Aᵤ ⦘ <: ⦗ l₁ ⦂ B₁, ..., lᵤ ⦂ Bᵤ ⦘

-- -- --     (S-RcdPerm)
-- -- --     ∀i∈1..u, ∃j∈1..u, kⱼ = lᵢ and Aⱼ = Bᵢ
-- -- --     ------------------------------------------------------
-- -- --     ⦗ k₁ ⦂ A₁, ..., kᵤ ⦂ Aᵤ ⦘ <: ⦗ l₁ ⦂ B₁, ..., lᵤ ⦂ Bᵤ ⦘

-- -- -- You will most likely need to prove inversion lemmas for the subtype relation
-- -- -- of the form:

-- -- --     If S <: T₁ ⇒ T₂, then S ≡ S₁ ⇒ S₂, T₁ <: S₁, and S₂ <: T₂, for some S₁, S₂.

-- -- --     If S <: ⦗ lᵢ ⦂ Tᵢ | i ∈ 1..n ⦘, then S ≡ ⦗ kⱼ ⦂ Sⱼ | j ∈ 1..m ⦘
-- -- --     and { lᵢ | i ∈ 1..n } ⊆ { kⱼ | j ∈ 1..m }
-- -- --     and Sⱼ <: Tᵢ for every i and j such that lᵢ = kⱼ.

-- ## References

-- * John C. Reynolds. Using Category Theory to Design Implicit
--   Conversions and Generic Operators.
--   In Semantics-Directed Compiler Generation, 1980.
--   LNCS Volume 94.

-- * Luca Cardelli. A semantics of multiple inheritance.  In Semantics of
--   Data Types, 1984. Springer.

-- * Barbara H. Liskov and Jeannette M. Wing.  A Behavioral Notion of
--   Subtyping. In ACM Trans. Program. Lang. Syst.  Volume 16, 1994.

-- * Types and Programming Languages. Benjamin C. Pierce. The MIT Press. 2002.

-- # Unicode

-- This chapter uses the following unicode:

--   ⦗  U+2997  LEFT BLACK TORTOISE SHELL BRACKET (\()
--    ⦘ U+2997  RIGHT BLACK TORTOISE SHELL BRACKET (\))
--    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
--    ⊆  U+2286  SUBSET OF OR EQUAL TO (\sub=)
--    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
--    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
--    μ  U+03BC  GREEK SMALL LETTER MU (\mu)
--    ·  U+00B7  MIDDLE DOT (\cdot)
--    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
--    ∋  U+220B  CONTAINS AS MEMBER (\ni)
--    →  U+2192  RIGHTWARDS ARROW (\to)
--    —  U+2014  EM DASH (\em)
