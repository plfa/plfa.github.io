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
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)
```

## Operators

First, we get all our infix declarations out of the way.
We list separately operators for judgments, types, and terms:
```agda
infix  4 _∈_

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

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

We consider maps indexed by the elements of a list with a fixed target
type.  The particular case of interest will be `AS : Map as Type`,
where `as` is a list of field names, and `AS` is a map of types.

We also consider dependent maps, which are indexed by the elements of
a list and where the target is a map of sets indexed by the same
list. The particular case of interest will be

    MS : dMap as (map (Γ ⊢_) AS)

where `as` is a list of field names, and `AS` is a map of types, and
`map` applies a function to a map to yield another map.

```agda
Map : ∀ {ℓ} {X : Set} (xs : List X) (Y : Set ℓ) → Set ℓ
Map {ℓ} {X} xs Y = ∀ (x : X) → (x ∈ xs) → Y

map : ∀ {ℓ} {X : Set} {xs : List X} {Y : Set} {Z : Set ℓ}
  → (Y → Z) → Map xs Y → Map xs Z
map f YS x x∈xs = f (YS x x∈xs)

dMap : ∀ {X : Set} (xs : List X) (YS : Map xs Set) → Set
dMap {X} xs YS = ∀ (x : X) → (x∈xs : x ∈ xs) → YS x x∈xs

-- rep* : ∀ as -> Type* as -> Set
-- rep* []  =  ⊤
-- rep* (a ∷ as)  =  Type × rep* as

```


## Record Fields

```agda
Field : Set
Field = String
```

## Types

```agda
Type* : List Field → Set

data Type : Set where
  _⇒_   : Type → Type → Type
  `ℕ    : Type
  ⦗_⦂_⦘ :  (as : List Field) → (AS : Map as Type) → {distinct as} → Type

Type* as = ∀ (a : Field) → (a ∈ as) → Type
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
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
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
    → Γ , A ⊢ B
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
    → Γ , `ℕ ⊢ A
      ----------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
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
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
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
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
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
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x
```

## Values

Keeping Jeremy's notion of lazy records for now.  We need one more
value form, to assert that a subsumptions is a value if its contained
term is a value.

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

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

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

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
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


-- -- The Progress theorem states that a well-typed term may either take a
-- -- reduction step or it is already a value. The proof of Progress is like
-- -- the one in the [Properties](/Properties/); it
-- -- proceeds by induction on the typing derivation and most of the cases
-- -- remain the same. Below we discuss the new cases for records and
-- -- subsumption.

-- -- ```agda
-- -- data Progress (M : Term) : Set where

-- --   step : ∀ {N}
-- --     → M —→ N
-- --       ----------
-- --     → Progress M

-- --   done :
-- --       Value M
-- --       ----------
-- --     → Progress M
-- -- ```

-- -- ```agda
-- -- progress : ∀ {M A}
-- --   → ∅ ⊢ M ⦂ A
-- --     ----------
-- --   → Progress M
-- -- progress (⊢` ())
-- -- progress (⊢ƛ ⊢N)                            = done V-ƛ
-- -- progress (⊢· ⊢L ⊢M)
-- --     with progress ⊢L
-- -- ... | step L—→L′                            = step (ξ-·₁ L—→L′)
-- -- ... | done VL
-- --         with progress ⊢M
-- -- ...     | step M—→M′                        = step (ξ-·₂ VL M—→M′)
-- -- ...     | done VM
-- --         with canonical ⊢L VL
-- -- ...     | C-ƛ ⊢N _                          = step (β-ƛ VM)
-- -- progress ⊢zero                              =  done V-zero
-- -- progress (⊢suc ⊢M) with progress ⊢M
-- -- ...  | step M—→M′                           =  step (ξ-suc M—→M′)
-- -- ...  | done VM                              =  done (V-suc VM)
-- -- progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
-- -- ... | step L—→L′                            =  step (ξ-case L—→L′)
-- -- ... | done VL with canonical ⊢L VL
-- -- ...   | C-zero                              =  step β-zero
-- -- ...   | C-suc CL                            =  step (β-suc (value CL))
-- -- progress (⊢μ ⊢M)                            =  step β-μ
-- -- progress (⊢# {n}{Γ}{A}{M}{l}{ls}{As}{i}{d} ⊢M ls[i]=l As[i]=A)
-- --     with progress ⊢M
-- -- ... | step M—→M′                            =  step (ξ-# M—→M′)
-- -- ... | done VM
-- --     with canonical ⊢M VM
-- -- ... | C-rcd {ks = ms}{As = Bs} ⊢Ms _ (<:-rcd ls⊆ms _)
-- --     with lookup-⊆ {i = i} ls⊆ms
-- -- ... | ⟨ k , ls[i]=ms[k] ⟩                   =  step (β-# {j = k}(trans (sym ls[i]=ms[k]) ls[i]=l))
-- -- progress (⊢rcd x d)                         =  done V-rcd
-- -- progress (⊢<: {A = A}{B} ⊢M A<:B)           =  progress ⊢M
-- -- ```
-- -- * Case `⊢#`: We have `Γ ⊢ M ⦂ ⦗ ls ⦂ As ⦘`, `lookup ls i ≡ l`, and `lookup As i ≡ A`.
-- --   By the induction hypothesis, either `M —→ M′` or `M` is a value. In the later case we
-- --   conclude that `M # l —→ M′ # l` by rule `ξ-#`. On the other hand, if `M` is a value,
-- --   we invoke the canonical forms lemma to show that `M` has the form `⦗ ms := Ms ⦘`
-- --   where `∅ ⊢* Ms ⦂ Bs` and `ls ⊆ ms`. By lemma `lookup-⊆`, we have
-- --   `lookup ls i ≡ lookup ms k` for some `k`. Thus, we have `lookup ms k ≡ l`
-- --   and we conclude `⦗ ms := Ms ⦘ # l —→ lookup Ms k` by rule `β-#`.

-- -- * Case `⊢rcd`: we immediately characterize the record as a value.

-- -- * Case `⊢<:`: we invoke the induction hypothesis on sub-derivation of `Γ ⊢ M ⦂ A`.


-- -- ## Preservation {#subtyping-preservation}

-- -- In this section we prove that when a well-typed term takes a reduction
-- -- step, the result is another well-typed term with the same type.

-- -- As mentioned earlier, we need to prove that substitution preserve
-- -- types, which in turn requires that renaming preserves types.  The
-- -- proofs of these lemmas are adapted from the intrinsic versions of the
-- -- `ext`, `rename`, `exts`, and `subst` functions in the
-- -- [DeBruijn](/DeBruijn/) chapter.

-- -- We define the following abbreviation for a *well-typed renaming* from Γ
-- -- to Δ, that is, a renaming that sends variables in Γ to variables in Δ
-- -- with the same type.
-- -- ```agda
-- -- _⦂ᵣ_⇒_ : (Id → Id) → Context → Context → Set
-- -- ρ ⦂ᵣ Γ ⇒ Δ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ ρ x ⦂ A
-- -- ```

-- -- The `ext` function takes a well-typed renaming from Γ to Δ
-- -- and extends it to become a renaming from (Γ , B) to (Δ , B).
-- -- ```agda
-- -- ext-pres : ∀ {Γ Δ ρ B}
-- --   → ρ ⦂ᵣ Γ ⇒ Δ
-- --     --------------------------------
-- --   → ext ρ ⦂ᵣ (Γ , B) ⇒ (Δ , B)
-- -- ext-pres {ρ = ρ } ρ⦂ Z = Z
-- -- ext-pres {ρ = ρ } ρ⦂ (S {x = x} ∋x) =  S (ρ⦂ ∋x)
-- -- ```

-- -- Next we prove that both `rename` and `rename-vec` preserve types.  We
-- -- use the `ext-pres` lemma in each of the cases with a variable binding: `⊢ƛ`,
-- -- `⊢μ`, and `⊢case`.
-- -- ```agda
-- -- ren-vec-pres : ∀ {Γ Δ ρ}{n}{Ms : Vec Term n}{As : Vec Type n}
-- --   → ρ ⦂ᵣ Γ ⇒ Δ  →  Γ ⊢* Ms ⦂ As  →  Δ ⊢* rename-vec ρ Ms ⦂ As

-- -- rename-pres : ∀ {Γ Δ ρ M A}
-- --   → ρ ⦂ᵣ Γ ⇒ Δ
-- --   → Γ ⊢ M ⦂ A
-- --     ------------------
-- --   → Δ ⊢ rename ρ M ⦂ A
-- -- rename-pres ρ⦂ (⊢` ∋w)           =  ⊢` (ρ⦂ ∋w)
-- -- rename-pres {ρ = ρ} ρ⦂ (⊢ƛ ⊢N)   =  ⊢ƛ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ρ⦂) ⊢N)
-- -- rename-pres {ρ = ρ} ρ⦂ (⊢· ⊢L ⊢M)=  ⊢· (rename-pres {ρ = ρ} ρ⦂ ⊢L) (rename-pres {ρ = ρ} ρ⦂ ⊢M)
-- -- rename-pres {ρ = ρ} ρ⦂ (⊢μ ⊢M)   =  ⊢μ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ρ⦂) ⊢M)
-- -- rename-pres ρ⦂ (⊢rcd ⊢Ms dls)    = ⊢rcd (ren-vec-pres ρ⦂ ⊢Ms ) dls
-- -- rename-pres {ρ = ρ} ρ⦂ (⊢# {d = d} ⊢M lif liA) = ⊢# {d = d}(rename-pres {ρ = ρ} ρ⦂ ⊢M) lif liA
-- -- rename-pres {ρ = ρ} ρ⦂ (⊢<: ⊢M lt) = ⊢<: (rename-pres {ρ = ρ} ρ⦂ ⊢M) lt
-- -- rename-pres ρ⦂ ⊢zero               = ⊢zero
-- -- rename-pres ρ⦂ (⊢suc ⊢M)           = ⊢suc (rename-pres ρ⦂ ⊢M)
-- -- rename-pres ρ⦂ (⊢case ⊢L ⊢M ⊢N)    =
-- --     ⊢case (rename-pres ρ⦂ ⊢L) (rename-pres ρ⦂ ⊢M) (rename-pres (ext-pres ρ⦂) ⊢N)

-- -- ren-vec-pres ρ⦂ ⊢*-[] = ⊢*-[]
-- -- ren-vec-pres {ρ = ρ} ρ⦂ (⊢*-∷ ⊢M ⊢Ms) =
-- --   let IH = ren-vec-pres {ρ = ρ} ρ⦂ ⊢Ms in
-- --   ⊢*-∷ (rename-pres {ρ = ρ} ρ⦂ ⊢M) IH
-- -- ```

-- -- A *well-typed substitution* from Γ to Δ sends variables in Γ to terms
-- -- of the same type in the context Δ.
-- -- ```agda
-- -- _⦂_⇒_ : (Id → Term) → Context → Context → Set
-- -- σ ⦂ Γ ⇒ Δ = ∀ {A x} → Γ ∋ x ⦂ A → Δ ⊢ subst σ (` x) ⦂ A
-- -- ```

-- -- The `exts` function sends well-typed substitutions from Γ to Δ to
-- -- well-typed substitutions from (Γ , B) to (Δ , B). In the case for `S`,
-- -- we note that `exts σ (suc x) ≡ rename sub (σ x)`, so we need to prove
-- -- `Δ , B ⊢ rename suc (σ x) ⦂ A`, which we obtain by the `rename-pres`
-- -- lemma.

-- -- ```agda
-- -- exts-pres : ∀ {Γ Δ σ B}
-- --   → σ ⦂ Γ ⇒ Δ
-- --     --------------------------------
-- --   → exts σ ⦂ (Γ , B) ⇒ (Δ , B)
-- -- exts-pres {σ = σ} σ⦂ Z = ⊢` Z
-- -- exts-pres {σ = σ} σ⦂ (S {x = x} ∋x) = rename-pres {ρ = suc} S (σ⦂ ∋x)
-- -- ```

-- -- Now we prove that both `subst` and `subst-vec` preserve types.  We use
-- -- the `exts-pres` lemma in each of the cases with a variable binding:
-- -- `⊢ƛ`, `⊢μ`, and `⊢case`.
-- -- ```agda
-- -- subst-vec-pres : ∀ {Γ Δ σ}{n}{Ms : Vec Term n}{A}
-- --   → σ ⦂ Γ ⇒ Δ  →  Γ ⊢* Ms ⦂ A  →  Δ ⊢* subst-vec σ Ms ⦂ A

-- -- subst-pres : ∀ {Γ Δ σ N A}
-- --   → σ ⦂ Γ ⇒ Δ
-- --   → Γ ⊢ N ⦂ A
-- --     -----------------
-- --   → Δ ⊢ subst σ N ⦂ A
-- -- subst-pres σ⦂ (⊢` eq)            = σ⦂ eq
-- -- subst-pres {σ = σ} σ⦂ (⊢ƛ ⊢N)    = ⊢ƛ (subst-pres{σ = exts σ}(exts-pres {σ = σ} σ⦂) ⊢N)
-- -- subst-pres {σ = σ} σ⦂ (⊢· ⊢L ⊢M) = ⊢· (subst-pres{σ = σ} σ⦂ ⊢L) (subst-pres{σ = σ} σ⦂ ⊢M)
-- -- subst-pres {σ = σ} σ⦂ (⊢μ ⊢M)    = ⊢μ (subst-pres{σ = exts σ} (exts-pres{σ = σ} σ⦂) ⊢M)
-- -- subst-pres σ⦂ (⊢rcd ⊢Ms dls) = ⊢rcd (subst-vec-pres σ⦂ ⊢Ms ) dls
-- -- subst-pres {σ = σ} σ⦂ (⊢# {d = d} ⊢M lif liA) =
-- --     ⊢# {d = d} (subst-pres {σ = σ} σ⦂ ⊢M) lif liA
-- -- subst-pres {σ = σ} σ⦂ (⊢<: ⊢N lt) = ⊢<: (subst-pres {σ = σ} σ⦂ ⊢N) lt
-- -- subst-pres σ⦂ ⊢zero = ⊢zero
-- -- subst-pres σ⦂ (⊢suc ⊢M) = ⊢suc (subst-pres σ⦂ ⊢M)
-- -- subst-pres σ⦂ (⊢case ⊢L ⊢M ⊢N) =
-- --     ⊢case (subst-pres σ⦂ ⊢L) (subst-pres σ⦂ ⊢M) (subst-pres (exts-pres σ⦂) ⊢N)

-- -- subst-vec-pres σ⦂ ⊢*-[] = ⊢*-[]
-- -- subst-vec-pres {σ = σ} σ⦂ (⊢*-∷ ⊢M ⊢Ms) =
-- --     ⊢*-∷ (subst-pres {σ = σ} σ⦂ ⊢M) (subst-vec-pres σ⦂ ⊢Ms)
-- -- ```

-- -- The fact that single substitution preserves types is a corollary
-- -- of `subst-pres`.
-- -- ```agda
-- -- substitution : ∀{Γ A B M N}
-- --    → Γ ⊢ M ⦂ A
-- --    → (Γ , A) ⊢ N ⦂ B
-- --      ---------------
-- --    → Γ ⊢ N [ M ] ⦂ B
-- -- substitution {Γ}{A}{B}{M}{N} ⊢M ⊢N = subst-pres {σ = subst-zero M} G ⊢N
-- --     where
-- --     G : ∀ {C : Type} {x : ℕ}
-- --       → (Γ , A) ∋ x ⦂ C → Γ ⊢ subst (subst-zero M) (` x) ⦂ C
-- --     G {C} {zero} Z = ⊢M
-- --     G {C} {suc x} (S ∋x) = ⊢` ∋x
-- -- ```

-- -- We require just one last lemma before we get to the proof of preservation.
-- -- The following lemma establishes that field access preserves types.
-- -- ```agda
-- -- field-pres : ∀{n}{As : Vec Type n}{A}{Ms : Vec Term n}{i : Fin n}
-- --          → ∅ ⊢* Ms ⦂ As
-- --          → lookup As i ≡ A
-- --          → ∅ ⊢ lookup Ms i ⦂ A
-- -- field-pres {i = zero} (⊢*-∷ ⊢M ⊢Ms) refl = ⊢M
-- -- field-pres {i = suc i} (⊢*-∷ ⊢M ⊢Ms) As[i]=A = field-pres ⊢Ms As[i]=A
-- -- ```
-- -- The proof is by induction on the typing derivation.

-- -- * Case `⊢-*-[]`: This case yields a contradiction because `Fin 0` is uninhabitable.

-- -- * Case `⊢-*-∷`: So we have `∅ ⊢ M ⦂ B` and `∅ ⊢* Ms ⦂ As`. We proceed by cases on `i`.

-- --     * If it is `0`, then lookup yields term `M` and `A ≡ B`, so we conclude that `∅ ⊢ M ⦂ A`.

-- --     * If it is `suc i`, then we conclude by the induction hypothesis.


-- -- We conclude this chapter with the proof of preservation. We discuss
-- -- the cases particular to records and subtyping in the paragraph
-- -- following the Agda proof.
-- -- ```agda
-- -- preserve : ∀ {M N A}
-- --   → ∅ ⊢ M ⦂ A
-- --   → M —→ N
-- --     ----------
-- --   → ∅ ⊢ N ⦂ A
-- -- preserve (⊢` ())
-- -- preserve (⊢ƛ ⊢N)                 ()
-- -- preserve (⊢· ⊢L ⊢M)              (ξ-·₁ L—→L′)     =  ⊢· (preserve ⊢L L—→L′) ⊢M
-- -- preserve (⊢· ⊢L ⊢M)              (ξ-·₂ VL M—→M′)  =  ⊢· ⊢L (preserve ⊢M M—→M′)
-- -- preserve (⊢· ⊢L ⊢M)              (β-ƛ VL)
-- --     with canonical ⊢L V-ƛ
-- -- ... | C-ƛ ⊢N (<:-fun CA BC)                       =  ⊢<: (substitution (⊢<: ⊢M CA) ⊢N) BC
-- -- preserve ⊢zero                   ()
-- -- preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
-- -- preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
-- -- preserve (⊢case ⊢L ⊢M ⊢N)        (β-zero)         =  ⊢M
-- -- preserve (⊢case ⊢L ⊢M ⊢N)        (β-suc VV)
-- --     with canonical ⊢L (V-suc VV)
-- -- ... | C-suc CV                                    =  substitution (typed CV) ⊢N
-- -- preserve (⊢μ ⊢M)                 (β-μ)            =  substitution (⊢μ ⊢M) ⊢M
-- -- preserve (⊢# {d = d} ⊢M lsi Asi) (ξ-# M—→M′)      =  ⊢# {d = d} (preserve ⊢M M—→M′) lsi Asi
-- -- preserve (⊢# {ls = ls}{i = i} ⊢M refl refl) (β-# {ls = ks}{Ms}{j = j} ks[j]=l)
-- --     with canonical ⊢M V-rcd
-- -- ... | C-rcd {As = Bs} ⊢Ms dks (<:-rcd {ks = ks} ls⊆ks Bs<:As)
-- --     with lookup-⊆ {i = i} ls⊆ks
-- -- ... | ⟨ k , ls[i]=ks[k] ⟩
-- --     with field-pres {i = k} ⊢Ms refl
-- -- ... | ⊢Ms[k]⦂Bs[k]
-- --     rewrite distinct-lookup-inj dks (trans ks[j]=l ls[i]=ks[k]) =
-- --     let Ms[k]⦂As[i] = ⊢<: ⊢Ms[k]⦂Bs[k] (Bs<:As (sym ls[i]=ks[k])) in
-- --     Ms[k]⦂As[i]
-- -- preserve (⊢<: ⊢M B<:A) M—→N                       =  ⊢<: (preserve ⊢M M—→N) B<:A
-- -- ```
-- -- Recall that the proof is by induction on the derivation of `∅ ⊢ M ⦂ A`
-- -- with cases on `M —→ N`.

-- -- * Case `⊢#` and `ξ-#`: So `∅ ⊢ M ⦂ ⦗ ls ⦂ As ⦘`, `lookup ls i ≡ l`, `lookup As i ≡ A`,
-- --   and `M —→ M′`. We apply the induction hypothesis to obtain `∅ ⊢ M′ ⦂ ⦗ ls ⦂ As ⦘`
-- --   and then conclude by rule `⊢#`.

-- -- * Case `⊢#` and `β-#`. We have `∅ ⊢ ⦗ ks := Ms ⦘ ⦂ ⦗ ls ⦂ As ⦘`, `lookup ls i ≡ l`,
-- --   `lookup As i ≡ A`, `lookup ks j ≡ l`, and `⦗ ks := Ms ⦘ # l —→ lookup Ms j`.
-- --   By the canonical forms lemma, we have `∅ ⊢* Ms ⦂ Bs`, `ls ⊆ ks` and `ks ⦂ Bs <: ls ⦂ As`.
-- --   By lemma `lookup-⊆` we have `lookup ls i ≡ lookup ks k` for some `k`.
-- --   Also, we have `∅ ⊢ lookup Ms k ⦂ lookup Bs k` by lemma `field-pres`.
-- --   Then because `ks ⦂ Bs <: ls ⦂ As` and `lookup ks k ≡ lookup ls i`, we have
-- --   `lookup Bs k <: lookup As i`. So by rule `⊢<:` we have
-- --   `∅ ⊢ lookup Ms k ⦂ lookup As i`.
-- --   Finally, because `lookup` is injective and `lookup ks j ≡ lookup ks k`,
-- --   we have `j ≡ k` and conclude that `∅ ⊢ lookup Ms j ⦂ lookup As i`.

-- -- * Case `⊢<:`. We have `∅ ⊢ M ⦂ B`, `B <: A`, and `M —→ N`. We apply the induction hypothesis
-- --   to obtain `∅ ⊢ N ⦂ B` and then subsumption to conclude that `∅ ⊢ N ⦂ A`.


-- -- #### Exercise `intrinsic-records` (stretch)

-- -- Formulate the language of this chapter, STLC with records, using
-- -- intrinsically typed terms. This requires taking an algorithmic approach
-- -- to the type system, which means that there is no subsumption rule and
-- -- instead subtyping is used in the elimination rules. For example,
-- -- the rule for function application would be:

-- --     _·_ : ∀ {Γ A B C}
-- --       → Γ ⊢ A ⇒ B
-- --       → Γ ⊢ C
-- --       → C <: A
-- --         -------
-- --       → Γ ⊢ B

-- -- #### Exercise `type-check-records` (practice)

-- -- Write a recursive function whose input is a `Term` and whose output
-- -- is a typing derivation for that term, if one exists.

-- --     type-check : (M : Term) → (Γ : Context) → Maybe (Σ[ A ∈ Type ] Γ ⊢ M ⦂ A)

-- -- #### Exercise `variants` (recommended)

-- -- Add variants to the language of this chapter and update the proofs of
-- -- progress and preservation. The variant type is a generalization of a
-- -- sum type, similar to the way the record type is a generalization of
-- -- product. The following summarizes the treatment of variants in the
-- -- book Types and Programming Languages. A variant type is traditionally
-- -- written:

-- --     〈l₁:A₁, ..., lᵤ:Aᵤ〉

-- -- The term for introducing a variant is

-- --     〈l=t〉

-- -- and the term for eliminating a variant is

-- --     case L of 〈l₁=x₁〉 ⇒ M₁ | ... | 〈lᵤ=xᵤ〉 ⇒ Mᵤ

-- -- The typing rules for these terms are

-- --     (T-Variant)
-- --     Γ ⊢ Mⱼ : Aⱼ
-- --     ---------------------------------
-- --     Γ ⊢ 〈lⱼ=Mⱼ〉 : 〈l₁=A₁, ... , lᵤ=Aᵤ〉


-- --     (T-Case)
-- --     Γ ⊢ L : 〈l₁=A₁, ... , lᵤ=Aᵤ〉
-- --     ∀ i ∈ 1..u,   Γ,xᵢ:Aᵢ ⊢ Mᵢ : B
-- --     ---------------------------------------------------
-- --     Γ ⊢ case L of 〈l₁=x₁〉 ⇒ M₁ | ... | 〈lᵤ=xᵤ〉 ⇒ Mᵤ  : B

-- -- The non-algorithmic subtyping rules for variants are

-- --     (S-VariantWidth)
-- --     ------------------------------------------------------------
-- --     〈l₁=A₁, ..., lᵤ=Aᵤ〉   <:   〈l₁=A₁, ..., lᵤ=Aᵤ, ..., lᵤ₊ₓ=Aᵤ₊ₓ〉

-- --     (S-VariantDepth)
-- --     ∀ i ∈ 1..u,    Aᵢ <: Bᵢ
-- --     ---------------------------------------------
-- --     〈l₁=A₁, ..., lᵤ=Aᵤ〉   <:   〈l₁=B₁, ..., lᵤ=Bᵤ〉

-- --     (S-VariantPerm)
-- --     ∀i∈1..u, ∃j∈1..u, kⱼ = lᵢ and Aⱼ = Bᵢ
-- --     ----------------------------------------------
-- --     〈k₁=A₁, ..., kᵤ=Aᵤ〉   <:   〈l₁=B₁, ..., lᵤ=Bᵤ〉

-- -- Come up with an algorithmic subtyping rule for variant types.

-- -- #### Exercise `<:-alternative` (stretch)

-- -- Revise this formalisation of records with subtyping (including proofs
-- -- of progress and preservation) to use the non-algorithmic subtyping
-- -- rules for Chapter 15 of Types and Programming Languages, which we list here:

-- --     (S-RcdWidth)
-- --     -------------------------------------------------------------------------
-- --     ⦗ l₁ ⦂ A₁, ..., lᵤ ⦂ Aᵤ, ..., lᵤ₊ₓ ⦂ Aᵤ₊ₓ ⦘ < ⦂  ⦗ l₁ ⦂ A₁, ..., lᵤ ⦂ Aᵤ ⦘

-- --     (S-RcdDepth)
-- --         ∀i∈1..u, Aᵢ <: Bᵢ
-- --     ------------------------------------------------------
-- --     ⦗ l₁ ⦂ A₁, ..., lᵤ ⦂ Aᵤ ⦘ <: ⦗ l₁ ⦂ B₁, ..., lᵤ ⦂ Bᵤ ⦘

-- --     (S-RcdPerm)
-- --     ∀i∈1..u, ∃j∈1..u, kⱼ = lᵢ and Aⱼ = Bᵢ
-- --     ------------------------------------------------------
-- --     ⦗ k₁ ⦂ A₁, ..., kᵤ ⦂ Aᵤ ⦘ <: ⦗ l₁ ⦂ B₁, ..., lᵤ ⦂ Bᵤ ⦘

-- -- You will most likely need to prove inversion lemmas for the subtype relation
-- -- of the form:

-- --     If S <: T₁ ⇒ T₂, then S ≡ S₁ ⇒ S₂, T₁ <: S₁, and S₂ <: T₂, for some S₁, S₂.

-- --     If S <: ⦗ lᵢ ⦂ Tᵢ | i ∈ 1..n ⦘, then S ≡ ⦗ kⱼ ⦂ Sⱼ | j ∈ 1..m ⦘
-- --     and { lᵢ | i ∈ 1..n } ⊆ { kⱼ | j ∈ 1..m }
-- --     and Sⱼ <: Tᵢ for every i and j such that lᵢ = kⱼ.

-- -- ## References

-- -- * John C. Reynolds. Using Category Theory to Design Implicit
-- --   Conversions and Generic Operators.
-- --   In Semantics-Directed Compiler Generation, 1980.
-- --   LNCS Volume 94.

-- -- * Luca Cardelli. A semantics of multiple inheritance.  In Semantics of
-- --   Data Types, 1984. Springer.

-- -- * Barbara H. Liskov and Jeannette M. Wing.  A Behavioral Notion of
-- --   Subtyping. In ACM Trans. Program. Lang. Syst.  Volume 16, 1994.

-- -- * Types and Programming Languages. Benjamin C. Pierce. The MIT Press. 2002.

-- -- ## Unicode

-- -- This chapter uses the following unicode:

-- --     ⦗  U+2997  LEFT BLACK TORTOISE SHELL BRACKET (\()
-- --     ⦘  U+2997  RIGHT BLACK TORTOISE SHELL BRACKET (\))
-- --     ⦂  U+2982  Z NOTATION TYPE COLON (\:)
-- --     ⊆  U+2286  SUBSET OF OR EQUAL TO (\sub=)
-- --     ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
-- --     ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
-- --     μ  U+03BC  GREEK SMALL LETTER MU (\mu)
-- --     ·  U+00B7  MIDDLE DOT (\cdot)
-- --     ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
-- --     ∋  U+220B  CONTAINS AS MEMBER (\ni)
-- --     →  U+2192  RIGHTWARDS ARROW (\to)
-- --     —  U+2014  EM DASH (\em)
