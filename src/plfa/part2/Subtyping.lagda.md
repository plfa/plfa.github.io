---
title     : "Subtyping: Records"
layout    : page
prev      : /More/
permalink : /Subtyping/
next      : /Bisimulation/
---

```
module plfa.part2.Subtyping where
```

This chapter introduces *subtyping*, a concept that plays an important
role in object-oriented languages. Subtyping enables code to be more
reusable by allowing it to work on objects of many different
types. Thus, subtyping provides a kind of polymorphism. In general, a
type `A` can be a subtype of another type `B`, written `A <: B`, when
an object of type `A` has all the capabilities expected of something
of type `B`. Or put another way, a type `A` can be a subtype of type
`B` when it is safe to substitute something of type `A` into code that
expects something of type `B`.  This is know as the *Liskov
Substitution Principle*. Given this semantic meaning of subtyping, a
subtype relation should always be reflexive and transitive. When
`A` is a subtype of `B`, that is, `A <: B`, we may also refer to
`B` as a supertype of `A`.

To formulate a type system for a language with subtyping, one simply
adds the *subsumption rule*, which states that a term of type `A`
can also have type `B` if `A` is a subtype of `B`.

    ⊢<: : ∀{Γ M A B}
      → Γ ⊢ M ⦂ A
    → A <: B
        -----------
      → Γ ⊢ M ⦂ B

In this chapter we study subtyping in the relatively simple context of
records and record types.  A *record* is a grouping of named values,
called *fields*. For example, one could represent a point on the
Cartesian plane with the following record.

    { x = 4, y = 1 }

A *record type* gives a type for each field. In the following, we
specify that the fields `x` and `y` both have type `ℕ`.

    { x : `ℕ,  y : `ℕ }

One record type is a subtype of another if it has all of the fields of
the supertype and if the types of those fields are subtypes of the
corresponding fields in the supertype. So, for example, a point in
three dimensions is a subtype of a point in two dimensions.

    { x : `ℕ,  y : `ℕ, z : `ℕ } <: { x : `ℕ,  y : `ℕ }

The elimination form for records is field access (aka. projection),
written `M # l`, and whose dynamic semantics is defined by the
following reduction rule, which says that accessing the field `lⱼ`
returns the value stored at that field.

    {l₁=v₁, ..., lⱼ=vⱼ, ..., lᵢ=vᵢ} # lⱼ —→  vⱼ

In this chapter we add records and record types to the simply typed
lambda calculus (STLC) and prove type safety. It is instructive to see
how the proof of type safety changes to handle subtyping.  Also, the
presence of subtyping makes the choice between extrinsic and intrinsic
typing more interesting by. If we wish to include the subsumption
rule, then we cannot use intrinsically typed terms, as intrinsic terms
only allow for syntax-directed rules, and subsumption is not syntax
directed.  A standard alternative to the subsumption rule is to
instead use subtyping in the typing rules for the elimination forms,
an approach called algorithmic typing. Here we choose to include the
subsumption rule and extrinsic typing, but we give an exercise at the
end of the chapter so the reader can explore algorithmic typing with
intrinsic terms.


## Imports

```
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_; _+_)
open import Data.Nat.Properties
    using (m+n≤o⇒m≤o; m+n≤o⇒n≤o; n≤0⇒n≡0; ≤-pred; ≤-refl; ≤-trans; m≤m+n; n≤m+n)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Data.Vec.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.Vec.Membership.Propositional.Properties using (∈-lookup)
open import Data.Vec.Relation.Unary.Any using (here; there)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)
```

## Syntax

The syntax includes that of the STLC with a few additions regarding
records that we explain in the following sections.

```
infixl 5 _,_
infix 4 _⊆_
infix 5 _<:_
infix  4 _⊢_⦂_
infix 4 _⊢*_⦂_
infix  4 _∋_⦂_
infix  4 Canonical_⦂_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infixl 7 _#_
infix 5 ｛_⦂_｝
infix 5 ｛_:=_｝

infix 5 _[_]
infix 2 _—→_
```

## Record Fields and their Properties

We represent field names as strings.

```
Name : Set
Name = String
```

A record is traditionally written as follows

    { l₁ = M₁, ..., lᵢ = Mᵢ }

so a natural representation is a list of label-term pairs.
However, we find it more convenient to represent records as a pair of
vectors (Agda's `Vec` type), one vector of fields and one vector of terms:

    l₁, ..., lᵢ
    M₁, ..., Mᵢ

This representation has the advantage that the traditional subscript
notation `lᵢ` corresponds to indexing into a vector.

Likewise, a record type, traditionally written as

    { l₁ : A₁, ..., lᵢ : Aᵢ }

will be represented as a pair of vectors, one vector of fields and one
vector of types.

    l₁, ..., lᵢ
    A₁, ..., Aᵢ

The field names of a record type must be distinct, which we define as
follows.
```
distinct : ∀{A : Set}{n} → Vec A n → Set
distinct [] = ⊤
distinct (x ∷ xs) = ¬ (x ∈ xs) × distinct xs
```

For vectors of distinct elements, lookup is injective.
```
distinct-lookup-inj : ∀ {n}{ls : Vec Name n}{i j : Fin n}
   → distinct ls  →  lookup ls i ≡ lookup ls j
   → i ≡ j
distinct-lookup-inj {ls = x ∷ ls} {zero} {zero} ⟨ x∉ls , dls ⟩ lsij = refl
distinct-lookup-inj {ls = x ∷ ls} {zero} {suc j} ⟨ x∉ls , dls ⟩ refl =
    ⊥-elim (x∉ls (∈-lookup j ls))
distinct-lookup-inj {ls = x ∷ ls} {suc i} {zero} ⟨ x∉ls , dls ⟩ refl =
    ⊥-elim (x∉ls (∈-lookup i ls))
distinct-lookup-inj {ls = x ∷ ls} {suc i} {suc j} ⟨ x∉ls , dls ⟩ lsij =
    cong suc (distinct-lookup-inj dls lsij)
```

We shall need to convert from an irrelevant proof of distinctness to a
relevant one. In general, the laundering of irrelevant proofs into
relevant ones is easy to do when the predicate in question is
decidable. The following is a decision procedure for whether a vector
is distinct.
```
distinct? : ∀{n} → (xs : Vec Name n) → Dec (distinct xs)
distinct? [] = yes tt
distinct? (x ∷ xs)
    with x ∈? xs
... | yes x∈xs = no λ z → proj₁ z x∈xs
... | no x∉xs
    with distinct? xs
... | yes dxs = yes ⟨ x∉xs , dxs ⟩
... | no ¬dxs = no λ z → ¬dxs (proj₂ z)
```

With this decision procedure in hand, we define the following
function for laundering irrelevant proofs of distinctness into
relevant ones.
```
distinct-relevant : ∀ {n}{fs : Vec Name n} .(d : distinct fs) → distinct fs
distinct-relevant {n}{fs} d
    with distinct? fs
... | yes dfs = dfs
... | no ¬dfs = ⊥-elimi (¬dfs d)
```

The fields of one record are a *subset* of the fields of another
record if every field of the first is also a field of the second.
```
_⊆_ : ∀{n m} → Vec Name n → Vec Name m → Set
xs ⊆ ys = (x : Name) → x ∈ xs → x ∈ ys
```

This subset relation is reflexive and transitive.
```
⊆-refl : ∀{n}{ls : Vec Name n} → ls ⊆ ls
⊆-refl {n}{ls} = λ x x∈ls → x∈ls

⊆-trans : ∀{l n m}{ns  : Vec Name n}{ms  : Vec Name m}{ls  : Vec Name l}
   → ns ⊆ ms  →  ms ⊆ ls  →  ns ⊆ ls
⊆-trans {l}{n}{m}{ns}{ms}{ls} ns⊆ms ms⊆ls = λ x z → ms⊆ls x (ns⊆ms x z)
```

If `y` is an element of vector `xs`, then `y` is at some index `i` of
the vector.
```
lookup-∈ : ∀{ℓ}{A : Set ℓ}{n} {xs : Vec A n}{y}
   → y ∈ xs
   → Σ[ i ∈ Fin n ] lookup xs i ≡ y
lookup-∈ {xs = x ∷ xs} (here refl) = ⟨ zero , refl ⟩
lookup-∈ {xs = x ∷ xs} (there y∈xs)
    with lookup-∈ y∈xs
... | ⟨ i , xs[i]=y ⟩ = ⟨ (suc i) , xs[i]=y ⟩
```

If one vector `ns` is a subset of another `ms`, then for any element
`lookup ns i`, there is an equal element in `ms` at some index.
```
lookup-⊆ : ∀{n m : ℕ}{ns : Vec Name n}{ms : Vec Name m}{i : Fin n}
   → ns ⊆ ms
   → Σ[ k ∈ Fin m ] lookup ns i ≡ lookup ms k
lookup-⊆ {suc n} {m} {x ∷ ns} {ms} {zero} ns⊆ms
    with lookup-∈ (ns⊆ms x (here refl))
... | ⟨ k , ms[k]=x ⟩ =
      ⟨ k , (sym ms[k]=x) ⟩
lookup-⊆ {suc n} {m} {x ∷ ns} {ms} {suc i} x∷ns⊆ms =
    lookup-⊆ {n} {m} {ns} {ms} {i} (λ x z → x∷ns⊆ms x (there z))
```

## Types

```
data Type : Set where
  _⇒_   : Type → Type → Type
  `ℕ    : Type
  ｛_⦂_｝ : {n : ℕ} (ls : Vec Name n) (As : Vec Type n) → .{d : distinct ls} → Type
```

In addition to function types `A ⇒ B` and natural numbers `ℕ`, we
have the record type `｛ ls ⦂ As ｝`, where `ls` is a vector of field
names and `As` is a vector of types, as discussed above.  We require
that the field names be distinct, but we do not want the details of
the proof of distinctness to affect whether two record types are
equal, so we declare that parameter to be irrelevant by placing a `.`
in front of it.


## Subtyping

The subtyping relation, written `A <: B`, defines when an implicit
cast is allowed via the subsumption rule. The following data type
definition specifies the subtyping rules for natural numbers,
functions, and record types. We discuss each rule below.

```
data _<:_ : Type → Type → Set where
  <:-nat : `ℕ <: `ℕ

  <:-fun : ∀{A B C D : Type}
    → C <: A  → B <: D
      ----------------
    → A ⇒ B <: C ⇒ D

  <:-rcd :  ∀{m}{ks : Vec Name m}{Ss : Vec Type m}.{d1 : distinct ks}
             {n}{ls : Vec Name n}{Ts : Vec Type n}.{d2 : distinct ls}
    → ls ⊆ ks
    → (∀{i : Fin n}{j : Fin m} → lookup ks j ≡ lookup ls i
                               → lookup Ss j <: lookup Ts i)
      ------------------------------------------------------
    → ｛ ks ⦂ Ss ｝ {d1} <: ｛ ls ⦂ Ts ｝ {d2}
```

The rule `<:-nat` says that `ℕ` is a subtype of itself.

The rule `<:-fun` is the traditional rule for function types, which is
best understood with the below diagram. It answers the question, when
can a function of type `A ⇒ B` be used in place of a function of type
`C ⇒ D`. It will be called with an argument of type `C`, so we need to
convert from `C` to `A`. We then call the function to get the result
of type `B`. Finally, we need to convert from `B` to `D`. Note that
the direction of subtyping for the parameters is swapped (`C <: A`), a
phenomenon named contra-variance.

    C <: A
    ⇓    ⇓
    D :> B

The record subtyping rule (`<:-rcd`) characterizes when a record of
one type can safely be used in place of another record type.  The
first premise of the rule expresses _width subtyping_ by requiring
that all the field names in `ls` are also in `ks`. So it allows the
hiding of fields when going from a subtype to a supertype.
The second premise of the record subtyping rule (`<:-rcd`) expresses
_depth subtyping_, that is, it allows the types of the fields to
change according to subtyping. The following is an abbreviation for
this premise.
```
_⦂_<:_⦂_ : ∀ {m n} → Vec Name m → Vec Type m → Vec Name n → Vec Type n → Set
_⦂_<:_⦂_ {m}{n} ks Ss ls Ts = (∀{i : Fin n}{j : Fin m}
    → lookup ks j ≡ lookup ls i  →  lookup Ss j <: lookup Ts i)
```

## Subtyping is Reflexive

In this section we prove that subtyping is reflexive, that is, `A <:
A` for any type `A`. The proof does not go by induction on the type
`A` because of the `<:-rcd` rule. We instead use induction on the size
of the type. So we first define size of a type, and the size of a
vector of types, as follows.
```
ty-size : (A : Type) → ℕ
vec-ty-size : ∀ {n : ℕ} → (As : Vec Type n) → ℕ

ty-size (A ⇒ B) = suc (ty-size A + ty-size B)
ty-size `ℕ = 1
ty-size ｛ ls ⦂ As ｝ = suc (vec-ty-size As)
vec-ty-size {n} [] = 0
vec-ty-size {n} (x ∷ xs) = ty-size x + vec-ty-size xs
```

The size of a type is always positive.
```
ty-size-pos : ∀ {A} → 0 < ty-size A
ty-size-pos {A ⇒ B} = s≤s z≤n
ty-size-pos {`ℕ} = s≤s z≤n
ty-size-pos {｛ fs ⦂ As ｝ } = s≤s z≤n
```

The size of a type in a vector is less-or-equal in size to the entire vector.
```
lookup-vec-ty-size : ∀{k} {As : Vec Type k} {j}
   → ty-size (lookup As j) ≤ vec-ty-size As
lookup-vec-ty-size {suc k} {A ∷ As} {zero} = m≤m+n _ _
lookup-vec-ty-size {suc k} {A ∷ As} {suc j} = ≤-trans (lookup-vec-ty-size {k} {As}) (n≤m+n _ _)
```

Here is the proof of reflexivity, by induction on the size of the type.
```
<:-refl-aux : ∀{n}{A}{m : ty-size A ≤ n} → A <: A
<:-refl-aux {0}{A}{m}
    with ty-size-pos {A}
... | pos rewrite n≤0⇒n≡0 m
    with pos
... | ()
<:-refl-aux {suc n}{`ℕ}{m} = <:-nat
<:-refl-aux {suc n}{A ⇒ B}{m} =
  let A<:A = <:-refl-aux {n}{A}{m+n≤o⇒m≤o _ (≤-pred m) } in
  let B<:B = <:-refl-aux {n}{B}{m+n≤o⇒n≤o _ (≤-pred m) } in
  <:-fun A<:A B<:B
<:-refl-aux {suc n}{｛ ls ⦂ As ｝ {d} }{m} = <:-rcd {d1 = d}{d2 = d} ⊆-refl G
    where
    G : ls ⦂ As <: ls ⦂ As
    G {i}{j} lij rewrite distinct-lookup-inj (distinct-relevant d) lij =
        let As[i]≤n = ≤-trans (lookup-vec-ty-size {As = As}{i}) (≤-pred m) in
        <:-refl-aux {n}{lookup As i}{As[i]≤n}
```
The theorem statement uses `n` as an upper bound on the size of the type `A`
and proceeds by induction on `n`.

* If it is `0`, then we have a contradiction because the size of a type is always positive.

* If it is `suc n`, we proceed by cases on the type `A`.

  * If it is `ℕ`, then we have `ℕ <: ℕ` by rule `<:-nat`.
  * If it is `A ⇒ B`, then by induction we have `A <: A` and `B <: B`.
    We conclude that `A ⇒ B <: A ⇒ B` by rule `<:-fun`.
  * If it is `｛ ls ⦂ As ｝`, then it suffices to prove that
    `ls ⊆ ls` and `ls ⦂ As <: ls ⦂ As`. The former is proved by `⊆-refl`.
    Regarding the latter, we need to show that for any `i` and `j`,
    `lookup ls j ≡ lookup ls i` implies `lookup As j <: lookup As i`.
    Because `lookup` is injective on distinct vectors, we have `i ≡ j`.
    We then use the induction hypothesis to show that
    `lookup As i <: lookup As i`, noting that the size of
    `lookup As i` is less-than-or-equal to the size of `As`, which
    is one smaller than the size of `｛ ls ⦂ As ｝`.

The following corollary packages up reflexivity for ease of use.
```
<:-refl : ∀{A} → A <: A
<:-refl {A} = <:-refl-aux {ty-size A}{A}{≤-refl}
```

## Subtyping is transitive

```
<:-trans : ∀{A B C}
    → A <: B   →   B <: C
      -------------------
    → A <: C
<:-trans {A₁ ⇒ A₂} {B₁ ⇒ B₂} {C₁ ⇒ C₂} (<:-fun A₁<:B₁ A₂<:B₂) (<:-fun B₁<:C₁ B₂<:C₂) =
    <:-fun (<:-trans B₁<:C₁ A₁<:B₁) (<:-trans A₂<:B₂ B₂<:C₂)
<:-trans {.`ℕ} {`ℕ} {.`ℕ} <:-nat <:-nat = <:-nat
<:-trans {｛ ls ⦂ As ｝{d1} } {｛ ms ⦂ Bs ｝ {d2} } {｛ ns ⦂ Cs ｝ {d3} }
    (<:-rcd ms⊆ls As<:Bs) (<:-rcd ns⊆ms Bs<:Cs) =
    <:-rcd (⊆-trans ns⊆ms ms⊆ls) As<:Cs
    where
    As<:Cs : ls ⦂ As <: ns ⦂ Cs
    As<:Cs {i}{j} ls[j]=ns[i]
        with lookup-⊆ {i = i} ns⊆ms
    ... | ⟨ k , ns[i]=ms[k] ⟩ =
        let As[j]<:Bs[k] = As<:Bs {k}{j} (trans ls[j]=ns[i] ns[i]=ms[k]) in
        let Bs[k]<:Cs[i] = Bs<:Cs {i}{k} (sym ns[i]=ms[k]) in
        <:-trans As[j]<:Bs[k] Bs[k]<:Cs[i]
```

The proof is by induction on the derivations of `A <: B` and `B <: C`.

* If both derivations end with `<:-nat`: then we immediately conclude that `ℕ <: ℕ`.

* If both derivations end with `<:-fun`:
  we have `A₁ ⇒ A₂ <: B₁ ⇒ B₂` and  `B₁ ⇒ B₂ <: C₁ ⇒ C₂`.
  So `A₁ <: B₁` and `B₁ <: C₁`, thus `A₁ <: C₁` by the induction hypothesis.
  We also have `A₂ <: B₂` and `B₂ <: C₂`, so by the induction hypothesis
  we have `A₂ <: C₂`. We conclude that `A₁ ⇒ A₂ <: C₁ ⇒ C₂` by rule `<:-fun`.

* If both derivations end with `<:-rcd`, so we have
  `｛ ls ⦂ As ｝ <: ｛ ms ⦂ Bs ｝` and `｛ ms ⦂ Bs ｝ <: ｛ ns ⦂ Cs ｝`.
  From `ls ⊆ ms` and `ms ⊆ ns` we have `ls ⊆ ns` because `⊆` is transitive.
  Next we need to prove that `ls ⦂ As <: ns ⦂ Cs`.
  Suppose `lookup ls j ≡ lookup ns i` for an arbitrary `i` and `j`.
  We need to prove that `lookup As j <: lookup Cs i`.
  By the induction hypothesis, it suffices to show
  that `lookup As j <: lookup Bs k` and `lookup Bs k <: lookup Cs i` for some `k`.
  We can obtain the former from `｛ ls ⦂ As ｝ <: ｛ ms ⦂ Bs ｝`
  if we can prove that `lookup ls j ≡ lookup ms k`.
  We already have `lookup ls j ≡ lookup ns i` and we
  obtain `lookup ns i ≡ lookup ms k` by use of the lemma `lookup-⊆`,
  noting that `ns ⊆ ms`.
  We can obtain the later, that `lookup Bs k <: lookup Cs i`,
  from `｛ ms ⦂ Bs ｝ <: ｛ ns ⦂ Cs ｝`.
  It suffices to show that `lookup ms k ≡ lookup ns i`,
  which we have by symmetry.


## Contexts

We choose to represent variables with de Bruijn indices, so contexts
are sequences of types.

```
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

## Variables and the lookup judgment

The lookup judgment is a three-place relation, with a context, a de
Bruijn index, and a type.

```
data _∋_⦂_ : Context → ℕ → Type → Set where

  Z : ∀ {Γ A}
      ------------------
    → Γ , A ∋ 0 ⦂ A

  S : ∀ {Γ x A B}
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , B ∋ (suc x) ⦂ A
```

* The index `0` has the type at the front of the context.

* For the index `suc x`, we recursively look up its type in the
  remaining context `Γ`.


## Terms and the typing judgment

As mentioned above, variables are de Bruijn indices, which we
represent with natural numbers.

```
Id : Set
Id = ℕ
```

Our terms are extrinsic, so we define a `Term` data type similar to
the one in the [Lambda](/Lambda/) chapter, but adapted for de
Bruijn indices.  The two new term constructors are for record creation
and field access.

```
data Term : Set where
  `_                      : Id → Term
  ƛ_                      : Term → Term
  _·_                     : Term → Term → Term
  `zero                   : Term
  `suc_                   : Term → Term
  case_[zero⇒_|suc⇒_]     : Term → Term → Term → Term
  μ_                      : Term → Term
  ｛_:=_｝                 : {n : ℕ} (ls : Vec Name n) (Ms : Vec Term n) → Term
  _#_                     : Term → Name → Term
```

In a record `｛ ls := Ms ｝`, we refer to the vector of terms `Ms` as
the *field initializers*.

The typing judgment takes the form `Γ ⊢ M ⦂ A` and relies on an
auxiliary judgment `Γ ⊢* Ms ⦂ As` for typing a vector of terms.

```
data _⊢*_⦂_ : Context → ∀ {n} → Vec Term n → Vec Type n → Set

data _⊢_⦂_ : Context → Term → Type → Set where

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  ⊢ƛ  : ∀ {Γ A B N}
    → (Γ , A) ⊢ N ⦂ B
      ---------------
    → Γ ⊢ (ƛ N) ⦂ A ⇒ B

  ⊢· : ∀ {Γ A B L M}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  ⊢case : ∀ {Γ A L M N}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , `ℕ ⊢ N ⦂ A
      ---------------------------------
    → Γ ⊢ case L [zero⇒ M |suc⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ A M}
    → Γ , A ⊢ M ⦂ A
      -------------
    → Γ ⊢ μ M ⦂ A

  ⊢rcd : ∀ {Γ n}{Ms : Vec Term n}{As : Vec Type n}{ls : Vec Name n}
     → Γ ⊢* Ms ⦂ As
     → (d : distinct ls)
     → Γ ⊢ ｛ ls := Ms ｝ ⦂ ｛ ls ⦂ As ｝ {d}


  ⊢# : ∀ {n : ℕ}{Γ A M l}{ls : Vec Name n}{As : Vec Type n}{i}{d}
     → Γ ⊢ M ⦂ ｛ ls ⦂ As ｝{d}
     → lookup ls i ≡ l
     → lookup As i ≡ A
     → Γ ⊢ M # l ⦂ A

  ⊢<: : ∀{Γ M A B}
    → Γ ⊢ M ⦂ A   → A <: B
      --------------------
    → Γ ⊢ M ⦂ B

data _⊢*_⦂_ where
  ⊢*-[] : ∀{Γ} → Γ ⊢* [] ⦂ []

  ⊢*-∷ : ∀ {n}{Γ M}{Ms : Vec Term n}{A}{As : Vec Type n}
     → Γ ⊢ M ⦂ A
     → Γ ⊢* Ms ⦂ As
     → Γ ⊢* (M ∷ Ms) ⦂ (A ∷ As)
```

Most of the typing rules are adapted from those in the [Lambda](/Lambda/)
chapter. Here we discuss the three new rules.

* Rule `⊢rcd`: A record is well-typed if the field initializers `Ms`
  have types `As`, to match the record type. Also, the vector of field
  names is required to be distinct.

* Rule `⊢#`: A field access is well-typed if the term `M` has record type,
  the field `l` is at some index `i` in the record type's vector of field names,
  and the result type `A` is at index `i` in the vector of field types.

* Rule `⊢<:`: (Subsumption) If a term `M` has type `A`, and `A <: B`,
  then term `M` also has type `B`.


## Renaming and Substitution

In preparation of defining the reduction rules for this language, we
define simultaneous substitution using the same recipe as in the
[DeBruijn](/DeBruijn/) chapter, but adapted to extrinsic
terms. Thus, the `subst` function is split into two parts: a raw
`subst` function that operators on terms and a `subst-pres` lemma that
proves that substitution preserves types. We define `subst` in this
section and postpone `subst-pres` to the
[Preservation](#subtyping-preservation) section.  Likewise for `rename`.

We begin by defining the `ext` function on renamings.
```
ext : (Id → Id) → (Id → Id)
ext ρ 0      =  0
ext ρ (suc x)  =  suc (ρ x)
```

The `rename` function is defined mutually with the auxiliary
`rename-vec` function, which is needed in the case for records.
```
rename-vec : (Id → Id) → ∀{n} → Vec Term n → Vec Term n

rename : (Id → Id) → (Term → Term)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L [zero⇒ M |suc⇒ N ]) =
    case (rename ρ L) [zero⇒ rename ρ M |suc⇒ rename (ext ρ) N ]
rename ρ (μ N)          =  μ (rename (ext ρ) N)
rename ρ ｛ ls := Ms ｝ = ｛ ls := rename-vec ρ Ms ｝
rename ρ (M # l)       = (rename ρ M) # l

rename-vec ρ [] = []
rename-vec ρ (M ∷ Ms) = rename ρ M ∷ rename-vec ρ Ms
```

With the `rename` function in hand, we can define the `exts` function
on substitutions.
```
exts : (Id → Term) → (Id → Term)
exts σ 0      =  ` 0
exts σ (suc x)  =  rename suc (σ x)
```

We define `subst` mutually with the auxiliary `subst-vec` function,
which is needed in the case for records.
```
subst-vec : (Id → Term) → ∀{n} → Vec Term n → Vec Term n

subst : (Id → Term) → (Term → Term)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L [zero⇒ M |suc⇒ N ])
                       =  case (subst σ L) [zero⇒ subst σ M |suc⇒ subst (exts σ) N ]
subst σ (μ N)          =  μ (subst (exts σ) N)
subst σ ｛ ls := Ms ｝  = ｛ ls := subst-vec σ Ms ｝
subst σ (M # l)        = (subst σ M) # l

subst-vec σ [] = []
subst-vec σ (M ∷ Ms) = (subst σ M) ∷ (subst-vec σ Ms)
```

As usual, we implement single substitution using simultaneous
substitution.
```
subst-zero : Term → Id → Term
subst-zero M 0       =  M
subst-zero M (suc x) =  ` x

_[_] : Term → Term → Term
_[_] N M =  subst (subst-zero M) N
```

## Values

We extend the definition of `Value` to include a clause for records.
In a call-by-value language, a record is usually only considered a
value if all its field initializers are values. Here we instead treat
records in a lazy fashion, declaring any record to be a value, to save
on some extra bookkeeping.
```
data Value : Term → Set where

  V-ƛ : ∀ {N}
      -----------
    → Value (ƛ N)

  V-zero :
      -------------
      Value (`zero)

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

  V-rcd : ∀{n}{ls : Vec Name n}{Ms : Vec Term n}
    → Value ｛ ls := Ms ｝
```

## Reduction

The following datatype `_—→_` defines the reduction relation for the
STLC with records. We discuss the two new rules for records in the
following paragraph.

```
data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M : Term}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V  M M′ : Term}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {N W : Term}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {M M′ : Term}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {L L′ M N : Term}
    → L —→ L′
      -------------------------------------------------------
    → case L [zero⇒ M |suc⇒ N ] —→ case L′ [zero⇒ M |suc⇒ N ]

  β-zero :  ∀ {M N : Term}
      ----------------------------------
    → case `zero [zero⇒ M |suc⇒ N ] —→ M

  β-suc : ∀ {V M N : Term}
    → Value V
      -------------------------------------------
    → case (`suc V) [zero⇒ M |suc⇒ N ] —→ N [ V ]

  β-μ : ∀ {N : Term}
      ----------------
    → μ N —→ N [ μ N ]

  ξ-# : ∀ {M M′ : Term}{l}
    → M —→ M′
    → M # l —→ M′ # l

  β-# : ∀ {n}{ls : Vec Name n}{Ms : Vec Term n} {l}{j : Fin n}
    → lookup ls j ≡ l
      ---------------------------------
    → ｛ ls := Ms ｝ # l —→  lookup Ms j
```

We have just two new reduction rules:
* Rule `ξ-#`: A field access expression `M # l` reduces to `M′ # l`
   provided that `M` reduces to `M′`.

* Rule `β-#`: When field access is applied to a record,
   and if the label `l` is at position `j` in the vector of field names,
   then result is the term at position `j` in the field initializers.


## Canonical Forms

As in the [Properties](/Properties/) chapter, we
define a `Canonical V ⦂ A` relation that characterizes the well-typed
values.  The presence of the subsumption rule impacts its definition
because we must allow the type of the value `V` to be a subtype of `A`.
```
data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {N A B C D}
    →  ∅ , A ⊢ N ⦂ B
    → A ⇒ B <: C ⇒ D
      -------------------------
    → Canonical (ƛ N) ⦂ (C ⇒ D)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ

  C-rcd : ∀{n m}{ls : Vec Name n}{ks : Vec Name m}{Ms As Bs}{dls}
    → ∅ ⊢* Ms ⦂ As
    → (dks : distinct ks)
    → ｛ ks ⦂ As ｝{dks}  <: ｛ ls ⦂ Bs ｝{dls}
    → Canonical ｛ ks := Ms ｝ ⦂ ｛ ls ⦂ Bs ｝ {dls}
```

Every closed, well-typed value is canonical:
```
canonical : ∀ {V A}
  → ∅ ⊢ V ⦂ A
  → Value V
    -----------
  → Canonical V ⦂ A
canonical (⊢` ())          ()
canonical (⊢ƛ ⊢N)          V-ƛ         =  C-ƛ ⊢N <:-refl
canonical (⊢· ⊢L ⊢M)       ()
canonical ⊢zero            V-zero      =  C-zero
canonical (⊢suc ⊢V)        (V-suc VV)  =  C-suc (canonical ⊢V VV)
canonical (⊢case ⊢L ⊢M ⊢N) ()
canonical (⊢μ ⊢M)          ()
canonical (⊢rcd ⊢Ms d) VV = C-rcd {dls = d} ⊢Ms d <:-refl
canonical (⊢<: ⊢V <:-nat) VV = canonical ⊢V VV
canonical (⊢<: ⊢V (<:-fun {A}{B}{C}{D} C<:A B<:D)) VV
    with canonical ⊢V VV
... | C-ƛ {N}{A′}{B′}{A}{B} ⊢N  AB′<:AB = C-ƛ ⊢N (<:-trans AB′<:AB (<:-fun C<:A B<:D))
canonical (⊢<: ⊢V (<:-rcd {ks = ks}{ls = ls}{d2 = dls} ls⊆ks ls⦂Ss<:ks⦂Ts)) VV
    with canonical ⊢V VV
... | C-rcd {ks = ks′} ⊢Ms dks′ As<:Ss =
      C-rcd {dls = distinct-relevant dls} ⊢Ms dks′ (<:-trans As<:Ss (<:-rcd ls⊆ks ls⦂Ss<:ks⦂Ts))
```
The case for subsumption (`⊢<:`) is interesting. We proceed by
cases on the derivation of subtyping.

* If the last rule is `<:-nat`, then we have `∅ ⊢ V ⦂ ℕ`
  and the induction hypothesis gives us `Canonical V ⦂ ℕ`.

* If the last rule is `<:-fun`, then we have `A ⇒ B <: C ⇒ D`
  and `∅ ⊢ ƛ N ⦂ A ⇒ B`. By the induction hypothesis,
  we have `∅ , A′ ⊢ N ⦂ B′` and `A′ ⇒ B′ <: A ⇒ B` for some `A′` and `B′`.
  We conclude that `Canonical (ƛ N) ⦂ C ⇒ D` by rule `C-ƛ` and the transitivity of subtyping.

* If the last rule is `<:-rcd`, then we have `｛ ls ⦂ Ss ｝ <: ｛ ks ⦂ Ts ｝`
  and `∅ ⊢ ｛ ks′ := Ms ｝ ⦂ ｛ ks ⦂ Ss ｝`. By the induction hypothesis,
  we have `∅ ⊢* Ms ⦂ As`, `distinct ks′`, and `｛ ks′ ⦂ As ｝ <: ｛ ks ⦂ Ss ｝`.
  We conclude that `Canonical ｛ ks′ := Ms ｝ ⦂ ｛ ks ⦂ Ts ｝`
  by rule `C-rcd` and the transitivity of subtyping.


If a term is canonical, then it is also a value.
```
value : ∀ {M A}
  → Canonical M ⦂ A
    ----------------
  → Value M
value (C-ƛ _ _)     = V-ƛ
value C-zero        = V-zero
value (C-suc CM)    = V-suc (value CM)
value (C-rcd _ _ _) = V-rcd
```

A canonical value is a well-typed value.
```
typed : ∀ {V A}
  → Canonical V ⦂ A
    ---------------
  → ∅ ⊢ V ⦂ A
typed (C-ƛ ⊢N AB<:CD) = ⊢<: (⊢ƛ ⊢N) AB<:CD
typed C-zero = ⊢zero
typed (C-suc c) = ⊢suc (typed c)
typed (C-rcd ⊢Ms dks As<:Bs) = ⊢<: (⊢rcd ⊢Ms dks) As<:Bs
```

## Progress {#subtyping-progress}

The Progress theorem states that a well-typed term may either take a
reduction step or it is already a value. The proof of Progress is like
the one in the [Properties](/Properties/); it
proceeds by induction on the typing derivation and most of the cases
remain the same. Below we discuss the new cases for records and
subsumption.

```
data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
```

```
progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N)                            = done V-ƛ
progress (⊢· ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                            = step (ξ-·₁ L—→L′)
... | done VL
        with progress ⊢M
...     | step M—→M′                        = step (ξ-·₂ VL M—→M′)
...     | done VM
        with canonical ⊢L VL
...     | C-ƛ ⊢N _                          = step (β-ƛ VM)
progress ⊢zero                              =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M—→M′                           =  step (ξ-suc M—→M′)
...  | done VM                              =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            =  step (ξ-case L—→L′)
... | done VL with canonical ⊢L VL
...   | C-zero                              =  step β-zero
...   | C-suc CL                            =  step (β-suc (value CL))
progress (⊢μ ⊢M)                            =  step β-μ
progress (⊢# {n}{Γ}{A}{M}{l}{ls}{As}{i}{d} ⊢M ls[i]=l As[i]=A)
    with progress ⊢M
... | step M—→M′                            =  step (ξ-# M—→M′)
... | done VM
    with canonical ⊢M VM
... | C-rcd {ks = ms}{As = Bs} ⊢Ms _ (<:-rcd ls⊆ms _)
    with lookup-⊆ {i = i} ls⊆ms
... | ⟨ k , ls[i]=ms[k] ⟩                   =  step (β-# {j = k}(trans (sym ls[i]=ms[k]) ls[i]=l))
progress (⊢rcd x d)                         =  done V-rcd
progress (⊢<: {A = A}{B} ⊢M A<:B)           =  progress ⊢M
```
* Case `⊢#`: We have `Γ ⊢ M ⦂ ｛ ls ⦂ As ｝`, `lookup ls i ≡ l`, and `lookup As i ≡ A`.
  By the induction hypothesis, either `M —→ M′` or `M` is a value. In the later case we
  conclude that `M # l —→ M′ # l` by rule `ξ-#`. On the other hand, if `M` is a value,
  we invoke the canonical forms lemma to show that `M` has the form `｛ ms := Ms ｝`
  where `∅ ⊢* Ms ⦂ Bs` and `ls ⊆ ms`. By lemma `lookup-⊆`, we have
  `lookup ls i ≡ lookup ms k` for some `k`. Thus, we have `lookup ms k ≡ l`
  and we conclude `｛ ms := Ms ｝ # l —→ lookup Ms k` by rule `β-#`.

* Case `⊢rcd`: we immediately characterize the record as a value.

* Case `⊢<:`: we invoke the induction hypothesis on sub-derivation of `Γ ⊢ M ⦂ A`.


## Preservation {#subtyping-preservation}

In this section we prove that when a well-typed term takes a reduction
step, the result is another well-typed term with the same type.

As mentioned earlier, we need to prove that substitution preserve
types, which in turn requires that renaming preserves types.  The
proofs of these lemmas are adapted from the intrinsic versions of the
`ext`, `rename`, `exts`, and `subst` functions in the
[DeBruijn](/DeBruijn/) chapter.

We define the following abbreviation for a *well-typed renaming* from Γ
to Δ, that is, a renaming that sends variables in Γ to variables in Δ
with the same type.
```
_⦂ᵣ_⇒_ : (Id → Id) → Context → Context → Set
ρ ⦂ᵣ Γ ⇒ Δ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ ρ x ⦂ A
```

The `ext` function takes a well-typed renaming from Γ to Δ
and extends it to become a renaming from (Γ , B) to (Δ , B).
```
ext-pres : ∀ {Γ Δ ρ B}
  → ρ ⦂ᵣ Γ ⇒ Δ
    --------------------------------
  → ext ρ ⦂ᵣ (Γ , B) ⇒ (Δ , B)
ext-pres {ρ = ρ } ρ⦂ Z = Z
ext-pres {ρ = ρ } ρ⦂ (S {x = x} ∋x) =  S (ρ⦂ ∋x)
```

Next we prove that both `rename` and `rename-vec` preserve types.  We
use the `ext-pres` lemma in each of the cases with a variable binding: `⊢ƛ`,
`⊢μ`, and `⊢case`.
```
ren-vec-pres : ∀ {Γ Δ ρ}{n}{Ms : Vec Term n}{As : Vec Type n}
  → ρ ⦂ᵣ Γ ⇒ Δ  →  Γ ⊢* Ms ⦂ As  →  Δ ⊢* rename-vec ρ Ms ⦂ As

rename-pres : ∀ {Γ Δ ρ M A}
  → ρ ⦂ᵣ Γ ⇒ Δ
  → Γ ⊢ M ⦂ A
    ------------------
  → Δ ⊢ rename ρ M ⦂ A
rename-pres ρ⦂ (⊢` ∋w)           =  ⊢` (ρ⦂ ∋w)
rename-pres {ρ = ρ} ρ⦂ (⊢ƛ ⊢N)   =  ⊢ƛ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ρ⦂) ⊢N)
rename-pres {ρ = ρ} ρ⦂ (⊢· ⊢L ⊢M)=  ⊢· (rename-pres {ρ = ρ} ρ⦂ ⊢L) (rename-pres {ρ = ρ} ρ⦂ ⊢M)
rename-pres {ρ = ρ} ρ⦂ (⊢μ ⊢M)   =  ⊢μ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ρ⦂) ⊢M)
rename-pres ρ⦂ (⊢rcd ⊢Ms dls)    = ⊢rcd (ren-vec-pres ρ⦂ ⊢Ms ) dls
rename-pres {ρ = ρ} ρ⦂ (⊢# {d = d} ⊢M lif liA) = ⊢# {d = d}(rename-pres {ρ = ρ} ρ⦂ ⊢M) lif liA
rename-pres {ρ = ρ} ρ⦂ (⊢<: ⊢M lt) = ⊢<: (rename-pres {ρ = ρ} ρ⦂ ⊢M) lt
rename-pres ρ⦂ ⊢zero               = ⊢zero
rename-pres ρ⦂ (⊢suc ⊢M)           = ⊢suc (rename-pres ρ⦂ ⊢M)
rename-pres ρ⦂ (⊢case ⊢L ⊢M ⊢N)    =
    ⊢case (rename-pres ρ⦂ ⊢L) (rename-pres ρ⦂ ⊢M) (rename-pres (ext-pres ρ⦂) ⊢N)

ren-vec-pres ρ⦂ ⊢*-[] = ⊢*-[]
ren-vec-pres {ρ = ρ} ρ⦂ (⊢*-∷ ⊢M ⊢Ms) =
  let IH = ren-vec-pres {ρ = ρ} ρ⦂ ⊢Ms in
  ⊢*-∷ (rename-pres {ρ = ρ} ρ⦂ ⊢M) IH
```

A *well-typed substitution* from Γ to Δ sends variables in Γ to terms
of the same type in the context Δ.
```
_⦂_⇒_ : (Id → Term) → Context → Context → Set
σ ⦂ Γ ⇒ Δ = ∀ {A x} → Γ ∋ x ⦂ A → Δ ⊢ subst σ (` x) ⦂ A
```

The `exts` function sends well-typed substitutions from Γ to Δ to
well-typed substitutions from (Γ , B) to (Δ , B). In the case for `S`,
we note that `exts σ (suc x) ≡ rename sub (σ x)`, so we need to prove
`Δ , B ⊢ rename suc (σ x) ⦂ A`, which we obtain by the `rename-pres`
lemma.

```
exts-pres : ∀ {Γ Δ σ B}
  → σ ⦂ Γ ⇒ Δ
    --------------------------------
  → exts σ ⦂ (Γ , B) ⇒ (Δ , B)
exts-pres {σ = σ} σ⦂ Z = ⊢` Z
exts-pres {σ = σ} σ⦂ (S {x = x} ∋x) = rename-pres {ρ = suc} S (σ⦂ ∋x)
```

Now we prove that both `subst` and `subst-vec` preserve types.  We use
the `exts-pres` lemma in each of the cases with a variable binding:
`⊢ƛ`, `⊢μ`, and `⊢case`.
```
subst-vec-pres : ∀ {Γ Δ σ}{n}{Ms : Vec Term n}{A}
  → σ ⦂ Γ ⇒ Δ  →  Γ ⊢* Ms ⦂ A  →  Δ ⊢* subst-vec σ Ms ⦂ A

subst-pres : ∀ {Γ Δ σ N A}
  → σ ⦂ Γ ⇒ Δ
  → Γ ⊢ N ⦂ A
    -----------------
  → Δ ⊢ subst σ N ⦂ A
subst-pres σ⦂ (⊢` eq)            = σ⦂ eq
subst-pres {σ = σ} σ⦂ (⊢ƛ ⊢N)    = ⊢ƛ (subst-pres{σ = exts σ}(exts-pres {σ = σ} σ⦂) ⊢N)
subst-pres {σ = σ} σ⦂ (⊢· ⊢L ⊢M) = ⊢· (subst-pres{σ = σ} σ⦂ ⊢L) (subst-pres{σ = σ} σ⦂ ⊢M)
subst-pres {σ = σ} σ⦂ (⊢μ ⊢M)    = ⊢μ (subst-pres{σ = exts σ} (exts-pres{σ = σ} σ⦂) ⊢M)
subst-pres σ⦂ (⊢rcd ⊢Ms dls) = ⊢rcd (subst-vec-pres σ⦂ ⊢Ms ) dls
subst-pres {σ = σ} σ⦂ (⊢# {d = d} ⊢M lif liA) =
    ⊢# {d = d} (subst-pres {σ = σ} σ⦂ ⊢M) lif liA
subst-pres {σ = σ} σ⦂ (⊢<: ⊢N lt) = ⊢<: (subst-pres {σ = σ} σ⦂ ⊢N) lt
subst-pres σ⦂ ⊢zero = ⊢zero
subst-pres σ⦂ (⊢suc ⊢M) = ⊢suc (subst-pres σ⦂ ⊢M)
subst-pres σ⦂ (⊢case ⊢L ⊢M ⊢N) =
    ⊢case (subst-pres σ⦂ ⊢L) (subst-pres σ⦂ ⊢M) (subst-pres (exts-pres σ⦂) ⊢N)

subst-vec-pres σ⦂ ⊢*-[] = ⊢*-[]
subst-vec-pres {σ = σ} σ⦂ (⊢*-∷ ⊢M ⊢Ms) =
    ⊢*-∷ (subst-pres {σ = σ} σ⦂ ⊢M) (subst-vec-pres σ⦂ ⊢Ms)
```

The fact that single substitution preserves types is a corollary
of `subst-pres`.
```
substitution : ∀{Γ A B M N}
   → Γ ⊢ M ⦂ A
   → (Γ , A) ⊢ N ⦂ B
     ---------------
   → Γ ⊢ N [ M ] ⦂ B
substitution {Γ}{A}{B}{M}{N} ⊢M ⊢N = subst-pres {σ = subst-zero M} G ⊢N
    where
    G : ∀ {C : Type} {x : ℕ}
      → (Γ , A) ∋ x ⦂ C → Γ ⊢ subst (subst-zero M) (` x) ⦂ C
    G {C} {zero} Z = ⊢M
    G {C} {suc x} (S ∋x) = ⊢` ∋x
```

We require just one last lemma before we get to the proof of preservation.
The following lemma establishes that field access preserves types.
```
field-pres : ∀{n}{As : Vec Type n}{A}{Ms : Vec Term n}{i : Fin n}
         → ∅ ⊢* Ms ⦂ As
         → lookup As i ≡ A
         → ∅ ⊢ lookup Ms i ⦂ A
field-pres {i = zero} (⊢*-∷ ⊢M ⊢Ms) refl = ⊢M
field-pres {i = suc i} (⊢*-∷ ⊢M ⊢Ms) As[i]=A = field-pres ⊢Ms As[i]=A
```
The proof is by induction on the typing derivation.

* Case `⊢-*-[]`: This case yields a contradiction because `Fin 0` is uninhabitable.

* Case `⊢-*-∷`: So we have `∅ ⊢ M ⦂ B` and `∅ ⊢* Ms ⦂ As`. We proceed by cases on `i`.

    * If it is `0`, then lookup yields term `M` and `A ≡ B`, so we conclude that `∅ ⊢ M ⦂ A`.

    * If it is `suc i`, then we conclude by the induction hypothesis.


We conclude this chapter with the proof of preservation. We discuss
the cases particular to records and subtyping in the paragraph
following the Agda proof.
```
preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢` ())
preserve (⊢ƛ ⊢N)                 ()
preserve (⊢· ⊢L ⊢M)              (ξ-·₁ L—→L′)     =  ⊢· (preserve ⊢L L—→L′) ⊢M
preserve (⊢· ⊢L ⊢M)              (ξ-·₂ VL M—→M′)  =  ⊢· ⊢L (preserve ⊢M M—→M′)
preserve (⊢· ⊢L ⊢M)              (β-ƛ VL)
    with canonical ⊢L V-ƛ
... | C-ƛ ⊢N (<:-fun CA BC)                       =  ⊢<: (substitution (⊢<: ⊢M CA) ⊢N) BC
preserve ⊢zero                   ()
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢L ⊢M ⊢N)        (β-zero)         =  ⊢M
preserve (⊢case ⊢L ⊢M ⊢N)        (β-suc VV)
    with canonical ⊢L (V-suc VV)
... | C-suc CV                                    =  substitution (typed CV) ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  substitution (⊢μ ⊢M) ⊢M
preserve (⊢# {d = d} ⊢M lsi Asi) (ξ-# M—→M′)      =  ⊢# {d = d} (preserve ⊢M M—→M′) lsi Asi
preserve (⊢# {ls = ls}{i = i} ⊢M refl refl) (β-# {ls = ks}{Ms}{j = j} ks[j]=l)
    with canonical ⊢M V-rcd
... | C-rcd {As = Bs} ⊢Ms dks (<:-rcd {ks = ks} ls⊆ks Bs<:As)
    with lookup-⊆ {i = i} ls⊆ks
... | ⟨ k , ls[i]=ks[k] ⟩
    with field-pres {i = k} ⊢Ms refl
... | ⊢Ms[k]⦂Bs[k]
    rewrite distinct-lookup-inj dks (trans ks[j]=l ls[i]=ks[k]) =
    let Ms[k]⦂As[i] = ⊢<: ⊢Ms[k]⦂Bs[k] (Bs<:As (sym ls[i]=ks[k])) in
    Ms[k]⦂As[i]
preserve (⊢<: ⊢M B<:A) M—→N                       =  ⊢<: (preserve ⊢M M—→N) B<:A
```
Recall that the proof is by induction on the derivation of `∅ ⊢ M ⦂ A`
with cases on `M —→ N`.

* Case `⊢#` and `ξ-#`: So `∅ ⊢ M ⦂ ｛ ls ⦂ As ｝`, `lookup ls i ≡ l`, `lookup As i ≡ A`,
  and `M —→ M′`. We apply the induction hypothesis to obtain `∅ ⊢ M′ ⦂ ｛ ls ⦂ As ｝`
  and then conclude by rule `⊢#`.

* Case `⊢#` and `β-#`. We have `∅ ⊢ ｛ ks := Ms ｝ ⦂ ｛ ls ⦂ As ｝`, `lookup ls i ≡ l`,
  `lookup As i ≡ A`, `lookup ks j ≡ l`, and `｛ ks := Ms ｝ # l —→ lookup Ms j`.
  By the canonical forms lemma, we have `∅ ⊢* Ms ⦂ Bs`, `ls ⊆ ks` and `ks ⦂ Bs <: ls ⦂ As`.
  By lemma `lookup-⊆` we have `lookup ls i ≡ lookup ks k` for some `k`.
  Also, we have `∅ ⊢ lookup Ms k ⦂ lookup Bs k` by lemma `field-pres`.
  Then because `ks ⦂ Bs <: ls ⦂ As` and `lookup ks k ≡ lookup ls i`, we have
  `lookup Bs k <: lookup As i`. So by rule `⊢<:` we have
  `∅ ⊢ lookup Ms k ⦂ lookup As i`.
  Finally, because `lookup` is injective and `lookup ks j ≡ lookup ks k`,
  we have `j ≡ k` and conclude that `∅ ⊢ lookup Ms j ⦂ lookup As i`.

* Case `⊢<:`. We have `∅ ⊢ M ⦂ B`, `B <: A`, and `M —→ N`. We apply the induction hypothesis
  to obtain `∅ ⊢ N ⦂ B` and then subsumption to conclude that `∅ ⊢ N ⦂ A`.


#### Exercise `intrinsic-records` (stretch)

Formulate the language of this chapter, STLC with records, using
intrinsically typed terms. This requires taking an algorithmic approach
to the type system, which means that there is no subsumption rule and
instead subtyping is used in the elimination rules. For example,
the rule for function application would be:

    _·_ : ∀ {Γ A B C}
      → Γ ⊢ A ⇒ B
      → Γ ⊢ C
      → C <: A
        -------
      → Γ ⊢ B

#### Exercise `type-check-records` (practice)

Write a recursive function whose input is a `Term` and whose output
is a typing derivation for that term, if one exists.

    type-check : (M : Term) → (Γ : Context) → Maybe (Σ[ A ∈ Type ] Γ ⊢ M ⦂ A)

#### Exercise `variants` (recommended)

Add variants to the language of this chapter and update the proofs of
progress and preservation. The variant type is a generalization of a
sum type, similar to the way the record type is a generalization of
product. The following summarizes the treatment of variants in the
book Types and Programming Languages. A variant type is traditionally
written:

    〈l₁:A₁, ..., lᵤ:Aᵤ〉

The term for introducing a variant is

    〈l=t〉

and the term for eliminating a variant is

    case L of 〈l₁=x₁〉 ⇒ M₁ | ... | 〈lᵤ=xᵤ〉 ⇒ Mᵤ

The typing rules for these terms are

    (T-Variant)
    Γ ⊢ Mⱼ : Aⱼ
    ---------------------------------
    Γ ⊢ 〈lⱼ=Mⱼ〉 : 〈l₁=A₁, ... , lᵤ=Aᵤ〉


    (T-Case)
    Γ ⊢ L : 〈l₁=A₁, ... , lᵤ=Aᵤ〉
    ∀ i ∈ 1..u,   Γ,xᵢ:Aᵢ ⊢ Mᵢ : B
    ---------------------------------------------------
    Γ ⊢ case L of 〈l₁=x₁〉 ⇒ M₁ | ... | 〈lᵤ=xᵤ〉 ⇒ Mᵤ  : B

The non-algorithmic subtyping rules for variants are

    (S-VariantWidth)
    ------------------------------------------------------------
    〈l₁=A₁, ..., lᵤ=Aᵤ〉   <:   〈l₁=A₁, ..., lᵤ=Aᵤ, ..., lᵤ₊ₓ=Aᵤ₊ₓ〉

    (S-VariantDepth)
    ∀ i ∈ 1..u,    Aᵢ <: Bᵢ
    ---------------------------------------------
    〈l₁=A₁, ..., lᵤ=Aᵤ〉   <:   〈l₁=B₁, ..., lᵤ=Bᵤ〉

    (S-VariantPerm)
    ∀i∈1..u, ∃j∈1..u, kⱼ = lᵢ and Aⱼ = Bᵢ
    ----------------------------------------------
    〈k₁=A₁, ..., kᵤ=Aᵤ〉   <:   〈l₁=B₁, ..., lᵤ=Bᵤ〉

Come up with an algorithmic subtyping rule for variant types.

#### Exercise `<:-alternative` (stretch)

Revise this formalisation of records with subtyping (including proofs
of progress and preservation) to use the non-algorithmic subtyping
rules for Chapter 15 of Types and Programming Languages, which we list here:

    (S-RcdWidth)
    --------------------------------------------------------------
    { l₁:A₁, ..., lᵤ:Aᵤ, ..., lᵤ₊ₓ:Aᵤ₊ₓ } <: { l₁:A₁, ..., lᵤ:Aᵤ }

    (S-RcdDepth)
        ∀i∈1..u, Aᵢ <: Bᵢ
    ----------------------------------------------
    { l₁:A₁, ..., lᵤ:Aᵤ } <: { l₁:B₁, ..., lᵤ:Bᵤ }

    (S-RcdPerm)
    ∀i∈1..u, ∃j∈1..u, kⱼ = lᵢ and Aⱼ = Bᵢ
    ----------------------------------------------
    { k₁:A₁, ..., kᵤ:Aᵤ } <: { l₁:B₁, ..., lᵤ:Bᵤ }

You will most likely need to prove inversion lemmas for the subtype relation
of the form:

    If S <: T₁ ⇒ T₂, then S ≡ S₁ ⇒ S₂, T₁ <: S₁, and S₂ <: T₂, for some S₁, S₂.

    If S <: { lᵢ : Tᵢ | i ∈ 1..n }, then S ≡ { kⱼ : Sⱼ | j ∈ 1..m }
    and { lᵢ | i ∈ 1..n } ⊆ { kⱼ | j ∈ 1..m }
    and Sⱼ <: Tᵢ for every i and j such that lᵢ = kⱼ.

## References

* John C. Reynolds. Using Category Theory to Design Implicit
  Conversions and Generic Operators.
  In Semantics-Directed Compiler Generation, 1980.
  LNCS Volume 94.

* Luca Cardelli. A semantics of multiple inheritance.  In Semantics of
  Data Types, 1984. Springer.

* Barbara H. Liskov and Jeannette M. Wing.  A Behavioral Notion of
  Subtyping. In ACM Trans. Program. Lang. Syst.  Volume 16, 1994.

* Types and Programming Languages. Benjamin C. Pierce. The MIT Press. 2002.
