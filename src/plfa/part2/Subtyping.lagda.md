---
title     : "Subtyping: records"
layout    : page
prev      : /More/
permalink : /Subtyping/
next      : /Bisimulation/
---

```
module plfa.part2.Subtyping where
```

## Imports

```
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_; _+_)
open import Data.Nat.Properties using (m+n≤o⇒m≤o; m+n≤o⇒n≤o; n≤0⇒n≡0; ≤-pred; ≤-refl)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Data.Vec.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.Vec.Membership.Propositional.Properties using (∈-lookup)
open import Data.Vec.Relation.Unary.Any using (here; there)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)
```

## Syntax

```
infix  4 _⊢_⦂_
infix  4 _∋_⦂_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infixl 7 _#_
```


## Record Field Names, Functions and Properties

We represent field identifiers (aka. names) as strings.

```
Name : Set
Name = String
```

The field identifiers of a record will be stored in a sequence,
specifically Agda's `Vec` type.  We require that the field names of a
record be distinct, which we define as follows.

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
distinct-lookup-inj {.(suc _)} {x ∷ ls} {zero} {zero} ⟨ x∉ls , dls ⟩ lsij = refl
distinct-lookup-inj {.(suc _)} {x ∷ ls} {zero} {suc j} ⟨ x∉ls , dls ⟩ refl =
    ⊥-elim (x∉ls (∈-lookup j ls))
distinct-lookup-inj {.(suc _)} {x ∷ ls} {suc i} {zero} ⟨ x∉ls , dls ⟩ refl =
    ⊥-elim (x∉ls (∈-lookup i ls))
distinct-lookup-inj {.(suc _)} {x ∷ ls} {suc i} {suc j} ⟨ x∉ls , dls ⟩ lsij =
    cong suc (distinct-lookup-inj dls lsij)
```

We shall need to convert from an irrelevent proof of distinctness to a
relevant one. In general, this can be accomplished for any decidable
predicate. The following is a decision procedure for whether a vector
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
... | no ¬dxs = no λ x₁ → ¬dxs (proj₂ x₁)
```

With the decision procedure in hand, we can launder an irrelevant
proof into a relevant one.

```
distinct-relevant : ∀ {n}{fs : Vec Name n} .(d : distinct fs) → distinct fs
distinct-relevant {n}{fs} d
    with distinct? fs
... | yes dfs = dfs
... | no ¬dfs = ⊥-elimi (¬dfs d)
```

The fields of one record are a subset of the fields of another record
if every field of the first is also a field of the second.

```
_⊆_ : ∀{n m} → Vec Name n → Vec Name m → Set
xs ⊆ ys = (x : Name) → x ∈ xs → x ∈ ys
```

This subset relation is reflexive.

```
⊆-refl : ∀{n}{ls : Vec Name n} → ls ⊆ ls
⊆-refl {n}{ls} = λ x x∈ls → x∈ls
```

It is also transitive.

```
⊆-trans : ∀{l n m}{ns  : Vec Name n}{ms  : Vec Name m}{ls  : Vec Name l}
        → ns ⊆ ms   →    ms ⊆ ls
        → ns ⊆ ls
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
infix 5 ｛_⦂_｝

data Type : Set where
  _⇒_   : Type → Type → Type
  `ℕ    : Type
  ｛_⦂_｝ : {n : ℕ} (ls : Vec Name n) (As : Vec Type n) → .{d : distinct ls} → Type 
```

We do not want the details of the proof of distinctness to affect
whether two record types are equal, so we declare that parameter to be
irrelevant by placing a `.` in front of it.


## Subtyping

```
infix 5 _<:_

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

The first premise of the record subtyping rule (`<:-rcd`) expresses
_width subtyping_ by requiring that all the labels in `ls` are also in
`ks`. So it allows the hiding of fields when going from a subtype to a
supertype.

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

The proof that subtyping is reflexive does not go by induction on the
type because of the `<:-rcd` rule. We instead use induction on the
size of the type. So we first define size of a type, and the size of a
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

If a vector of types has a size smaller than `n`, then so is any type
in the vector.

```
lookup-vec-ty-size : ∀{n}{k} {As : Vec Type k} {j}
   → vec-ty-size As ≤ n
   → ty-size (lookup As j) ≤ n
lookup-vec-ty-size {n} {suc k} {A ∷ As} {zero} As≤n = m+n≤o⇒m≤o (ty-size A) As≤n
lookup-vec-ty-size {n} {suc k} {A ∷ As} {suc j} As≤n =
    lookup-vec-ty-size {n} {k} {As} (m+n≤o⇒n≤o (ty-size A) As≤n)
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
  let a = ≤-pred m in
  <:-fun (<:-refl-aux{n}{A}{m+n≤o⇒m≤o (ty-size A) a })
         (<:-refl-aux{n}{B}{m+n≤o⇒n≤o (ty-size A) a})
<:-refl-aux {suc n}{｛ fs ⦂ As ｝ {d} }{m} = <:-rcd {d1 = d}{d2 = d} ⊆-refl G
    where
    G : fs ⦂ As <: fs ⦂ As
    G {i}{j} lij rewrite distinct-lookup-inj (distinct-relevant d) lij =
        let As[i]≤n = lookup-vec-ty-size {As = As}{i} (≤-pred m) in 
        <:-refl-aux {n}{lookup As i}{As[i]≤n}
```

```
<:-refl : ∀{A} → A <: A
<:-refl {A} = <:-refl-aux {ty-size A}{A}{≤-refl}
```

## Subtyping is transitive

The proof of transitivity is straightforward, given that we've
already proved the two lemmas needed in the case for `<:-rcd`:
`⊆-trans` and `lookup-⊆`.

```
<:-trans : ∀{A B C}
    → A <: B   →   B <: C
      -------------------
    → A <: C
<:-trans {A₁ ⇒ A₂} {B₁ ⇒ B₂} {C₁ ⇒ C₂} (<:-fun A<:B A<:B₁) (<:-fun B<:C B<:C₁) =
    <:-fun (<:-trans B<:C A<:B) (<:-trans A<:B₁ B<:C₁)
<:-trans {.`ℕ} {`ℕ} {.`ℕ} <:-nat <:-nat = <:-nat
<:-trans {｛ ls ⦂ As ｝{d1} } {｛ ms ⦂ Bs ｝ {d2} } {｛ ns ⦂ Cs ｝ {d3} }
    (<:-rcd ms⊆ls As<:Bs) (<:-rcd ns⊆ms Bs<:Cs) =
    <:-rcd (⊆-trans ns⊆ms ms⊆ls) G
    where
    G : ls ⦂ As <: ns ⦂ Cs
    G {i}{j} lij
        with lookup-⊆ {i = i} ns⊆ms 
    ... | ⟨ k , lik ⟩
        with lookup-⊆ {i = k} ms⊆ls
    ... | ⟨ j' , lkj' ⟩ rewrite sym lkj' | lij | sym lik  =
        let ab = As<:Bs {k}{j} (trans lij lik) in
        let bc = Bs<:Cs {i}{k} (sym lik) in
        <:-trans ab bc
```

## Contexts

```
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

## Variables and the lookup judgment

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



## Terms and the typing judgment

```
Id : Set
Id = ℕ

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


## Renaming and Substitution

```
ext : (Id → Id) → (Id → Id)
ext ρ 0      =  0
ext ρ (suc x)  =  suc (ρ x)
```

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

```
exts : (Id → Term) → (Id → Term)
exts σ 0      =  ` 0
exts σ (suc x)  =  rename suc (σ x)
```

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

```
subst-zero : Term → Id → Term
subst-zero M 0       =  M
subst-zero M (suc x) =  ` x

_[_] : Term → Term → Term
_[_] N M =  subst (subst-zero M) N
```

## Values

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

```
infix 2 _—→_

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

  β-# : ∀ {n}{ls : Vec Name n}{vs : Vec Term n} {lⱼ}{j : Fin n}
    → lookup ls j ≡ lⱼ
      ---------------------------------
    → ｛ ls := vs ｝ # lⱼ —→  lookup vs j


```

## Canonical Forms

```
infix  4 Canonical_⦂_

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
canonical (⊢<: ⊢M <:-nat) VV = canonical ⊢M VV
canonical (⊢<: ⊢M (<:-fun A<:B A<:B₁)) VV 
    with canonical ⊢M VV 
... | C-ƛ ⊢N  AB<:CD = C-ƛ ⊢N (<:-trans AB<:CD (<:-fun A<:B A<:B₁))
canonical (⊢<: ⊢M (<:-rcd {d2 = dls} ls⊆ks ls⦂Ss<:ks⦂Ts)) VV
    with canonical ⊢M VV
... | C-rcd {dls = d} ⊢Ms dks As<:Ss =
      C-rcd {dls = distinct-relevant dls} ⊢Ms dks (<:-trans As<:Ss (<:-rcd ls⊆ks ls⦂Ss<:ks⦂Ts))
```

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

```
typed : ∀ {M A}
  → Canonical M ⦂ A
    ---------------
  → ∅ ⊢ M ⦂ A
typed (C-ƛ ⊢N AB<:CD) = ⊢<: (⊢ƛ ⊢N) AB<:CD
typed C-zero = ⊢zero
typed (C-suc c) = ⊢suc (typed c)
typed (C-rcd ⊢Ms dks As<:Bs) = ⊢<: (⊢rcd ⊢Ms dks) As<:Bs
```

## Progress

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
progress (⊢μ ⊢M)                          = step β-μ
progress (⊢# {Γ}{A}{M}{n}{fs}{As}{d}{i}{f} ⊢R lif liA)
    with progress ⊢R
... | step R—→R′                          = step (ξ-# R—→R′)
... | done VR
    with canonical ⊢R VR
... | C-rcd ⊢Ms dks (<:-rcd fs⊆fs' _)
    with lookup-⊆ {i = i} fs⊆fs'
... | ⟨ k , eq ⟩ rewrite eq = step (β-# {j = k} lif)
progress (⊢rcd x d)                       = done V-rcd
progress (⊢<: {A = A}{B} ⊢M A<:B)         = progress ⊢M
```


## Preservation


```
_⦂ᵣ_⇒_ : (Id → Id) → Context → Context → Set
ρ ⦂ᵣ Γ ⇒ Δ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ ρ x ⦂ A
```

```
ext-pres : ∀ {Γ Δ ρ B}
  → ρ ⦂ᵣ Γ ⇒ Δ
    --------------------------------
  → ext ρ ⦂ᵣ (Γ , B) ⇒ (Δ , B)
ext-pres {ρ = ρ } ρ⦂ Z = Z
ext-pres {ρ = ρ } ρ⦂ (S {x = x} ∋x) =  S (ρ⦂ ∋x)
```

```
ren-vec-pres : ∀ {Γ Δ ρ}{n}{Ms : Vec Term n}{As : Vec Type n}
  → ρ ⦂ᵣ Γ ⇒ Δ
  → Γ ⊢* Ms ⦂ As
    ---------------------
  → Δ ⊢* rename-vec ρ Ms ⦂ As

rename-pres : ∀ {Γ Δ ρ M A}
  → ρ ⦂ᵣ Γ ⇒ Δ
  → Γ ⊢ M ⦂ A
    ------------------
  → Δ ⊢ rename ρ M ⦂ A
rename-pres ρ⦂ (⊢` ∋w)           =  ⊢` (ρ⦂ ∋w)
rename-pres {ρ = ρ} ρ⦂ (⊢ƛ ⊢N)   =  ⊢ƛ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ρ⦂) ⊢N)
rename-pres {ρ = ρ} ρ⦂ (⊢· ⊢L ⊢M)=  ⊢· (rename-pres {ρ = ρ} ρ⦂ ⊢L) (rename-pres {ρ = ρ} ρ⦂ ⊢M)
rename-pres {ρ = ρ} ρ⦂ (⊢μ ⊢M)   =  ⊢μ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ρ⦂) ⊢M)
rename-pres ρ⦂ (⊢rcd ⊢Ms dfs)    = ⊢rcd (ren-vec-pres ρ⦂ ⊢Ms ) dfs
rename-pres {ρ = ρ} ρ⦂ (⊢# {d = d} ⊢R lif liA) = ⊢# {d = d}(rename-pres {ρ = ρ} ρ⦂ ⊢R) lif liA
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

```
_⦂_⇒_ : (Id → Term) → Context → Context → Set
σ ⦂ Γ ⇒ Δ = ∀ {A x} → Γ ∋ x ⦂ A → Δ ⊢ subst σ (` x) ⦂ A
```

```
exts-pres : ∀ {Γ Δ σ B}
  → σ ⦂ Γ ⇒ Δ
    --------------------------------
  → exts σ ⦂ (Γ , B) ⇒ (Δ , B)
exts-pres {σ = σ} σ⦂ Z = ⊢` Z
exts-pres {σ = σ} σ⦂ (S {x = x} ∋x) = rename-pres {ρ = suc} S (σ⦂ ∋x)
```


```
subst-vec-pres : ∀ {Γ Δ σ}{n}{Ms : Vec Term n}{A}
  → σ ⦂ Γ ⇒ Δ
  → Γ ⊢* Ms ⦂ A
    -----------------
  → Δ ⊢* subst-vec σ Ms ⦂ A

subst-pres : ∀ {Γ Δ σ N A}
  → σ ⦂ Γ ⇒ Δ
  → Γ ⊢ N ⦂ A
    -----------------
  → Δ ⊢ subst σ N ⦂ A
subst-pres σ⦂ (⊢` eq)            = σ⦂ eq
subst-pres {σ = σ} σ⦂ (⊢ƛ ⊢N)    = ⊢ƛ (subst-pres{σ = exts σ}(exts-pres {σ = σ} σ⦂) ⊢N) 
subst-pres {σ = σ} σ⦂ (⊢· ⊢L ⊢M) = ⊢· (subst-pres{σ = σ} σ⦂ ⊢L) (subst-pres{σ = σ} σ⦂ ⊢M) 
subst-pres {σ = σ} σ⦂ (⊢μ ⊢M)    = ⊢μ (subst-pres{σ = exts σ} (exts-pres{σ = σ} σ⦂) ⊢M) 
subst-pres σ⦂ (⊢rcd ⊢Ms dfs) = ⊢rcd (subst-vec-pres σ⦂ ⊢Ms ) dfs
subst-pres {σ = σ} σ⦂ (⊢# {d = d} ⊢R lif liA) =
    ⊢# {d = d} (subst-pres {σ = σ} σ⦂ ⊢R) lif liA
subst-pres {σ = σ} σ⦂ (⊢<: ⊢N lt) = ⊢<: (subst-pres {σ = σ} σ⦂ ⊢N) lt
subst-pres σ⦂ ⊢zero = ⊢zero
subst-pres σ⦂ (⊢suc ⊢M) = ⊢suc (subst-pres σ⦂ ⊢M)
subst-pres σ⦂ (⊢case ⊢L ⊢M ⊢N) =
    ⊢case (subst-pres σ⦂ ⊢L) (subst-pres σ⦂ ⊢M) (subst-pres (exts-pres σ⦂) ⊢N)

subst-vec-pres σ⦂ ⊢*-[] = ⊢*-[]
subst-vec-pres {σ = σ} σ⦂ (⊢*-∷ ⊢M ⊢Ms) =
    ⊢*-∷ (subst-pres {σ = σ} σ⦂ ⊢M) (subst-vec-pres σ⦂ ⊢Ms)
```

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

```
field-pres : ∀{n}{As : Vec Type n}{A}{Ms : Vec Term n}{i : Fin n}
         → ∅ ⊢* Ms ⦂ As
         → lookup As i ≡ A
         → ∅ ⊢ lookup Ms i ⦂ A
field-pres {i = zero} (⊢*-∷ ⊢M ⊢Ms) refl = ⊢M
field-pres {i = suc i} (⊢*-∷ ⊢M ⊢Ms) As[i]=A = field-pres ⊢Ms As[i]=A

```

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
... | C-suc CV                                    = substitution (typed CV) ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  substitution (⊢μ ⊢M) ⊢M
preserve (⊢# {d = d} ⊢M lsi Asi) (ξ-# M—→M′)      = ⊢# {d = d} (preserve ⊢M M—→M′) lsi Asi
preserve (⊢# {ls = ls′}{i = i} ⊢M refl refl) (β-# {ls = ks}{Ms}{j = j} ks[j]=l)
    with canonical ⊢M V-rcd
... | C-rcd ⊢Ms dks (<:-rcd {ks = ks}{ls} ls⊆ks As<:Bs)
    with lookup-⊆ {i = i} ls⊆ks
... | ⟨ k , ls′[i]=ks[k] ⟩
    with field-pres {i = k} ⊢Ms refl
... | ⊢Ms[k]
    rewrite distinct-lookup-inj dks (trans ks[j]=l ls′[i]=ks[k]) =
    ⊢<: ⊢Ms[k] (As<:Bs (sym ls′[i]=ks[k]))
preserve (⊢<: ⊢M A<:B) M—→N                       =  ⊢<: (preserve ⊢M M—→N) A<:B
```
