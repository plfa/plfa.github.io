---
title     : "Substitution: Substitution in the untyped lambda calculus"
layout    : page
prev      : /ContextualEquivalence/
permalink : /Substitution/
next      : /Acknowledgements/
---


```
module plfa.part2.Substitution where
```

## Introduction

The primary purpose of this chapter is to prove that substitution
commutes with itself. Barendgredt (1984) refers to this
as the substitution lemma:

    M [x:=N] [y:=L] = M [y:=L] [x:= N[y:=L] ]

In our setting, with de Bruijn indices for variables, the statement of
the lemma becomes:

    M [ N ] [ L ] ≡  M〔 L 〕[ N [ L ] ]                     (substitution)

where the notation `M 〔 L 〕` is for substituting L for index 1 inside
M.  In addition, because we define substitution in terms of parallel
substitution, we have the following generalization, replacing the
substitution of L with an arbitrary parallel substitution σ.

    subst σ (M [ N ]) ≡ (subst (exts σ) M) [ subst σ N ]    (subst-commute)

The special case for renamings is also useful.

    rename ρ (M [ N ]) ≡ (rename (ext ρ) M) [ rename ρ N ]
                                                     (rename-subst-commute)

The secondary purpose of this chapter is to define the σ algebra of
parallel substitution due to Abadi, Cardelli, Curien, and Levy
(1991). The equations of this algebra not only help us prove the
substitution lemma, but they are generally useful. Furthermore, when
the equations are applied from left to right, they form a rewrite
system that _decides_ whether any two substitutions are equal.

## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Function using (_∘_)
open import plfa.part2.Untyped
     using (Type; Context; _⊢_; ★; _∋_; ∅; _,_; Z; S_; `_; ƛ_; _·_;
            rename; subst; ext; exts; _[_]; subst-zero)
```

```
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

## Notation

We introduce the following shorthand for the type of a _renaming_ from
variables in context `Γ` to variables in context `Δ`.

```
Rename : Context → Context → Set
Rename Γ Δ = ∀{A} → Γ ∋ A → Δ ∋ A
```

Similarly, we introduce the following shorthand for the type of a
_substitution_ from variables in context `Γ` to terms in context `Δ`.

```
Subst : Context → Context → Set
Subst Γ Δ = ∀{A} → Γ ∋ A → Δ ⊢ A
```

We use the following more succinct notation the `subst` function.

```
⟪_⟫ : ∀{Γ Δ A} → Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
⟪ σ ⟫ = λ M → subst σ M
```


## The σ algebra of substitution

Substitutions map de Bruijn indices (natural numbers) to terms, so we
can view a substitution simply as a sequence of terms, or more
precisely, as an infinite sequence of terms. The σ algebra consists of
four operations for building such sequences: identity `ids`, shift
`↑`, cons `M • σ`, and sequencing `σ ⨟ τ`.  The sequence `0, 1, 2, ...`
is constructed by the identity substitution.

```
ids : ∀{Γ} → Subst Γ Γ
ids x = ` x
```

The shift operation `↑` constructs the sequence

    1, 2, 3, ...

and is defined as follows.

```
↑ : ∀{Γ A} → Subst Γ (Γ , A)
↑ x = ` (S x)
```

Given a term `M` and substitution `σ`, the operation
`M • σ` constructs the sequence

    M , σ 0, σ 1, σ 2, ...

This operation is analogous to the `cons` operation of Lisp.

```
infixr 6 _•_

_•_ : ∀{Γ Δ A} → (Δ ⊢ A) → Subst Γ Δ → Subst (Γ , A) Δ
(M • σ) Z = M
(M • σ) (S x) = σ x
```

Given two substitutions `σ` and `τ`, the sequencing operation `σ ⨟ τ`
produces the sequence

    ⟪τ⟫(σ 0), ⟪τ⟫(σ 1), ⟪τ⟫(σ 2), ...

That is, it composes the two substitutions by first applying
`σ` and then applying `τ`.

```
infixr 5 _⨟_

_⨟_ : ∀{Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
σ ⨟ τ = ⟪ τ ⟫ ∘ σ
```

For the sequencing operation, Abadi et al. use the notation of
function composition, writing `σ ∘ τ`, but still with `σ` applied
before `τ`, which is the opposite of standard mathematical
practice. We instead write `σ ⨟ τ`, because semicolon is
the standard notation for forward function composition.

## The σ algebra equations

The σ algebra includes the following equations.

    (sub-head)  ⟪ M • σ ⟫ (` Z) ≡ M
    (sub-tail)  ↑ ⨟ (M • σ)    ≡ σ
    (sub-η)     (⟪ σ ⟫ (` Z)) • (↑ ⨟ σ) ≡ σ
    (Z-shift)   (` Z) • ↑      ≡ ids

    (sub-id)    ⟪ ids ⟫ M      ≡ M
    (sub-app)   ⟪ σ ⟫ (L · M)  ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
    (sub-abs)   ⟪ σ ⟫ (ƛ N)    ≡ ƛ ⟪ σ ⟫ N
    (sub-sub)   ⟪ τ ⟫ ⟪ σ ⟫ M  ≡ ⟪ σ ⨟ τ ⟫ M

    (sub-idL)   ids ⨟ σ        ≡ σ
    (sub-idR)   σ ⨟ ids        ≡ σ
    (sub-assoc) (σ ⨟ τ) ⨟ θ    ≡ σ ⨟ (τ ⨟ θ)
    (sub-dist)  (M • σ) ⨟ τ    ≡ (⟪ τ ⟫ M) • (σ ⨟ τ)

The first group of equations describe how the `•` operator acts like cons.
The equation `sub-head` says that the variable zero `Z` returns the
head of the sequence (it acts like the `car` of Lisp).  Similarly,
`sub-tail` says that sequencing with shift `↑` returns the tail of the
sequence (it acts like `cdr` of Lisp).  The `sub-η` equation is the
η-expansion rule for sequences, saying that taking the head and tail
of a sequence, and then cons'ing them together yields the original
sequence. The `Z-shift` equation says that cons'ing zero onto the
shifted sequence produces the identity sequence.

The next four equations involve applying substitutions to terms.  The
equation `sub-id` says that the identity substitution returns the term
unchanged. The equations `sub-app` and `sub-abs` says that
substitution is a congruence for the lambda calculus. The `sub-sub`
equation says that the sequence operator `⨟` behaves as intended.

The last four equations concern the sequencing of substitutions.
The first two equations, `sub-idL` and `sub-idR`, say that
`ids` is the left and right unit of the sequencing operator.
The `sub-assoc` equation says that sequencing is associative.
Finally, `sub-dist` says that post-sequencing distributes through cons.

## Relating the σ algebra and substitution functions

The definitions of substitution `N [ M ]` and parallel substitution
`subst σ N` depend on several auxiliary functions: `rename`, `exts`,
`ext`, and `subst-zero`. We shall relate those functions to terms in
the σ algebra.


To begin with, renaming can be expressed in terms of substitution.
We have

    rename ρ M ≡ ⟪ ren ρ ⟫ M               (rename-subst-ren)

where `ren` turns a renaming `ρ` into a substitution by post-composing
`ρ` with the identity substitution.

```
ren : ∀{Γ Δ} → Rename Γ Δ → Subst Γ Δ
ren ρ = ids ∘ ρ
```

When the renaming is the increment function, then it is equivalent to
shift.

    ren S_ ≡ ↑                             (ren-shift)

    rename S_ M ≡ ⟪ ↑ ⟫ M                  (rename-shift)

Renaming with the identity renaming leaves the term unchanged.

    rename (λ {A} x → x) M ≡ M             (rename-id)

Next we relate the `exts` function to the σ algebra.  Recall that the
`exts` function extends a substitution as follows:

    exts σ = ` Z, rename S_ (σ 0), rename S_ (σ 1), rename S_ (σ 2), ...

So `exts` is equivalent to cons'ing Z onto the sequence formed
by applying `σ` and then shifting.

    exts σ ≡ ` Z • (σ ⨟ ↑)                (exts-cons-shift)

The `ext` function does the same job as `exts` but for renamings
instead of substitutions. So composing `ext` with `ren` is the same as
composing `ren` with `exts`.

    ren (ext ρ) ≡ exts (ren ρ)            (ren-ext)

Thus, we can recast the `exts-cons-shift` equation in terms of
renamings.

    ren (ext ρ) ≡ ` Z • (ren ρ ⨟ ↑)       (ext-cons-Z-shift)

It is also useful to specialize the `sub-sub` equation of the σ
algebra to the situation where the first substitution is a renaming.

    ⟪ σ ⟫ (rename ρ M) ≡ ⟪ σ ∘ ρ ⟫ M       (rename-subst)

The `subst-zero M` substitution is equivalent to cons'ing
`M` onto the identity substitution.

    subst-zero M ≡ M • ids                (subst-Z-cons-ids)


Finally, sequencing `exts σ` with `subst-zero M` is equivalent to
cons'ing `M` onto `σ`.

    exts σ ⨟ subst-zero M ≡ (M • σ)       (subst-zero-exts-cons)


## Proofs of sub-head, sub-tail, sub-η, Z-shift, sub-idL, sub-dist, and sub-app

We start with the proofs that are immediate from the definitions of
the operators.

```
sub-head : ∀ {Γ Δ} {A} {M : Δ ⊢ A}{σ : Subst Γ Δ}
         → ⟪ M • σ ⟫ (` Z) ≡ M
sub-head = refl
```

```
sub-tail : ∀{Γ Δ} {A B} {M : Δ ⊢ A} {σ : Subst Γ Δ}
         → (↑ ⨟ M • σ) {A = B} ≡ σ
sub-tail = extensionality λ x → refl
```

```
sub-η : ∀{Γ Δ} {A B} {σ : Subst (Γ , A) Δ}
      → (⟪ σ ⟫ (` Z) • (↑ ⨟ σ)) {A = B} ≡ σ
sub-η {Γ}{Δ}{A}{B}{σ} = extensionality λ x → lemma
   where
   lemma : ∀ {x} → ((⟪ σ ⟫ (` Z)) • (↑ ⨟ σ)) x ≡ σ x
   lemma {x = Z} = refl
   lemma {x = S x} = refl
```

```
Z-shift : ∀{Γ}{A B}
        → ((` Z) • ↑) ≡ ids {Γ , A} {B}
Z-shift {Γ}{A}{B} = extensionality lemma
   where
   lemma : (x : Γ , A ∋ B) → ((` Z) • ↑) x ≡ ids x
   lemma Z = refl
   lemma (S y) = refl
```

```
sub-idL : ∀{Γ Δ} {σ : Subst Γ Δ} {A}
       → ids ⨟ σ ≡ σ {A}
sub-idL = extensionality λ x → refl
```

```
sub-dist :  ∀{Γ Δ Σ : Context} {A B} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
              {M : Δ ⊢ A}
         → ((M • σ) ⨟ τ) ≡ ((subst τ M) • (σ ⨟ τ)) {B}
sub-dist {Γ}{Δ}{Σ}{A}{B}{σ}{τ}{M} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Γ , A ∋ B} → ((M • σ) ⨟ τ) x ≡ ((subst τ M) • (σ ⨟ τ)) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl
```

```
sub-app : ∀{Γ Δ} {σ : Subst Γ Δ} {L : Γ ⊢ ★}{M : Γ ⊢ ★}
        → ⟪ σ ⟫ (L · M)  ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app = refl
```


## Interlude: congruences

In this section we establish congruence rules for the σ algebra
operators `•` and `⨟` and for `subst` and its helper functions `ext`,
`rename`, `exts`, and `subst-zero`. These congruence rules help with
the equational reasoning in the later sections of this chapter.

[JGS: I would have liked to prove all of these via cong and cong₂,
 but I have not yet found a way to make that work. It seems that
 various implicit parameters get in the way.]

```
cong-ext : ∀{Γ Δ}{ρ ρ′ : Rename Γ Δ}{B}
   → (∀{A} → ρ ≡ ρ′ {A})
     ---------------------------------
   → ∀{A} → ext ρ {B = B} ≡ ext ρ′ {A}
cong-ext{Γ}{Δ}{ρ}{ρ′}{B} rr {A} = extensionality λ x → lemma {x}
  where
  lemma : ∀{x : Γ , B ∋ A} → ext ρ x ≡ ext ρ′ x
  lemma {Z} = refl
  lemma {S y} = cong S_ (cong-app rr y)
```

```
cong-rename : ∀{Γ Δ}{ρ ρ′ : Rename Γ Δ}{B}{M : Γ ⊢ B}
        → (∀{A} → ρ ≡ ρ′ {A})
          ------------------------
        → rename ρ M ≡ rename ρ′ M
cong-rename {M = ` x} rr = cong `_ (cong-app rr x)
cong-rename {ρ = ρ} {ρ′ = ρ′} {M = ƛ N} rr =
   cong ƛ_ (cong-rename {ρ = ext ρ}{ρ′ = ext ρ′}{M = N} (cong-ext rr))
cong-rename {M = L · M} rr =
   cong₂ _·_ (cong-rename rr) (cong-rename rr)
```

```
cong-exts : ∀{Γ Δ}{σ σ′ : Subst Γ Δ}{B}
   → (∀{A} → σ ≡ σ′ {A})
     -----------------------------------
   → ∀{A} → exts σ {B = B} ≡ exts σ′ {A}
cong-exts{Γ}{Δ}{σ}{σ′}{B} ss {A} = extensionality λ x → lemma {x}
   where
   lemma : ∀{x} → exts σ x ≡ exts σ′ x
   lemma {Z} = refl
   lemma {S x} = cong (rename S_) (cong-app (ss {A}) x)
```

```
cong-sub : ∀{Γ Δ}{σ σ′ : Subst Γ Δ}{A}{M M′ : Γ ⊢ A}
            → (∀{A} → σ ≡ σ′ {A})  →  M ≡ M′
              ------------------------------
            → subst σ M ≡ subst σ′ M′
cong-sub {Γ} {Δ} {σ} {σ′} {A} {` x} ss refl = cong-app ss x
cong-sub {Γ} {Δ} {σ} {σ′} {A} {ƛ M} ss refl =
   cong ƛ_ (cong-sub {σ = exts σ}{σ′ = exts σ′} {M = M} (cong-exts ss) refl)
cong-sub {Γ} {Δ} {σ} {σ′} {A} {L · M} ss refl =
   cong₂ _·_ (cong-sub {M = L} ss refl) (cong-sub {M = M} ss refl)
```

```
cong-sub-zero : ∀{Γ}{B : Type}{M M′ : Γ ⊢ B}
  → M ≡ M′
    -----------------------------------------
  → ∀{A} → subst-zero M ≡ (subst-zero M′) {A}
cong-sub-zero {Γ}{B}{M}{M′} mm' {A} =
   extensionality λ x → cong (λ z → subst-zero z x) mm'
```

```
cong-cons : ∀{Γ Δ}{A}{M N : Δ ⊢ A}{σ τ : Subst Γ Δ}
  → M ≡ N  →  (∀{A} → σ {A} ≡ τ {A})
    --------------------------------
  → ∀{A} → (M • σ) {A} ≡ (N • τ) {A}
cong-cons{Γ}{Δ}{A}{M}{N}{σ}{τ} refl st {A′} = extensionality lemma
  where
  lemma : (x : Γ , A ∋ A′) → (M • σ) x ≡ (M • τ) x
  lemma Z = refl
  lemma (S x) = cong-app st x
```

```
cong-seq : ∀{Γ Δ Σ}{σ σ′ : Subst Γ Δ}{τ τ′ : Subst Δ Σ}
  → (∀{A} → σ {A} ≡ σ′ {A}) → (∀{A} → τ {A} ≡ τ′ {A})
  → ∀{A} → (σ ⨟ τ) {A} ≡ (σ′ ⨟ τ′) {A}
cong-seq {Γ}{Δ}{Σ}{σ}{σ′}{τ}{τ′} ss' tt' {A} = extensionality lemma
  where
  lemma : (x : Γ ∋ A) → (σ ⨟ τ) x ≡ (σ′ ⨟ τ′) x
  lemma x =
     begin
       (σ ⨟ τ) x
     ≡⟨⟩
       subst τ (σ x)
     ≡⟨ cong (subst τ) (cong-app ss' x) ⟩
       subst τ (σ′ x)
     ≡⟨ cong-sub{M = σ′ x} tt' refl ⟩
       subst τ′ (σ′ x)
     ≡⟨⟩
       (σ′ ⨟ τ′) x
     ∎
```


## Relating `rename`, `exts`, `ext`, and `subst-zero` to the σ algebra

In this section we establish equations that relate `subst` and its
helper functions (`rename`, `exts`, `ext`, and `subst-zero`) to terms
in the σ algebra.

The first equation we prove is

    rename ρ M ≡ ⟪ ren ρ ⟫ M              (rename-subst-ren)

Because `subst` uses the `exts` function, we need the following lemma
which says that `exts` and `ext` do the same thing except that `ext`
works on renamings and `exts` works on substitutions.

```
ren-ext : ∀ {Γ Δ}{B C : Type} {ρ : Rename Γ Δ}
        → ren (ext ρ {B = B}) ≡ exts (ren ρ) {C}
ren-ext {Γ}{Δ}{B}{C}{ρ} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Γ , B ∋ C} → (ren (ext ρ)) x ≡ exts (ren ρ) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl
```

With this lemma in hand, the proof is a straightforward induction on
the term `M`.

```
rename-subst-ren : ∀ {Γ Δ}{A} {ρ : Rename Γ Δ}{M : Γ ⊢ A}
                 → rename ρ M ≡ ⟪ ren ρ ⟫ M
rename-subst-ren {M = ` x} = refl
rename-subst-ren {ρ = ρ}{M = ƛ N} =
  begin
      rename ρ (ƛ N)
    ≡⟨⟩
      ƛ rename (ext ρ) N
    ≡⟨ cong ƛ_ (rename-subst-ren {ρ = ext ρ}{M = N}) ⟩
      ƛ ⟪ ren (ext ρ) ⟫ N
    ≡⟨ cong ƛ_ (cong-sub {M = N} ren-ext refl) ⟩
      ƛ ⟪ exts (ren ρ) ⟫  N
    ≡⟨⟩
      ⟪ ren ρ ⟫ (ƛ N)
  ∎
rename-subst-ren {M = L · M} = cong₂ _·_ rename-subst-ren rename-subst-ren
```

The substitution `ren S_` is equivalent to `↑`.

```
ren-shift : ∀{Γ}{A}{B}
          → ren S_ ≡ ↑ {A = B} {A}
ren-shift {Γ}{A}{B} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Γ ∋ A} → ren (S_{B = B}) x ≡ ↑ {A = B} x
  lemma {x = Z} = refl
  lemma {x = S x} = refl
```

The substitution `rename S_ M` is equivalent to shifting: `⟪ ↑ ⟫ M`.

```
rename-shift : ∀{Γ} {A} {B} {M : Γ ⊢ A}
             → rename (S_{B = B}) M ≡ ⟪ ↑ ⟫ M
rename-shift{Γ}{A}{B}{M} =
  begin
    rename S_ M
  ≡⟨ rename-subst-ren ⟩
    ⟪ ren S_ ⟫ M
  ≡⟨ cong-sub{M = M} ren-shift refl ⟩
    ⟪ ↑ ⟫ M
  ∎
```

Next we prove the equation `exts-cons-shift`, which states that `exts`
is equivalent to cons'ing Z onto the sequence formed by applying `σ`
and then shifting. The proof is by case analysis on the variable `x`,
using `rename-subst-ren` for when `x = S y`.

```
exts-cons-shift : ∀{Γ Δ} {A B} {σ : Subst Γ Δ}
                → exts σ {A} {B} ≡ (` Z • (σ ⨟ ↑))
exts-cons-shift = extensionality λ x → lemma{x = x}
  where
  lemma : ∀{Γ Δ} {A B} {σ : Subst Γ Δ} {x : Γ , B ∋ A}
                  → exts σ x ≡ (` Z • (σ ⨟ ↑)) x
  lemma {x = Z} = refl
  lemma {x = S y} = rename-subst-ren
```

As a corollary, we have a similar correspondence for `ren (ext ρ)`.

```
ext-cons-Z-shift : ∀{Γ Δ} {ρ : Rename Γ Δ}{A}{B}
                 → ren (ext ρ {B = B}) ≡ (` Z • (ren ρ ⨟ ↑)) {A}
ext-cons-Z-shift {Γ}{Δ}{ρ}{A}{B} =
  begin
    ren (ext ρ)
  ≡⟨ ren-ext ⟩
    exts (ren ρ)
  ≡⟨ exts-cons-shift{σ = ren ρ} ⟩
   ((` Z) • (ren ρ ⨟ ↑))
  ∎
```

Finally, the `subst-zero M` substitution is equivalent to cons'ing `M`
onto the identity substitution.

```
subst-Z-cons-ids : ∀{Γ}{A B : Type}{M : Γ ⊢ B}
                 → subst-zero M ≡ (M • ids) {A}
subst-Z-cons-ids = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ}{A B : Type}{M : Γ ⊢ B}{x : Γ , B ∋ A}
                      → subst-zero M x ≡ (M • ids) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl
```


## Proofs of sub-abs, sub-id, and rename-id

The equation `sub-abs` follows immediately from the equation
`exts-cons-shift`.

```
sub-abs : ∀{Γ Δ} {σ : Subst Γ Δ} {N : Γ , ★ ⊢ ★}
        → ⟪ σ ⟫ (ƛ N) ≡ ƛ ⟪ (` Z) • (σ ⨟ ↑) ⟫ N
sub-abs {σ = σ}{N = N} =
   begin
     ⟪ σ ⟫ (ƛ N)
   ≡⟨⟩
     ƛ ⟪ exts σ ⟫ N
   ≡⟨ cong ƛ_ (cong-sub{M = N} exts-cons-shift refl) ⟩
     ƛ ⟪ (` Z) • (σ ⨟ ↑) ⟫ N
   ∎
```

The proof of `sub-id` requires the following lemma which says that
extending the identity substitution produces the identity
substitution.

```
exts-ids : ∀{Γ}{A B}
         → exts ids ≡ ids {Γ , B} {A}
exts-ids {Γ}{A}{B} = extensionality lemma
  where lemma : (x : Γ , B ∋ A) → exts ids x ≡ ids x
        lemma Z = refl
        lemma (S x) = refl
```

The proof of `⟪ ids ⟫ M ≡ M` now follows easily by induction on `M`,
using `exts-ids` in the case for `M ≡ ƛ N`.

```
sub-id : ∀{Γ} {A} {M : Γ ⊢ A}
         → ⟪ ids ⟫ M ≡ M
sub-id {M = ` x} = refl
sub-id {M = ƛ N} =
   begin
     ⟪ ids ⟫ (ƛ N)
   ≡⟨⟩
     ƛ ⟪ exts ids ⟫ N
   ≡⟨ cong ƛ_ (cong-sub{M = N} exts-ids refl)  ⟩
     ƛ ⟪ ids ⟫ N
   ≡⟨ cong ƛ_ sub-id ⟩
     ƛ N
   ∎
sub-id {M = L · M} = cong₂ _·_ sub-id sub-id
```

The `rename-id` equation is a corollary is `sub-id`.

```
rename-id : ∀ {Γ}{A} {M : Γ ⊢ A}
  → rename (λ {A} x → x) M ≡ M
rename-id {M = M} =
   begin
     rename (λ {A} x → x) M
   ≡⟨ rename-subst-ren  ⟩
     ⟪ ren (λ {A} x → x) ⟫ M
   ≡⟨⟩
     ⟪ ids ⟫ M
   ≡⟨ sub-id  ⟩
     M
   ∎
```

## Proof of sub-idR

The proof of `sub-idR` follows directly from `sub-id`.

```
sub-idR : ∀{Γ Δ} {σ : Subst Γ Δ} {A}
       → (σ ⨟ ids) ≡ σ {A}
sub-idR {Γ}{σ = σ}{A} =
          begin
            σ ⨟ ids
          ≡⟨⟩
            ⟪ ids ⟫ ∘ σ
          ≡⟨ extensionality (λ x → sub-id) ⟩
            σ
          ∎
```


## Proof of sub-sub

The `sub-sub` equation states that sequenced substitutions `σ ⨟ τ`
are equivalent to first applying `σ` then applying `τ`.

    ⟪ τ ⟫ ⟪ σ ⟫ M  ≡ ⟪ σ ⨟ τ ⟫ M

The proof requires several lemmas. First, we need to prove the
specialization for renaming.

    rename ρ (rename ρ′ M) ≡ rename (ρ ∘ ρ′) M

This in turn requires the following lemma about `ext`.

```
compose-ext : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ} {A B}
            → ((ext ρ) ∘ (ext ρ′)) ≡ ext (ρ ∘ ρ′) {B} {A}
compose-ext = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ} {A B} {x : Γ , B ∋ A}
              → ((ext ρ) ∘ (ext ρ′)) x ≡ ext (ρ ∘ ρ′) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl
```

To prove that composing renamings is equivalent to applying one after
the other using `rename`, we proceed by induction on the term `M`,
using the `compose-ext` lemma in the case for `M ≡ ƛ N`.

```
compose-rename : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A}{ρ : Rename Δ Σ}{ρ′ : Rename Γ Δ}
  → rename ρ (rename ρ′ M) ≡ rename (ρ ∘ ρ′) M
compose-rename {M = ` x} = refl
compose-rename {Γ}{Δ}{Σ}{A}{ƛ N}{ρ}{ρ′} = cong ƛ_ G
  where
  G : rename (ext ρ) (rename (ext ρ′) N) ≡ rename (ext (ρ ∘ ρ′)) N
  G =
      begin
        rename (ext ρ) (rename (ext ρ′) N)
      ≡⟨ compose-rename{ρ = ext ρ}{ρ′ = ext ρ′} ⟩
        rename ((ext ρ) ∘ (ext ρ′)) N
      ≡⟨ cong-rename compose-ext ⟩
        rename (ext (ρ ∘ ρ′)) N
      ∎
compose-rename {M = L · M} = cong₂ _·_ compose-rename compose-rename
```

The next lemma states that if a renaming and substitution commute on
variables, then they also commute on terms. We explain the proof in
detail below.

```
commute-subst-rename : ∀{Γ Δ}{M : Γ ⊢ ★}{σ : Subst Γ Δ}
                        {ρ : ∀{Γ} → Rename Γ (Γ , ★)}
     → (∀{x : Γ ∋ ★} → exts σ {B = ★} (ρ x) ≡ rename ρ (σ x))
     → subst (exts σ {B = ★}) (rename ρ M) ≡ rename ρ (subst σ M)
commute-subst-rename {M = ` x} r = r
commute-subst-rename{Γ}{Δ}{ƛ N}{σ}{ρ} r =
   cong ƛ_ (commute-subst-rename{Γ , ★}{Δ , ★}{N}
               {exts σ}{ρ = ρ′} (λ {x} → H {x}))
   where
   ρ′ : ∀ {Γ} → Rename Γ (Γ , ★)
   ρ′ {∅} = λ ()
   ρ′ {Γ , ★} = ext ρ

   H : {x : Γ , ★ ∋ ★} → exts (exts σ) (ext ρ x) ≡ rename (ext ρ) (exts σ x)
   H {Z} = refl
   H {S y} =
     begin
       exts (exts σ) (ext ρ (S y))
     ≡⟨⟩
       rename S_ (exts σ (ρ y))
     ≡⟨ cong (rename S_) r ⟩
       rename S_ (rename ρ (σ y))
     ≡⟨ compose-rename ⟩
       rename (S_ ∘ ρ) (σ y)
     ≡⟨ cong-rename refl ⟩
       rename ((ext ρ) ∘ S_) (σ y)
     ≡⟨ sym compose-rename ⟩
       rename (ext ρ) (rename S_ (σ y))
     ≡⟨⟩
       rename (ext ρ) (exts σ (S y))
     ∎
commute-subst-rename {M = L · M}{ρ = ρ} r =
   cong₂ _·_ (commute-subst-rename{M = L}{ρ = ρ} r)
             (commute-subst-rename{M = M}{ρ = ρ} r)
```

The proof is by induction on the term `M`.

* If `M` is a variable, then we use the premise to conclude.

* If `M ≡ ƛ N`, we conclude using the induction hypothesis for
  `N`. However, to use the induction hypothesis, we must show
  that

        exts (exts σ) (ext ρ x) ≡ rename (ext ρ) (exts σ x)

  We prove this equation by cases on x.

    * If `x = Z`, the two sides are equal by definition.

    * If `x = S y`, we obtain the goal by the following equational reasoning.

            exts (exts σ) (ext ρ (S y))
          ≡ rename S_ (exts σ (ρ y))
          ≡ rename S_ (rename S_ (σ (ρ y)      (by the premise)
          ≡ rename (ext ρ) (exts σ (S y))      (by compose-rename)
          ≡ rename ((ext ρ) ∘ S_) (σ y)
          ≡ rename (ext ρ) (rename S_ (σ y))   (by compose-rename)
          ≡ rename (ext ρ) (exts σ (S y))

* If `M` is an application, we obtain the goal using the induction
  hypothesis for each subterm.


The last lemma needed to prove `sub-sub` states that the `exts`
function distributes with sequencing. It is a corollary of
`commute-subst-rename` as described below.  (It would have been nicer
to prove this directly by equational reasoning in the σ algebra, but
that would require the `sub-assoc` equation, whose proof depends on
`sub-sub`, which in turn depends on this lemma.)

```
exts-seq : ∀{Γ Δ Δ′} {σ₁ : Subst Γ Δ} {σ₂ : Subst Δ Δ′}
         → ∀ {A} → (exts σ₁ ⨟ exts σ₂) {A} ≡ exts (σ₁ ⨟ σ₂)
exts-seq = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ Δ Δ′}{A}{x : Γ , ★ ∋ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Δ′}
     → (exts σ₁ ⨟ exts σ₂) x ≡ exts (σ₁ ⨟ σ₂) x
  lemma {x = Z} = refl
  lemma {A = ★}{x = S x}{σ₁}{σ₂} =
     begin
       (exts σ₁ ⨟ exts σ₂) (S x)
     ≡⟨⟩
       ⟪ exts σ₂ ⟫ (rename S_ (σ₁ x))
     ≡⟨ commute-subst-rename{M = σ₁ x}{σ = σ₂}{ρ = S_} refl ⟩
       rename S_ (⟪ σ₂ ⟫ (σ₁ x))
     ≡⟨⟩
       rename S_ ((σ₁ ⨟ σ₂) x)
     ∎
```

The proof proceed by cases on `x`.

* If `x = Z`, the two sides are equal by the definition of `exts`
  and sequencing.

* If `x = S x`, we unfold the first use of `exts` and sequencing, then
  apply the lemma `commute-subst-rename`. We conclude by the
  definition of sequencing.


Now we come to the proof of `sub-sub`, which we explain below.

```
sub-sub : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ}
            → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
sub-sub {M = ` x} = refl
sub-sub {Γ}{Δ}{Σ}{A}{ƛ N}{σ₁}{σ₂} =
   begin
     ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ (ƛ N))
   ≡⟨⟩
     ƛ ⟪ exts σ₂ ⟫ (⟪ exts σ₁ ⟫ N)
   ≡⟨ cong ƛ_ (sub-sub{M = N}{σ₁ = exts σ₁}{σ₂ = exts σ₂}) ⟩
     ƛ ⟪ exts σ₁ ⨟ exts σ₂ ⟫ N
   ≡⟨ cong ƛ_ (cong-sub{M = N} (λ {A} → exts-seq) refl) ⟩
     ƛ ⟪ exts ( σ₁ ⨟ σ₂) ⟫ N
   ∎
sub-sub {M = L · M} = cong₂ _·_ (sub-sub{M = L}) (sub-sub{M = M})
```

We proceed by induction on the term `M`.

* If `M = x`, then both sides are equal to `σ₂ (σ₁ x)`.

* If `M = ƛ N`, we first use the induction hypothesis to show that

        ƛ ⟪ exts σ₂ ⟫ (⟪ exts σ₁ ⟫ N) ≡ ƛ ⟪ exts σ₁ ⨟ exts σ₂ ⟫ N

  and then use the lemma `exts-seq` to show

        ƛ ⟪ exts σ₁ ⨟ exts σ₂ ⟫ N ≡ ƛ ⟪ exts ( σ₁ ⨟ σ₂) ⟫ N

* If `M` is an application, we use the induction hypothesis
  for both subterms.


The following corollary of `sub-sub` specializes the first
substitution to a renaming.

```
rename-subst : ∀{Γ Δ Δ′}{M : Γ ⊢ ★}{ρ : Rename Γ Δ}{σ : Subst Δ Δ′}
             → ⟪ σ ⟫ (rename ρ M) ≡ ⟪ σ ∘ ρ ⟫ M
rename-subst {Γ}{Δ}{Δ′}{M}{ρ}{σ} =
   begin
     ⟪ σ ⟫ (rename ρ M)
   ≡⟨ cong ⟪ σ ⟫ (rename-subst-ren{M = M}) ⟩
     ⟪ σ ⟫ (⟪ ren ρ ⟫ M)
   ≡⟨ sub-sub{M = M} ⟩
     ⟪ ren ρ ⨟ σ ⟫ M
   ≡⟨⟩
     ⟪ σ ∘ ρ ⟫ M
   ∎
```


## Proof of sub-assoc

The proof of `sub-assoc` follows directly from `sub-sub` and the
definition of sequencing.

```
sub-assoc : ∀{Γ Δ Σ Ψ : Context} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
             {θ : Subst Σ Ψ}
          → ∀{A} → (σ ⨟ τ) ⨟ θ ≡ (σ ⨟ τ ⨟ θ) {A}
sub-assoc {Γ}{Δ}{Σ}{Ψ}{σ}{τ}{θ}{A} = extensionality λ x → lemma{x = x}
  where
  lemma : ∀ {x : Γ ∋ A} → ((σ ⨟ τ) ⨟ θ) x ≡ (σ ⨟ τ ⨟ θ) x
  lemma {x} =
      begin
        ((σ ⨟ τ) ⨟ θ) x
      ≡⟨⟩
        ⟪ θ ⟫ (⟪ τ ⟫ (σ x))
      ≡⟨ sub-sub{M = σ x} ⟩
        ⟪ τ ⨟ θ ⟫ (σ x)
      ≡⟨⟩
        (σ ⨟ τ ⨟ θ) x
      ∎
```

## Proof of subst-zero-exts-cons

The last equation we needed to prove `subst-zero-exts-cons` was
`sub-assoc`, so we can now go ahead with its proof.  We simply apply
the equations for `exts` and `subst-zero` and then apply the σ algebra
equation to arrive at the normal form `M • σ`.

```
subst-zero-exts-cons : ∀{Γ Δ}{σ : Subst Γ Δ}{B}{M : Δ ⊢ B}{A}
                     → exts σ ⨟ subst-zero M ≡ (M • σ) {A}
subst-zero-exts-cons {Γ}{Δ}{σ}{B}{M}{A} =
    begin
      exts σ ⨟ subst-zero M
    ≡⟨ cong-seq exts-cons-shift subst-Z-cons-ids ⟩
      (` Z • (σ ⨟ ↑)) ⨟ (M • ids)
    ≡⟨ sub-dist ⟩
      (⟪ M • ids ⟫ (` Z)) • ((σ ⨟ ↑) ⨟ (M • ids))
    ≡⟨ cong-cons (sub-head{σ = ids}) refl ⟩
      M • ((σ ⨟ ↑) ⨟ (M • ids))
    ≡⟨ cong-cons refl (sub-assoc{σ = σ}) ⟩
      M • (σ ⨟ (↑ ⨟ (M • ids)))
    ≡⟨ cong-cons refl (cong-seq{σ = σ} refl (sub-tail{M = M}{σ = ids})) ⟩
      M • (σ ⨟ ids)
    ≡⟨ cong-cons refl (sub-idR{σ = σ}) ⟩
      M • σ
    ∎
```


## Proof of the substitution lemma

We first prove the generalized form of the substitution lemma, showing
that a substitution `σ` commutes with the substitution of `M` into
`N`.

    ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])

This proof is where the σ algebra pays off.  The proof is by direct
equational reasoning. Starting with the left-hand side, we apply σ
algebra equations, oriented left-to-right, until we arrive at the
normal form

    ⟪ ⟪ σ ⟫ M • σ ⟫ N

We then do the same with the right-hand side, arriving at the same
normal form.

```
subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{σ : Subst Γ Δ }
    → ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
subst-commute {Γ}{Δ}{N}{M}{σ} =
     begin
       ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ]
     ≡⟨⟩
       ⟪ subst-zero (⟪ σ ⟫ M) ⟫ (⟪ exts σ ⟫ N)
     ≡⟨ cong-sub {M = ⟪ exts σ ⟫ N} subst-Z-cons-ids refl ⟩
       ⟪ ⟪ σ ⟫ M • ids ⟫ (⟪ exts σ ⟫ N)
     ≡⟨ sub-sub {M = N} ⟩
       ⟪ (exts σ) ⨟ ((⟪ σ ⟫ M) • ids) ⟫ N
     ≡⟨ cong-sub {M = N} (cong-seq exts-cons-shift refl) refl ⟩
       ⟪ (` Z • (σ ⨟ ↑)) ⨟ (⟪ σ ⟫ M • ids) ⟫ N
     ≡⟨ cong-sub {M = N} (sub-dist {M = ` Z}) refl ⟩
       ⟪ ⟪ ⟪ σ ⟫ M • ids ⟫ (` Z) • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
     ≡⟨⟩
       ⟪ ⟪ σ ⟫ M • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
     ≡⟨ cong-sub{M = N} (cong-cons refl (sub-assoc{σ = σ})) refl ⟩
       ⟪ ⟪ σ ⟫ M • (σ ⨟ ↑ ⨟ ⟪ σ ⟫ M • ids) ⟫ N
     ≡⟨ cong-sub{M = N} refl refl ⟩
       ⟪ ⟪ σ ⟫ M • (σ ⨟ ids) ⟫ N
     ≡⟨ cong-sub{M = N} (cong-cons refl (sub-idR{σ = σ})) refl ⟩
       ⟪ ⟪ σ ⟫ M • σ ⟫ N
     ≡⟨ cong-sub{M = N} (cong-cons refl (sub-idL{σ = σ})) refl ⟩
       ⟪ ⟪ σ ⟫ M • (ids ⨟ σ) ⟫ N
     ≡⟨ cong-sub{M = N} (sym sub-dist) refl ⟩
       ⟪ M • ids ⨟ σ ⟫ N
     ≡⟨ sym (sub-sub{M = N}) ⟩
       ⟪ σ ⟫ (⟪ M • ids ⟫ N)
     ≡⟨ cong ⟪ σ ⟫ (sym (cong-sub{M = N} subst-Z-cons-ids refl)) ⟩
       ⟪ σ ⟫ (N [ M ])
     ∎
```

A corollary of `subst-commute` is that `rename` also commutes with
substitution. In the proof below, we first exchange `rename ρ` for
the substitution `⟪ ren ρ ⟫`, and apply `subst-commute`, and
then convert back to `rename ρ`.

```
rename-subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {Γ}{Δ}{N}{M}{ρ} =
     begin
       (rename (ext ρ) N) [ rename ρ M ]
     ≡⟨ cong-sub (cong-sub-zero (rename-subst-ren{M = M}))
                 (rename-subst-ren{M = N}) ⟩
       (⟪ ren (ext ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
     ≡⟨ cong-sub refl (cong-sub{M = N} ren-ext refl) ⟩
       (⟪ exts (ren ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
     ≡⟨ subst-commute{N = N} ⟩
       subst (ren ρ) (N [ M ])
     ≡⟨ sym (rename-subst-ren) ⟩
       rename ρ (N [ M ])
     ∎
```

To present the substitution lemma, we introduce the following notation
for substituting a term `M` for index 1 within term `N`.

```
_〔_〕 : ∀ {Γ A B C}
        → Γ , B , C ⊢ A
        → Γ ⊢ B
          ---------
        → Γ , C ⊢ A
_〔_〕 {Γ} {A} {B} {C} N M =
   subst {Γ , B , C} {Γ , C} (exts (subst-zero M)) {A} N
```

The substitution lemma is stated as follows and proved as a corollary
of the `subst-commute` lemma.

```
substitution : ∀{Γ}{M : Γ , ★ , ★ ⊢ ★}{N : Γ , ★ ⊢ ★}{L : Γ ⊢ ★}
    → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution{M = M}{N = N}{L = L} =
   sym (subst-commute{N = M}{M = N}{σ = subst-zero L})
```


## Notes

Most of the properties and proofs in this file are based on the paper
_Autosubst: Reasoning with de Bruijn Terms and Parallel Substitution_
by Schafer, Tebbi, and Smolka (ITP 2015). That paper, in turn, is
based on the paper of Abadi, Cardelli, Curien, and Levy (1991) that
defines the σ algebra.


## Unicode

This chapter uses the following unicode:

    ⟪  U+27EA  MATHEMATICAL LEFT DOUBLE ANGLE BRACKET (\<<)
    ⟫  U+27EA  MATHEMATICAL RIGHT DOUBLE ANGLE BRACKET (\>>)
    ↑  U+2191  UPWARDS ARROW (\u)
    •  U+2022  BULLET (\bub)
    ⨟  U+2A1F  Z NOTATION SCHEMA COMPOSITION (C-x 8 RET Z NOTATION SCHEMA COMPOSITION)
    〔  U+3014  LEFT TORTOISE SHELL BRACKET (\( option 9 on page 2)
    〕  U+3015  RIGHT TORTOISE SHELL BRACKET (\) option 9 on page 2)
