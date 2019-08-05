---
title     : "Confluence of the untyped lambda calculus"
layout    : page
prev      : /Untyped/
permalink : /Confluence/
next      : /CallByName/
---

```
module plfa.Confluence where
```

## Introduction

In this chapter we prove that beta reduction is _confluent_, a
property also known as _Church-Rosser_. That is, if there is a
reduction sequence from any term `L` to two different terms `M₁` and
`M₂`, then there exist reduction sequences from those two terms to
some common term `N`. In pictures:

        L
       / \
      /   \
     /     \
    M₁      M₂
     \     /
      \   /
       \ /
        N

where downward lines are instances of `—↠`.

Confluence is studied in many other kinds of rewrite systems besides
the lambda calculus, and it is well known how to prove confluence in
rewrite systems that enjoy the _diamond property_, a single-step
version of confluence. Let `⇛` be a relation.  Then `⇛` has the
diamond property if whenever `L ⇛ M₁` and `L ⇛ M₂`, then there exists
an `N` such that `M₁ ⇛ N` and `M₂ ⇛ N`. This is just an instance of
the same picture above, where downward lines are now instance of `⇛`.
If we write `⇛*` for the reflexive and transitive closure of `⇛`, then
confluence of `⇛*` follows immediately from the diamond property.

Unfortunately, reduction in the lambda calculus does not satisfy the
diamond property. Here is a counter example.

    (λ x. x x)((λ x. x) a) —→ (λ x. x x) a
    (λ x. x x)((λ x. x) a) —→ ((λ x. x) a) ((λ x. x) a)

Both terms can reduce to `a a`, but the second term requires two steps
to get there, not one.

To side-step this problem, we'll define an auxilliary reduction
relation, called _parallel reduction_, that can perform many
reductions simultaneously and thereby satisfy the diamond property.
Furthermore, we show that a parallel reduction sequence exists between
any two terms if and only if a beta reduction sequence exists between them.
Thus, we can reduce the proof of confluence for beta reduction to
confluence for parallel reduction.


## Imports

```
open import plfa.Substitution using (Rename; Subst)
open import plfa.Untyped
    using (_—→_; β; ξ₁; ξ₂; ζ; _—↠_; _—→⟨_⟩_; _∎;
           abs-cong; appL-cong; appR-cong; —↠-trans;
           _⊢_; _∋_; `_; #_; _,_; ★; ƛ_; _·_; _[_];
           rename; ext; exts; Z; S_; subst; subst-zero)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Function using (_∘_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
     renaming (_,_ to ⟨_,_⟩)
```

## Parallel Reduction

The parallel reduction relation is defined as follows.

```
infix 2 _⇛_

data _⇛_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  pvar : ∀{Γ A}{x : Γ ∋ A}
         ---------
       → (` x) ⇛ (` x)

  pabs : ∀{Γ}{N N′ : Γ , ★ ⊢ ★}
       → N ⇛ N′
         ----------
       → ƛ N ⇛ ƛ N′

  papp : ∀{Γ}{L L′ M M′ : Γ ⊢ ★}
       → L ⇛ L′
       → M ⇛ M′
         -----------------
       → L · M ⇛ L′ · M′

  pbeta : ∀{Γ}{N N′  : Γ , ★ ⊢ ★}{M M′ : Γ ⊢ ★}
       → N ⇛ N′
       → M ⇛ M′
         -----------------------
       → (ƛ N) · M  ⇛  N′ [ M′ ]
```
The first three rules are congruences that reduce each of their
parts simultaneously. The last rule reduces a lambda term and
term in parallel followed by a beta step.

We remark that the `pabs`, `papp`, and `pbeta` rules perform reduction
on all their subexpressions simultaneously. Also, the `pabs` rule is
akin to the `ζ` rule and `pbeta` is akin to `β`.

Parallel reduction is reflexive.

```
par-refl : ∀{Γ A}{M : Γ ⊢ A} → M ⇛ M
par-refl {Γ} {A} {` x} = pvar
par-refl {Γ} {★} {ƛ N} = pabs par-refl
par-refl {Γ} {★} {L · M} = papp par-refl par-refl
```
We define the sequences of parallel reduction as follows.

```
infix  2 _⇛*_
infixr 2 _⇛⟨_⟩_
infix  3 _∎

data _⇛*_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M ⇛* M

  _⇛⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ⇛ M
    → M ⇛* N
      ---------
    → L ⇛* N
```


#### Exercise `par-diamond-eg`

Revisit the counter example to the diamond property for reduction by
showing that the diamond property holds for parallel reduction in that
case.

```
-- Your code goes here
```


## Equivalence between parallel reduction and reduction

Here we prove that for any `M` and `N`, `M ⇛* N` if and only if `M —↠ N`.
The only-if direction is particularly easy. We start by showing
that if `M —→ N`, then `M ⇛ N`. The proof is by induction on
the reduction `M —→ N`.

```
beta-par : ∀{Γ A}{M N : Γ ⊢ A}
         → M —→ N
           ------
         → M ⇛ N
beta-par {Γ} {★} {L · M} (ξ₁ r) = papp (beta-par {M = L} r) par-refl
beta-par {Γ} {★} {L · M} (ξ₂ r) = papp par-refl (beta-par {M = M} r)
beta-par {Γ} {★} {(ƛ N) · M} β = pbeta par-refl par-refl
beta-par {Γ} {★} {ƛ N} (ζ r) = pabs (beta-par r)
```

With this lemma in hand we complete the only-if direction,
that `M —↠ N` implies `M ⇛* N`. The proof is a straightforward
induction on the reduction sequence `M —↠ N`.

```
betas-pars : ∀{Γ A} {M N : Γ ⊢ A}
           → M —↠ N
             ------
           → M ⇛* N
betas-pars {Γ} {A} {M₁} {.M₁} (M₁ ∎) = M₁ ∎
betas-pars {Γ} {A} {.L} {N} (L —→⟨ b ⟩ bs) =
   L ⇛⟨ beta-par b ⟩ betas-pars bs
```

Now for the other direction, that `M ⇛* N` implies `M —↠ N`.  The
proof of this direction is a bit different because it's not the case
that `M ⇛ N` implies `M —→ N`. After all, `M ⇛ N` performs many
reductions. So instead we shall prove that `M ⇛ N` implies `M —↠ N`.

```
par-betas : ∀{Γ A}{M N : Γ ⊢ A}
         → M ⇛ N
           ------
         → M —↠ N
par-betas {Γ} {A} {.(` _)} (pvar{x = x}) = (` x) ∎
par-betas {Γ} {★} {ƛ N} (pabs p) = abs-cong (par-betas p)
par-betas {Γ} {★} {L · M} (papp p₁ p₂) =
   —↠-trans (appL-cong{M = M} (par-betas p₁)) (appR-cong (par-betas p₂))
par-betas {Γ} {★} {(ƛ N) · M} (pbeta{N′ = N′}{M′ = M′} p₁ p₂) =
  let ih₁ = par-betas p₁ in
  let ih₂ = par-betas p₂ in
  let a : (ƛ N) · M —↠ (ƛ N′) · M
      a = appL-cong{M = M} (abs-cong ih₁) in
  let b : (ƛ N′) · M —↠ (ƛ N′) · M′
      b = appR-cong{L = ƛ N′} ih₂ in
  let c = (ƛ N′) · M′ —→⟨ β ⟩ N′ [ M′ ] ∎ in
  —↠-trans (—↠-trans a b) c
```

The proof is by induction on `M ⇛ N`.

* Suppose `x ⇛ x`. We immediately have `x —↠ x`.

* Suppose `ƛ N ⇛ ƛ N′` because `N ⇛ N′`. By the induction hypothesis
  we have `N —↠ N′`. We conclude that `ƛ N —↠ ƛ N′` because
  `—↠` is a congruence.

* Suppose `L · M ⇛ L′ · M′` because `L ⇛ L′` and `M ⇛ M′`.
  By the induction hypothesis, we have `L —↠ L′` and `M —↠ M′`.
  So `L · M —↠ L′ · M` and then `L′ · M  —↠ L′ · M′`
  because `—↠` is a congruence. We conclude using the transitity
  of `—↠`.

* Suppose `(ƛ N) · M  ⇛  N′ [ M′ ]` because `N ⇛ N′` and `M ⇛ M′`.
  By similar reasoning, we have
  `(ƛ N) · M —↠ (ƛ N′) · M′`.
  Of course, `(ƛ N′) · M′ —→ N′ [ M′ ]`, so we can conclude
  using the transitivity of `—↠`.

With this lemma in hand, we complete the proof that `M ⇛* N` implies
`M —↠ N` with a simple induction on `M ⇛* N`.

```
pars-betas : ∀{Γ A} {M N : Γ ⊢ A}
           → M ⇛* N
             ------
           → M —↠ N
pars-betas (M₁ ∎) = M₁ ∎
pars-betas (L ⇛⟨ p ⟩ ps) = —↠-trans (par-betas p) (pars-betas ps)
```


## Substitution lemma for parallel reduction

Our next goal is the prove the diamond property for parallel
reduction. But to do that, we need to prove that substitution
respects parallel reduction. That is, if
`N ⇛ N′` and `M ⇛ M′`, then `N [ M ] ⇛ N′ [ M′ ]`.
We cannot prove this directly by induction, so we
generalize it to: if `N ⇛ N′` and
the substitution `σ` pointwise parallel reduces to `τ`,
then `subst σ N ⇛ subst τ N′`. We define the notion
of pointwise parallel reduction as follows.

```
par-subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
par-subst {Γ}{Δ} σ σ′ = ∀{A}{x : Γ ∋ A} → σ x ⇛ σ′ x
```

Because substitution depends on the extension function `exts`, which
in turn relies on `rename`, we start with a version of the
substitution lemma, called `par-rename`, that is specialized to
renamings.  The proof of `par-rename` relies on the fact that renaming
and substitution commute with one another, which is a lemma that we
import from Chapter [Substitution]({{ site.baseurl }}/Substitution/)
and restate here.

```
rename-subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {N = N} = plfa.Substitution.rename-subst-commute {N = N}
```

Now for the `par-rename` lemma.

```
par-rename : ∀{Γ Δ A} {ρ : Rename Γ Δ} {M M′ : Γ ⊢ A}
  → M ⇛ M′
    ------------------------
  → rename ρ M ⇛ rename ρ M′
par-rename pvar = pvar
par-rename (pabs p) = pabs (par-rename p)
par-rename (papp p₁ p₂) = papp (par-rename p₁) (par-rename p₂)
par-rename {Γ}{Δ}{A}{ρ} (pbeta{Γ}{N}{N′}{M}{M′} p₁ p₂)
     with pbeta (par-rename{ρ = ext ρ} p₁) (par-rename{ρ = ρ} p₂)
... | G rewrite rename-subst-commute{Γ}{Δ}{N′}{M′}{ρ} = G

```

The proof is by induction on `M ⇛ M′`. The first four cases
are straightforward so we just consider the last one for `pbeta`.

* Suppose `(ƛ N) · M  ⇛  N′ [ M′ ]` because `N ⇛ N′` and `M ⇛ M′`.
  By the induction hypothesis, we have
  `rename (ext ρ) N ⇛ rename (ext ρ) N′` and
  `rename ρ M ⇛ rename ρ M′`.
  So by `pbeta` we have
  `(ƛ rename (ext ρ) N) · (rename ρ M) ⇛ (rename (ext ρ) N) [ rename ρ M ]`.
  However, to conclude we instead need parallel reduction to
  `rename ρ (N [ M ])`. But thankfully, renaming and substitution
  commute with one another.


With the `par-rename` lemma in hand, it is straightforward to show
that extending substitutions preserves the pointwise parallel
reduction relation.

```
par-subst-exts : ∀{Γ Δ} {σ τ : Subst Γ Δ}
   → par-subst σ τ
   → ∀{B} → par-subst (exts σ {B = B}) (exts τ)
par-subst-exts s {x = Z} = pvar
par-subst-exts s {x = S x} = par-rename s
```

The next lemma that we need to prove that substitution respects
parallel reduction is the following one, which states that
simultaneoous substitution commutes with single substitution. We import this
lemma from Chapter [Substitution]({{ site.baseurl }}/Substitution/)
and restate it below.

```
subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{σ : Subst Γ Δ }
    → subst (exts σ) N [ subst σ M ] ≡ subst σ (N [ M ])
subst-commute {N = N} = plfa.Substitution.subst-commute {N = N}
```

We are ready to prove that substitution respects parallel reduction.

```
subst-par : ∀{Γ Δ A} {σ τ : Subst Γ Δ} {M M′ : Γ ⊢ A}
   → par-subst σ τ  →  M ⇛ M′
     --------------------------
   → subst σ M ⇛ subst τ M′
subst-par {Γ} {Δ} {A} {σ} {τ} {` x} s pvar = s
subst-par {Γ} {Δ} {A} {σ} {τ} {ƛ N} s (pabs p) =
   pabs (subst-par {σ = exts σ} {τ = exts τ}
            (λ {A}{x} → par-subst-exts s {x = x}) p)
subst-par {Γ} {Δ} {★} {σ} {τ} {L · M} s (papp p₁ p₂) =
   papp (subst-par s p₁) (subst-par s p₂)
subst-par {Γ} {Δ} {★} {σ} {τ} {(ƛ N) · M} s (pbeta{N′ = N′}{M′ = M′} p₁ p₂)
    with pbeta (subst-par{σ = exts σ}{τ = exts τ}{M = N}
                        (λ{A}{x} → par-subst-exts s {x = x}) p₁)
               (subst-par {σ = σ} s p₂)
... | G rewrite subst-commute{N = N′}{M = M′}{σ = τ} =
    G
```

We proceed by induction on `M ⇛ M′`.

* Suppose `x ⇛ x`. We conclude that `σ x ⇛ τ x` using
  the premise `par-subst σ τ`.

* Suppose `ƛ N ⇛ ƛ N′` because `N ⇛ N′`.
  To use the induction hypothesis, we need `par-subst (exts σ) (exts τ)`,
  which we obtain by `par-subst-exts`.
  So we have `subst (exts σ) N ⇛ subst (exts τ) N′`
  and conclude by rule `pabs`.

* Suppose `L · M ⇛ L′ · M′` because `L ⇛ L′` and `M ⇛ M′`.
  By the induction hypothesis we have
  `subst σ L ⇛ subst τ L′` and `subst σ M ⇛ subst τ M′`, so
  we conclude by rule `papp`.

* Suppose `(ƛ N) · M  ⇛  N′ [ M′ ]` because `N ⇛ N′` and `M ⇛ M′`.
  Again we obtain `par-subst (exts σ) (exts τ)` by `par-subst-exts`.
  So by the induction hypothesis, we have
  `subst (exts σ) N ⇛ subst (exts τ) N′` and
  `subst σ M ⇛ subst τ M′`. Then by rule `pbeta`, we have parallel reduction
  to `subst (exts τ) N′ [ subst τ M′ ]`.
  Substitution commutes with itself in the following sense.
  For any σ, N, and M, we have

        (subst (exts σ) N) [ subst σ M ] ≡ subst σ (N [ M ])

  So we have parallel reduction to `subst τ (N′ [ M′ ])`.


Of course, if `M ⇛ M′`, then `subst-zero M` pointwise parallel reduces
to `subst-zero M′`.

```
par-subst-zero : ∀{Γ}{A}{M M′ : Γ ⊢ A}
       → M ⇛ M′
       → par-subst (subst-zero M) (subst-zero M′)
par-subst-zero {M} {M′} p {A} {Z} = p
par-subst-zero {M} {M′} p {A} {S x} = pvar
```

We conclude this section with the desired corollary, that substitution
respects parallel reduction.

```
sub-par : ∀{Γ A B} {N N′ : Γ , A ⊢ B} {M M′ : Γ ⊢ A}
   → N ⇛ N′
   → M ⇛ M′
     --------------------------
   → N [ M ] ⇛ N′ [ M′ ]
sub-par pn pm = subst-par (par-subst-zero pm) pn
```


## Parallel reduction satisfies the diamond property

The heart of the confluence proof is made of stone, or rather, of
diamond!  We show that parallel reduction satisfies the diamond
property: that if `M ⇛ N` and `M ⇛ N′`, then `N ⇛ L` and `N′ ⇛ L` for
some `L`.  The proof is relatively easy; it is parallel reduction's
_raison d'etre_.

```
par-diamond : ∀{Γ A} {M N N′ : Γ ⊢ A}
  → M ⇛ N
  → M ⇛ N′
    ---------------------------------
  → Σ[ L ∈ Γ ⊢ A ] (N ⇛ L) × (N′ ⇛ L)
par-diamond (pvar{x = x}) pvar = ⟨ ` x , ⟨ pvar , pvar ⟩ ⟩
par-diamond (pabs p1) (pabs p2)
    with par-diamond p1 p2
... | ⟨ L′ , ⟨ p3 , p4 ⟩ ⟩ =
      ⟨ ƛ L′ , ⟨ pabs p3 , pabs p4 ⟩ ⟩
par-diamond{Γ}{A}{L · M}{N}{N′} (papp{Γ}{L}{L₁}{M}{M₁} p1 p3)
                                (papp{Γ}{L}{L₂}{M}{M₂} p2 p4)
    with par-diamond p1 p2
... | ⟨ L₃ , ⟨ p5 , p6 ⟩ ⟩
    with par-diamond p3 p4
... | ⟨ M₃ , ⟨ p7 , p8 ⟩ ⟩ =
      ⟨ (L₃ · M₃) , ⟨ (papp p5 p7) , (papp p6 p8) ⟩ ⟩
par-diamond (papp (pabs p1) p3) (pbeta p2 p4)
    with par-diamond p1 p2
... | ⟨ N₃ , ⟨ p5 , p6 ⟩ ⟩
    with par-diamond p3 p4
... | ⟨ M₃ , ⟨ p7 , p8 ⟩ ⟩ =
    ⟨ N₃ [ M₃ ] , ⟨ pbeta p5 p7 , sub-par p6 p8 ⟩ ⟩
par-diamond (pbeta p1 p3) (papp (pabs p2) p4)
    with par-diamond p1 p2
... | ⟨ N₃ , ⟨ p5 , p6 ⟩ ⟩
    with par-diamond p3 p4
... | ⟨ M₃ , ⟨ p7 , p8 ⟩ ⟩ =
    ⟨ (N₃ [ M₃ ]) , ⟨ sub-par p5  p7 , pbeta p6 p8 ⟩ ⟩
par-diamond {Γ}{A} (pbeta p1 p3) (pbeta p2 p4)
    with par-diamond p1 p2
... | ⟨ N₃ , ⟨ p5 , p6 ⟩ ⟩
    with par-diamond p3 p4
... | ⟨ M₃ , ⟨ p7 , p8 ⟩ ⟩ =
      ⟨ N₃ [ M₃ ] , ⟨ sub-par p5 p7 , sub-par p6 p8 ⟩ ⟩
```

The proof is by induction on both premises.

* Suppose `x ⇛ x` and `x ⇛ x`.
  We choose `L = x` and immediately have `x ⇛ x` and `x ⇛ x`.

* Suppose `ƛ N ⇛ ƛ N′` and `ƛ N ⇛ ƛ N′′`.
  By the induction hypothesis, there exists `L′` such that
  `N′ ⇛ L′` and `N′′ ⇛ L′`. We choose `L = ƛ L′` and
  by `pabs` conclude that `ƛ N′ ⇛ ƛ L′` and `ƛ N′′ ⇛ ƛ L′.

* Suppose that `L · M ⇛ L₁ · M₁` and `L · M ⇛ L₂ · M₂`.
  By the induction hypothesis we have
  `L₁ ⇛ L₃` and `L₂ ⇛ L₃` for some `L₃`.
  Likewise, we have
  `M₁ ⇛ M₃` and `M₂ ⇛ M₃` for some `M₃`.
  We choose `L = L₃ · M₃` and conclude with two uses of `papp`.

* Suppose that `(ƛ N) · M ⇛ (ƛ N₁) · M₁` and `(ƛ N) · M ⇛ N₂ [ M₂ ]`
  By the induction hypothesis we have
  `N₁ ⇛ N₃` and `N₂ ⇛ N₃` for some `N₃`.
  Likewise, we have
  `M₁ ⇛ M₃` and `M₂ ⇛ M₃` for some `M₃`.
  We choose `L = N₃ [ M₃ ]`.
  We have `(ƛ N₁) · M₁ ⇛ N₃ [ M₃ ]` by rule `pbeta`
  and conclude that `N₂ [ M₂ ] ⇛ N₃ [ M₃ ]` because
  substitution respects parallel reduction.

* Suppose that `(ƛ N) · M ⇛ N₁ [ M₁ ]` and `(ƛ N) · M ⇛ (ƛ N₂) · M₂`.
  The proof of this case is the mirror image of the last one.

* Suppose that `(ƛ N) · M ⇛ N₁ [ M₁ ]` and `(ƛ N) · M ⇛ N₂ [ M₂ ]`.
  By the induction hypothesis we have
  `N₁ ⇛ N₃` and `N₂ ⇛ N₃` for some `N₃`.
  Likewise, we have
  `M₁ ⇛ M₃` and `M₂ ⇛ M₃` for some `M₃`.
  We choose `L = N₃ [ M₃ ]`.
  We have both `(ƛ N₁) · M₁ ⇛ N₃ [ M₃ ]`
  and `(ƛ N₂) · M₂ ⇛ N₃ [ M₃ ]`
  by rule `pbeta`

#### Exercise

Draw pictures that represent the proofs of each of the six
cases in the above proof of `par-diamond`.


## Proof of confluence for parallel reduction

As promised at the beginning, the proof that parallel reduction is
confluent is easy now that we know it satisfies the diamond property.
We just need to prove the strip lemma, which states that
if `M ⇛ N` and `M ⇛* N′`, then
`N ⇛* L` and `N′ ⇛ L` for some `L`.
The following diagram illustrates the strip lemma

        M
       / \
      1   *
     /     \
    N       N′
     \     /
      *   1
       \ /
        L

where downward lines are instances of `⇛` or `⇛*`, depending on how
they are marked.

The proof of the strip lemma is a straightforward induction on `M ⇛* N′`,
using the diamond property in the induction step.

```
strip : ∀{Γ A} {M N N′ : Γ ⊢ A}
  → M ⇛ N
  → M ⇛* N′
    ------------------------------------
  → Σ[ L ∈ Γ ⊢ A ] (N ⇛* L)  ×  (N′ ⇛ L)
strip{Γ}{A}{M}{N}{N′} mn (M ∎) = ⟨ N , ⟨ N ∎ , mn ⟩ ⟩
strip{Γ}{A}{M}{N}{N′} mn (M ⇛⟨ mm' ⟩ m'n')
    with par-diamond mn mm'
... | ⟨ L , ⟨ nl , m'l ⟩ ⟩
    with strip m'l m'n'
... | ⟨ L′ , ⟨ ll' , n'l' ⟩ ⟩ =
    ⟨ L′ , ⟨ (N ⇛⟨ nl ⟩ ll') , n'l' ⟩ ⟩
```

The proof of confluence for parallel reduction is now proved by
induction on the sequence `M ⇛* N`, using the above lemma in the
induction step.

```
par-confluence : ∀{Γ A} {L M₁ M₂ : Γ ⊢ A}
  → L ⇛* M₁
  → L ⇛* M₂
    ------------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (M₁ ⇛* N) × (M₂ ⇛* N)
par-confluence {Γ}{A}{L}{.L}{N} (L ∎) L⇛*N = ⟨ N , ⟨ L⇛*N , N ∎ ⟩ ⟩
par-confluence {Γ}{A}{L}{M₁′}{M₂} (L ⇛⟨ L⇛M₁ ⟩ M₁⇛*M₁′) L⇛*M₂
    with strip L⇛M₁ L⇛*M₂
...    | ⟨ N , ⟨ M₁⇛*N , M₂⇛N ⟩ ⟩
         with par-confluence M₁⇛*M₁′ M₁⇛*N
...         | ⟨ N′ , ⟨ M₁′⇛*N′ , N⇛*N′ ⟩ ⟩ =
              ⟨ N′ , ⟨ M₁′⇛*N′ , (M₂ ⇛⟨ M₂⇛N ⟩ N⇛*N′) ⟩ ⟩
```

The step case may be illustrated as follows:

            L
           / \
          1   *
         /     \
        M₁ (a)  M₂
       / \     /
      *   *   1
     /     \ /
    M₁′(b)  N
     \     /
      *   *
       \ /
        N′

where downward lines are instances of `⇛` or `⇛*`, depending on how
they are marked. Here `(a)` holds by `strip` and `(b)` holds by
induction.


## Proof of confluence for reduction

Confluence of reduction is a corollary of confluence for parallel
reduction. From
`L —↠ M₁` and `L —↠ M₂` we have
`L ⇛* M₁` and `L ⇛* M₂` by `betas-pars`.
Then by confluence we obtain some `L` such that
`M₁ ⇛* N` and `M₂ ⇛* N`, from which we conclude that
`M₁ —↠ N` and `M₂ —↠ N` by `pars-betas`.

```
confluence : ∀{Γ A} {L M₁ M₂ : Γ ⊢ A}
  → L —↠ M₁
  → L —↠ M₂
    -----------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (M₁ —↠ N) × (M₂ —↠ N)
confluence L↠M₁ L↠M₂
    with par-confluence (betas-pars L↠M₁) (betas-pars L↠M₂)
...    | ⟨ N , ⟨ M₁⇛N , M₂⇛N ⟩ ⟩ =
         ⟨ N , ⟨ pars-betas M₁⇛N , pars-betas M₂⇛N ⟩ ⟩
```


## Notes

Broadly speaking, this proof of confluence, based on parallel
reduction, is due to W. Tait and P. Martin-Lof (see Barendredgt 1984,
Section 3.2).  Details of the mechanization come from several sources.
The `subst-par` lemma is the "strong substitutivity" lemma of Shafer,
Tebbi, and Smolka (ITP 2015). The proofs of `par-diamond`, `strip`,
and `par-confluence` are based on Pfenning's 1992 technical report
about the Church-Rosser theorem. In addition, we consulted Nipkow and
Berghofer's mechanization in Isabelle, which is based on an earlier
article by Nipkow (JAR 1996).  We opted not to use the "complete
developments" approach of Takahashi (1995) because we felt that the
proof was simple enough based solely on parallel reduction.  There are
many more mechanizations of the Church-Rosser theorem that we have not
yet had the time to read, including Shankar's (J. ACM 1988) and
Homeier's (TPHOLs 2001).

## Unicode

This chapter uses the following unicode:

    ⇛  U+3015  RIGHTWARDS TRIPLE ARROW (\r== or \Rrightarrow)
