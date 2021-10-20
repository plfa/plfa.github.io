---
title     : "BigStep: Big-step semantics of untyped lambda calculus"
layout    : page
prev      : /Confluence/
permalink : /BigStep/
next      : /Denotational/
---

```
module plfa.part2.BigStep where
```

## Introduction

The call-by-name evaluation strategy is a deterministic method for
computing the value of a program in the lambda calculus.  That is,
call-by-name produces a value if and only if beta reduction can reduce
the program to a lambda abstraction. In this chapter we define
call-by-name evaluation and prove the forward direction of this
if-and-only-if. The backward direction is traditionally proved via
Curry-Feys standardisation, which is quite complex.  We give a sketch
of that proof, due to Plotkin, but postpone the proof in Agda until
after we have developed a denotational semantics for the lambda
calculus, at which point the proof is an easy corollary of properties
of the denotational semantics.

We present the call-by-name strategy as a relation between an input
term and an output value. Such a relation is often called a _big-step
semantics_, written `M ⇓ V`, as it relates the input term `M` directly
to the final result `V`, in contrast to the small-step reduction
relation, `M —→ M′`, that maps `M` to another term `M′` in which a
single sub-computation has been completed.

## Imports

```
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong-app)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import plfa.part2.Untyped
  using (Context; _⊢_; _∋_; ★; ∅; _,_; Z; S_; `_; #_; ƛ_; _·_;
  subst; subst-zero; exts; rename; β; ξ₁; ξ₂; ζ; _—→_; _—↠_; _—→⟨_⟩_; _∎;
  —↠-trans; appL-cong)
open import plfa.part2.Substitution using (Subst; ids)
```

## Environments

To handle variables and function applications, there is the choice
between using substitution, as in `—→`, or to use an _environment_.
An environment in call-by-name is a map from variables to closures,
that is, to terms paired with their environments. We choose to use
environments instead of substitution because the point of the
call-by-name strategy is to be closer to an implementation of the
language. Also, the denotational semantics introduced in later
chapters uses environments and the proof of adequacy
is made easier by aligning these choices.

We define environments and closures as follows.

```
ClosEnv : Context → Set

data Clos : Set where
  clos : ∀{Γ} → (M : Γ ⊢ ★) → ClosEnv Γ → Clos

ClosEnv Γ = ∀ (x : Γ ∋ ★) → Clos
```

As usual, we have the empty environment, and we can extend an
environment.

```
∅' : ClosEnv ∅
∅' ()

_,'_ : ∀ {Γ} → ClosEnv Γ → Clos → ClosEnv (Γ , ★)
(γ ,' c) Z = c
(γ ,' c) (S x) = γ x
```

## Big-step evaluation

The big-step semantics is represented as a ternary relation,
written `γ ⊢ M ⇓ V`, where `γ` is the environment, `M` is the input
term, and `V` is the result value.  A _value_ is a closure whose term
is a lambda abstraction.

```
data _⊢_⇓_ : ∀{Γ} → ClosEnv Γ → (Γ ⊢ ★) → Clos → Set where

  ⇓-var : ∀{Γ}{γ : ClosEnv Γ}{x : Γ ∋ ★}{Δ}{δ : ClosEnv Δ}{M : Δ ⊢ ★}{V}
    → γ x ≡ clos M δ
    → δ ⊢ M ⇓ V
      -----------
    → γ ⊢ ` x ⇓ V

  ⇓-lam : ∀{Γ}{γ : ClosEnv Γ}{M : Γ , ★ ⊢ ★}
    → γ ⊢ ƛ M ⇓ clos (ƛ M) γ

  ⇓-app : ∀{Γ}{γ : ClosEnv Γ}{L M : Γ ⊢ ★}{Δ}{δ : ClosEnv Δ}{N : Δ , ★ ⊢ ★}{V}
    → γ ⊢ L ⇓ clos (ƛ N) δ   →   (δ ,' clos M γ) ⊢ N ⇓ V
      ---------------------------------------------------
    → γ ⊢ L · M ⇓ V
```

* The `⇓-var` rule evaluates a variable by finding the associated
  closure in the environment and then evaluating the closure.

* The `⇓-lam` rule turns a lambda abstraction into a closure
  by packaging it up with its environment.

* The `⇓-app` rule performs function application by first evaluating
  the term `L` in operator position. If that produces a closure containing
  a lambda abstraction `ƛ N`, then we evaluate the body `N` in an
  environment extended with the argument `M`. Note that `M` is not
  evaluated in rule `⇓-app` because this is call-by-name and not
  call-by-value.


#### Exercise `big-step-eg` (practice)

Show that `(ƛ ƛ # 1) · ((ƛ # 0 · # 0) · (ƛ # 0 · # 0))`
terminates under big-step call-by-name evaluation.

```
-- Your code goes here
```


## The big-step semantics is deterministic

If the big-step relation evaluates a term `M` to both `V` and
`V′`, then `V` and `V′` must be identical. In other words, the
call-by-name relation is a partial function. The proof is a
straightforward induction on the two big-step derivations.

```
⇓-determ : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{V V' : Clos}
  → γ ⊢ M ⇓ V → γ ⊢ M ⇓ V'
  → V ≡ V'
⇓-determ (⇓-var eq1 mc) (⇓-var eq2 mc')
    with trans (sym eq1) eq2
... | refl = ⇓-determ mc mc'
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc mc₁) (⇓-app mc' mc'')
    with ⇓-determ mc mc'
... | refl = ⇓-determ mc₁ mc''
```


## Big-step evaluation implies beta reduction to a lambda

If big-step evaluation produces a value, then the input term can
reduce to a lambda abstraction by beta reduction:

      ∅' ⊢ M ⇓ clos (ƛ N′) δ
      -----------------------------
    → Σ[ N ∈ ∅ , ★ ⊢ ★ ] (M —↠ ƛ N)

The proof is by induction on the big-step derivation. As is often
necessary, one must generalize the statement to get the induction to
go through. In the case for `⇓-app` (function application), the
argument is added to the environment, so the environment becomes
non-empty. The corresponding β reduction substitutes the argument into
the body of the lambda abstraction.  So we generalize the lemma to
allow an arbitrary environment `γ` and we add a premise that relates
the environment `γ` to an equivalent substitution `σ`.

The case for `⇓-app` also requires that we strengthen the
conclusion. In the case for `⇓-app` we have `γ ⊢ L ⇓ clos (λ N) δ` and
the induction hypothesis gives us `L —↠ ƛ N′`, but we need to know
that `N` and `N′` are equivalent. In particular, that `N′ ≡ subst τ N`
where `τ` is the substitution that is equivalent to `δ`. Therefore we
expand the conclusion of the statement, stating that the results are
equivalent.

We make the two notions of equivalence precise by defining the
following two mutually-recursive predicates `V ≈ M` and `γ ≈ₑ σ`.

```
_≈_ : Clos → (∅ ⊢ ★) → Set
_≈ₑ_ : ∀{Γ} → ClosEnv Γ → Subst Γ ∅ → Set

(clos {Γ} M γ) ≈ N = Σ[ σ ∈ Subst Γ ∅ ] γ ≈ₑ σ × (N ≡ subst σ M)

γ ≈ₑ σ = ∀{x} → (γ x) ≈ (σ x)
```

We can now state the main lemma:

    If γ ⊢ M ⇓ V  and  γ ≈ₑ σ,
    then  subst σ M —↠ N  and  V ≈ N  for some N.

Before starting the proof, we establish a couple lemmas
about equivalent environments and substitutions.

The empty environment is equivalent to the identity substitution
`ids`, which we import from Chapter [Substitution](/Substitution/).

```
≈ₑ-id : ∅' ≈ₑ ids
≈ₑ-id {()}
```

Of course, applying the identity substitution to a term returns
the same term.

```
sub-id : ∀{Γ} {A} {M : Γ ⊢ A} → subst ids M ≡ M
sub-id = plfa.part2.Substitution.sub-id
```


We define an auxiliary function for extending a substitution.

```
ext-subst : ∀{Γ Δ} → Subst Γ Δ → Δ ⊢ ★ → Subst (Γ , ★) Δ
ext-subst{Γ}{Δ} σ N {A} = subst (subst-zero N) ∘ exts σ
```

The next lemma we need to prove states that if you start with an
equivalent environment and substitution `γ ≈ₑ σ`, extending them with
an equivalent closure and term `c ≈ N` produces an equivalent
environment and substitution: `(γ ,' V) ≈ₑ (ext-subst σ N)`,
or equivalently, `(γ ,' V) x ≈ (ext-subst σ N) x` for any
variable `x`. The proof will be by induction on `x` and
for the induction step we need the following lemma,
which states that applying the composition of `exts σ`
and `subst-zero` to `S x` is the same as just `σ x`,
which is a corollary of a theorem in
Chapter [Substitution](/Substitution/).

```
subst-zero-exts : ∀{Γ Δ}{σ : Subst Γ Δ}{B}{M : Δ ⊢ B}{x : Γ ∋ ★}
  → (subst (subst-zero M) ∘ exts σ) (S x) ≡ σ x
subst-zero-exts {Γ}{Δ}{σ}{B}{M}{x} =
   cong-app (plfa.part2.Substitution.subst-zero-exts-cons{σ = σ}) (S x)
```

So the proof of `≈ₑ-ext` is as follows.

```
≈ₑ-ext : ∀ {Γ} {γ : ClosEnv Γ} {σ : Subst Γ ∅} {V} {N : ∅ ⊢ ★}
  → γ ≈ₑ σ  →  V ≈ N
    --------------------------
  → (γ ,' V) ≈ₑ (ext-subst σ N)
≈ₑ-ext {Γ} {γ} {σ} {V} {N} γ≈ₑσ V≈N {Z} = V≈N
≈ₑ-ext {Γ} {γ} {σ} {V} {N} γ≈ₑσ V≈N {S x}
  rewrite subst-zero-exts {σ = σ}{M = N}{x} = γ≈ₑσ
```

We proceed by induction on the input variable.

* If it is `Z`, then we immediately conclude using the
  premise `V ≈ N`.

* If it is `S x`, then we rewrite using the
  `subst-zero-exts` lemma and use the premise `γ ≈ₑ σ`
  to conclude.


To prove the main lemma, we need another technical lemma about
substitution. Applying one substitution after another is the same as
composing the two substitutions and then applying them.

```
sub-sub : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ}
  → subst σ₂ (subst σ₁ M) ≡ subst (subst σ₂ ∘ σ₁) M
sub-sub {M = M} = plfa.part2.Substitution.sub-sub {M = M}
```

We arrive at the main lemma: if `M` big steps to a
closure `V` in environment `γ`, and if `γ ≈ₑ σ`, then `subst σ M` reduces
to some term `N` that is equivalent to `V`. We describe the proof
below.

```
⇓→—↠×≈ : ∀{Γ}{γ : ClosEnv Γ}{σ : Subst Γ ∅}{M : Γ ⊢ ★}{V : Clos}
       → γ ⊢ M ⇓ V  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ ∅ ⊢ ★ ] (subst σ M —↠ N) × V ≈ N
⇓→—↠×≈ {γ = γ} (⇓-var{x = x} γx≡Lδ δ⊢L⇓V) γ≈ₑσ
    with γ x | γ≈ₑσ {x} | γx≡Lδ
... | clos L δ | ⟨ τ , ⟨ δ≈ₑτ , σx≡τL ⟩ ⟩ | refl
      with ⇓→—↠×≈{σ = τ} δ⊢L⇓V δ≈ₑτ
...   | ⟨ N , ⟨ τL—↠N , V≈N ⟩ ⟩ rewrite σx≡τL =
        ⟨ N , ⟨ τL—↠N , V≈N ⟩ ⟩
⇓→—↠×≈ {σ = σ} {V = clos (ƛ N) γ} (⇓-lam) γ≈ₑσ =
    ⟨ subst σ (ƛ N) , ⟨ subst σ (ƛ N) ∎ , ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ ⟩ ⟩
⇓→—↠×≈{Γ}{γ} {σ = σ} {L · M} {V} (⇓-app {N = N} L⇓ƛNδ N⇓V) γ≈ₑσ
    with ⇓→—↠×≈{σ = σ} L⇓ƛNδ γ≈ₑσ
... | ⟨ _ , ⟨ σL—↠ƛτN , ⟨ τ , ⟨ δ≈ₑτ , ≡ƛτN ⟩ ⟩ ⟩ ⟩ rewrite ≡ƛτN
      with ⇓→—↠×≈ {σ = ext-subst τ (subst σ M)} N⇓V
             (λ {x} → ≈ₑ-ext{σ = τ} δ≈ₑτ ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ {x})
           | β{∅}{subst (exts τ) N}{subst σ M}
...   | ⟨ N' , ⟨ —↠N' , V≈N' ⟩ ⟩ | ƛτN·σM—→
        rewrite sub-sub{M = N}{σ₁ = exts τ}{σ₂ = subst-zero (subst σ M)} =
        let rs = (ƛ subst (exts τ) N) · subst σ M —→⟨ ƛτN·σM—→ ⟩ —↠N' in
        let g = —↠-trans (appL-cong σL—↠ƛτN) rs in
        ⟨ N' , ⟨ g , V≈N' ⟩ ⟩
```

The proof is by induction on `γ ⊢ M ⇓ V`. We have three cases
to consider.

* Case `⇓-var`.
  So we have `γ x ≡ clos L δ` and `δ ⊢ L ⇓ V`.
  We need to show that ``subst σ (` x) —↠ N`` and `V ≈ N` for some `N`.
  The premise `γ ≈ₑ σ` tells us that `γ x ≈ σ x`, so `clos L δ ≈ σ x`.
  By the definition of `≈`, there exists a `τ` such that
  `δ ≈ₑ τ` and `σ x ≡ subst τ L `.
  Using `δ ⊢ L ⇓ V` and `δ ≈ₑ τ`,
  the induction hypothesis gives us
  `subst τ L —↠ N` and `V ≈ N` for some `N`.
  So we have shown that `subst σ x —↠ N` and `V ≈ N` for some `N`.

* Case `⇓-lam`.
  We immediately have `subst σ (ƛ N) —↠ subst σ (ƛ N)`
  and `clos (subst σ (ƛ N)) γ ≈ subst σ (ƛ N)`.

* Case `⇓-app`.
  Using `γ ⊢ L ⇓ clos (ƛ N) δ` and `γ ≈ₑ σ`,
  the induction hypothesis gives us

        subst σ L —↠ ƛ subst (exts τ) N                                     (1)

  and `δ ≈ₑ τ` for some `τ`.
  From `γ≈ₑσ` we have `clos M γ ≈ subst σ M`.
  Then with `(δ ,' clos M γ) ⊢ N ⇓ V`,
  the induction hypothesis gives us `V ≈ N'` and

        subst (subst (subst-zero (subst σ M)) ∘ (exts τ)) N —↠ N'         (2)

  Meanwhile, by `β`, we have

        (ƛ subst (exts τ) N) · subst σ M
        —→ subst (subst-zero (subst σ M)) (subst (exts τ) N)

  which is the same as the following, by `sub-sub`.

        (ƛ subst (exts τ) N) · subst σ M
        —→ subst (subst (subst-zero (subst σ M)) ∘ exts τ) N              (3)

  Using (3) and (2) we have

        (ƛ subst (exts τ) N) · subst σ M —↠ N'                             (4)

  From (1) we have

        subst σ L · subst σ M —↠ (ƛ subst (exts τ) N) · subst σ M

  which we combine with (4) to conclude that

        subst σ L · subst σ M —↠ N'


With the main lemma complete, we establish the forward direction
of the equivalence between the big-step semantics and beta reduction.

```
cbn→reduce :  ∀{M : ∅ ⊢ ★}{Δ}{δ : ClosEnv Δ}{N′ : Δ , ★ ⊢ ★}
  → ∅' ⊢ M ⇓ clos (ƛ N′) δ
    -----------------------------
  → Σ[ N ∈ ∅ , ★ ⊢ ★ ] (M —↠ ƛ N)
cbn→reduce {M}{Δ}{δ}{N′} M⇓c
    with ⇓→—↠×≈{σ = ids} M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , ⟨ σ , ⟨ h , eq2 ⟩ ⟩ ⟩ ⟩ rewrite sub-id{M = M} | eq2 =
      ⟨ subst (exts σ) N′ , rs ⟩
```

#### Exercise `big-alt-implies-multi` (practice)

Formulate an alternative big-step semantics, of the form `M ↓ N`, for
call-by-name that uses substitution instead of environments.  That is,
the analogue of the application rule `⇓-app` should perform
substitution, as in `N [ M ]`, instead of extending the environment
with `M`. Prove that `M ↓ N` implies `M —↠ N`.

```
-- Your code goes here
```

## Beta reduction to a lambda implies big-step evaluation

The proof of the backward direction, that beta reduction to a lambda
implies that the call-by-name semantics produces a result, is more
difficult to prove. The difficulty stems from reduction proceeding
underneath lambda abstractions via the `ζ` rule. The call-by-name
semantics does not reduce under lambda, so a straightforward proof by
induction on the reduction sequence is impossible.  In the article
_Call-by-name, call-by-value, and the λ-calculus_, Plotkin proves the
theorem in two steps, using two auxiliary reduction relations. The
first step uses a classic technique called Curry-Feys standardisation.
It relies on the notion of _standard reduction sequence_, which acts
as a half-way point between full beta reduction and call-by-name by
expanding call-by-name to also include reduction underneath
lambda. Plotkin proves that `M` reduces to `L` if and only if `M` is
related to `L` by a standard reduction sequence.

    Theorem 1 (Standardisation)
    `M —↠ L` if and only if `M` goes to `L` via a standard reduction sequence.

Plotkin then introduces _left reduction_, a small-step version of
call-by-name and uses the above theorem to prove that beta reduction
and left reduction are equivalent in the following sense.

    Corollary 1
    `M —↠ ƛ N` if and only if `M` goes to `ƛ N′`, for some `N′`, by left reduction.

The second step of the proof connects left reduction to call-by-name
evaluation.

    Theorem 2
    `M` left reduces to `ƛ N` if and only if `⊢ M ⇓ ƛ N`.

(Plotkin's call-by-name evaluator uses substitution instead of
environments, which explains why the environment is omitted in `⊢ M ⇓
ƛ N` in the above theorem statement.)

Putting Corollary 1 and Theorem 2 together, Plotkin proves that
call-by-name evaluation is equivalent to beta reduction.

    Corollary 2
    `M —↠ ƛ N` if and only if `⊢ M ⇓ ƛ N′` for some `N′`.

Plotkin also proves an analogous result for the λᵥ calculus, relating
it to call-by-value evaluation. For a nice exposition of that proof,
we recommend Chapter 5 of _Semantics Engineering with PLT Redex_ by
Felleisen, Findler, and Flatt.

Instead of proving the backwards direction via standardisation, as
sketched above, we defer the proof until after we define a
denotational semantics for the lambda calculus, at which point the
proof of the backwards direction will fall out as a corollary to the
soundness and adequacy of the denotational semantics.


## Unicode

This chapter uses the following unicode:

    ≈  U+2248  ALMOST EQUAL TO (\~~ or \approx)
    ₑ  U+2091  LATIN SUBSCRIPT SMALL LETTER E (\_e)
    ⊢  U+22A2  RIGHT TACK (\|- or \vdash)
    ⇓  U+21DB  DOWNWARDS DOUBLE ARROW (\d= or \Downarrow)
