---
title     : "Soundness: Soundness of reduction with respect to denotational semantics"
layout    : page
prev      : /Compositional/
permalink : /Soundness/
next      : /Adequacy/
---

```
module plfa.part3.Soundness where
```


## Introduction

In this chapter we prove that the reduction semantics is sound with
respect to the denotational semantics, i.e., for any term L

    L —↠ ƛ N  implies  ℰ L ≃ ℰ (ƛ N)

The proof is by induction on the reduction sequence, so the main lemma
concerns a single reduction step. We prove that if any term `M` steps
to a term `N`, then `M` and `N` are denotationally equal. We shall
prove each direction of this if-and-only-if separately. One direction
will look just like a type preservation proof. The other direction is
like proving type preservation for reduction going in reverse.  Recall
that type preservation is sometimes called subject
reduction. Preservation in reverse is a well-known property and is
called _subject expansion_. It is also well-known that subject
expansion is false for most typed lambda calculi!


## Imports

```
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Agda.Primitive using (lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)
open import plfa.part2.Untyped
     using (Context; _,_; _∋_; _⊢_; ★; Z; S_; `_; ƛ_; _·_;
            subst; _[_]; subst-zero; ext; rename; exts;
            _—→_; ξ₁; ξ₂; β; ζ; _—↠_; _—→⟨_⟩_; _∎)
open import plfa.part2.Substitution using (Rename; Subst; ids)
open import plfa.part3.Denotational
     using (Value; ⊥; Env; _⊢_↓_; _`,_; _⊑_; _`⊑_; `⊥; _`⊔_; init; last; init-last;
            ⊑-refl; ⊑-trans; `⊑-refl; ⊑-env; ⊑-env-conj-R1; ⊑-env-conj-R2; up-env;
            var; ↦-elim; ↦-intro; ⊥-intro; ⊔-intro; sub;
            rename-pres; ℰ; _≃_; ≃-trans)
open import plfa.part3.Compositional using (lambda-inversion; var-inv)
```

## Forward reduction preserves denotations

The proof of preservation in this section mixes techniques from
previous chapters. Like the proof of preservation for the STLC, we are
preserving a relation defined separately from the syntax, in contrast
to the intrinsically-typed terms. On the other hand, we are using de
Bruijn indices for variables.

The outline of the proof remains the same in that we must prove lemmas
concerning all of the auxiliary functions used in the reduction
relation: substitution, renaming, and extension.


### Simultaneous substitution preserves denotations

Our next goal is to prove that simultaneous substitution preserves
meaning.  That is, if `M` results in `v` in environment `γ`, then applying a
substitution `σ` to `M` gives us a program that also results in `v`, but in
an environment `δ` in which, for every variable `x`, `σ x` results in the
same value as the one for `x` in the original environment `γ`.
We write `δ ⊢ σ ↓ γ` for this condition.

```
infix 3 _`⊢_↓_
_`⊢_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
_`⊢_↓_ {Δ}{Γ} δ σ γ = (∀ (x : Γ ∋ ★) → δ ⊢ σ x ↓ γ x)
```

As usual, to prepare for lambda abstraction, we prove an extension
lemma. It says that applying the `exts` function to a substitution
produces a new substitution that maps variables to terms that when
evaluated in `δ , v` produce the values in `γ , v`.

```
subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (σ : Subst Γ Δ)
  → δ `⊢ σ ↓ γ
   --------------------------
  → δ `, v `⊢ exts σ ↓ γ `, v
subst-ext σ d Z = var
subst-ext σ d (S x′) = rename-pres S_ (λ _ → ⊑-refl) (d x′)
```

The proof is by cases on the de Bruijn index `x`.

* If it is `Z`, then we need to show that `δ , v ⊢ # 0 ↓ v`,
  which we have by rule `var`.

* If it is `S x′`,then we need to show that
  `δ , v ⊢ rename S_ (σ x′) ↓ γ x′`,
  which we obtain by the `rename-pres` lemma.

With the extension lemma in hand, the proof that simultaneous
substitution preserves meaning is straightforward.  Let's dive in!

```
subst-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ ★}
  → (σ : Subst Γ Δ)
  → δ `⊢ σ ↓ γ
  → γ ⊢ M ↓ v
    ------------------
  → δ ⊢ subst σ M ↓ v
subst-pres σ s (var {x = x}) = (s x)
subst-pres σ s (↦-elim d₁ d₂) =
  ↦-elim (subst-pres σ s d₁) (subst-pres σ s d₂)
subst-pres σ s (↦-intro d) =
  ↦-intro (subst-pres (λ {A} → exts σ) (subst-ext σ s) d)
subst-pres σ s ⊥-intro = ⊥-intro
subst-pres σ s (⊔-intro d₁ d₂) =
  ⊔-intro (subst-pres σ s d₁) (subst-pres σ s d₂)
subst-pres σ s (sub d lt) = sub (subst-pres σ s d) lt
```

The proof is by induction on the semantics of `M`.  The two interesting
cases are for variables and lambda abstractions.

* For a variable `x`, we have that `v ⊑ γ x` and we need to show that
  `δ ⊢ σ x ↓ v`.  From the premise applied to `x`, we have that
  `δ ⊢ σ x ↓ γ x`, so we conclude by the `sub` rule.

* For a lambda abstraction, we must extend the substitution
  for the induction hypothesis. We apply the `subst-ext` lemma
  to show that the extended substitution maps variables to
  terms that result in the appropriate values.


### Single substitution preserves denotations

For β reduction, `(ƛ N) · M —→ N [ M ]`, we need to show that the
semantics is preserved when substituting `M` for de Bruijn index 0 in
term `N`. By inversion on the rules `↦-elim` and `↦-intro`,
we have that `γ , v ⊢ M ↓ w` and `γ ⊢ N ↓ v`.
So we need to show that `γ ⊢ M [ N ] ↓ w`, or equivalently,
that `γ ⊢ subst (subst-zero N) M ↓ w`.

```
substitution : ∀ {Γ} {γ : Env Γ} {N M v w}
   → γ `, v ⊢ N ↓ w
   → γ ⊢ M ↓ v
     ---------------
   → γ ⊢ N [ M ] ↓ w
substitution{Γ}{γ}{N}{M}{v}{w} dn dm =
  subst-pres (subst-zero M) sub-z-ok dn
  where
  sub-z-ok : γ `⊢ subst-zero M ↓ (γ `, v)
  sub-z-ok Z = dm
  sub-z-ok (S x) = var
```

This result is a corollary of the lemma for simultaneous substitution.
To use the lemma, we just need to show that `subst-zero M` maps
variables to terms that produces the same values as those in `γ , v`.
Let `y` be an arbitrary variable (de Bruijn index).

* If it is `Z`, then `(subst-zero M) y = M` and `(γ , v) y = v`.
  By the premise we conclude that `γ ⊢ M ↓ v`.

* If it is `S x`, then `(subst-zero M) (S x) = x` and
  `(γ , v) (S x) = γ x`.  So we conclude that
  `γ ⊢ x ↓ γ x` by rule `var`.


### Reduction preserves denotations

With the substitution lemma in hand, it is straightforward to prove
that reduction preserves denotations.

```
preserve : ∀ {Γ} {γ : Env Γ} {M N v}
  → γ ⊢ M ↓ v
  → M —→ N
    ----------
  → γ ⊢ N ↓ v
preserve (var) ()
preserve (↦-elim d₁ d₂) (ξ₁ r) = ↦-elim (preserve d₁ r) d₂
preserve (↦-elim d₁ d₂) (ξ₂ r) = ↦-elim d₁ (preserve d₂ r)
preserve (↦-elim d₁ d₂) β = substitution (lambda-inversion d₁) d₂
preserve (↦-intro d) (ζ r) = ↦-intro (preserve d r)
preserve ⊥-intro r = ⊥-intro
preserve (⊔-intro d d₁) r = ⊔-intro (preserve d r) (preserve d₁ r)
preserve (sub d lt) r = sub (preserve d r) lt
```

We proceed by induction on the semantics of `M` with case analysis on
the reduction.

* If `M` is a variable, then there is no such reduction.

* If `M` is an application, then the reduction is either a congruence
  (ξ₁ or ξ₂) or β. For each congruence, we use the induction
  hypothesis. For β reduction we use the substitution lemma and the
  `sub` rule.

* The rest of the cases are straightforward.

## Reduction reflects denotations

This section proves that reduction reflects the denotation of a
term. That is, if `N` results in `v`, and if `M` reduces to `N`, then
`M` also results in `v`. While there are some broad similarities
between this proof and the above proof of semantic preservation, we
shall require a few more technical lemmas to obtain this result.

The main challenge is dealing with the substitution in β reduction:

    (ƛ N) · M —→ N [ M ]

We have that `γ ⊢ N [ M ] ↓ v` and need to show that
`γ ⊢ (ƛ N) · M ↓ v`. Now consider the derivation of `γ ⊢ N [ M ] ↓ v`.
The term `M` may occur 0, 1, or many times inside `N [ M ]`. At each of
those occurrences, `M` may result in a different value. But to build a
derivation for `(ƛ N) · M`, we need a single value for `M`.  If `M`
occurred more than 1 time, then we can join all of the different values
using `⊔`. If `M` occurred 0 times, then we do not need any information
about `M` and can therefore use `⊥` for the value of `M`.


### Renaming reflects meaning

Previously we showed that renaming variables preserves meaning.  Now
we prove the opposite, that it reflects meaning. That is,
if `δ ⊢ rename ρ M ↓ v`, then `γ ⊢ M ↓ v`, where `(δ ∘ ρ) `⊑ γ`.

First, we need a variant of a lemma given earlier.
```
ext-⊑′ : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (ρ : Rename Γ Δ)
  → (δ ∘ ρ) `⊑ γ
    ------------------------------
  → ((δ `, v) ∘ ext ρ) `⊑ (γ `, v)
ext-⊑′ ρ lt Z = ⊑-refl
ext-⊑′ ρ lt (S x) = lt x
```

The proof is then as follows.
```
rename-reflect : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} { M : Γ ⊢ ★}
  → {ρ : Rename Γ Δ}
  → (δ ∘ ρ) `⊑ γ
  → δ ⊢ rename ρ M ↓ v
    ------------------------------------
  → γ ⊢ M ↓ v
rename-reflect {M = ` x} all-n d with var-inv d
... | lt =  sub var (⊑-trans lt (all-n x))
rename-reflect {M = ƛ N}{ρ = ρ} all-n (↦-intro d) =
   ↦-intro (rename-reflect (ext-⊑′ ρ all-n) d)
rename-reflect {M = ƛ N} all-n ⊥-intro = ⊥-intro
rename-reflect {M = ƛ N} all-n (⊔-intro d₁ d₂) =
   ⊔-intro (rename-reflect all-n d₁) (rename-reflect all-n d₂)
rename-reflect {M = ƛ N} all-n (sub d₁ lt) =
   sub (rename-reflect all-n d₁) lt
rename-reflect {M = L · M} all-n (↦-elim d₁ d₂) =
   ↦-elim (rename-reflect all-n d₁) (rename-reflect all-n d₂)
rename-reflect {M = L · M} all-n ⊥-intro = ⊥-intro
rename-reflect {M = L · M} all-n (⊔-intro d₁ d₂) =
   ⊔-intro (rename-reflect all-n d₁) (rename-reflect all-n d₂)
rename-reflect {M = L · M} all-n (sub d₁ lt) =
   sub (rename-reflect all-n d₁) lt
```

We cannot prove this lemma by induction on the derivation of
`δ ⊢ rename ρ M ↓ v`, so instead we proceed by induction on `M`.

* If it is a variable, we apply the inversion lemma to obtain
  that `v ⊑ δ (ρ x)`. Instantiating the premise to `x` we have
  `δ (ρ x) = γ x`, so we conclude by the `var` rule.

* If it is a lambda abstraction `ƛ N`, we have
  rename `ρ (ƛ N) = ƛ (rename (ext ρ) N)`.
  We proceed by cases on `δ ⊢ ƛ (rename (ext ρ) N) ↓ v`.

  * Rule `↦-intro`: To satisfy the premise of the induction
    hypothesis, we prove that the renaming can be extended to be a
    mapping from `γ , v₁ to δ , v₁`.

  * Rule `⊥-intro`: We simply apply `⊥-intro`.

  * Rule `⊔-intro`: We apply the induction hypotheses and `⊔-intro`.

  * Rule `sub`: We apply the induction hypothesis and `sub`.

* If it is an application `L · M`, we have
  `rename ρ (L · M) = (rename ρ L) · (rename ρ M)`.
  We proceed by cases on `δ ⊢ (rename ρ L) · (rename ρ M) ↓ v`
  and all the cases are straightforward.

In the upcoming uses of `rename-reflect`, the renaming will always be
the increment function. So we prove a corollary for that special case.

```
rename-inc-reflect : ∀ {Γ v′ v} {γ : Env Γ} { M : Γ ⊢ ★}
  → (γ `, v′) ⊢ rename S_ M ↓ v
    ----------------------------
  → γ ⊢ M ↓ v
rename-inc-reflect d = rename-reflect `⊑-refl d
```


### Substitution reflects denotations, the variable case

We are almost ready to begin proving that simultaneous substitution
reflects denotations. That is, if `γ ⊢ (subst σ M) ↓ v`, then
`γ ⊢ σ k ↓ δ k` and `δ ⊢ M ↓ v` for any `k` and some `δ`.
We shall start with the case in which `M` is a variable `x`.
So instead the premise is `γ ⊢ σ x ↓ v` and we need to show that
`δ ⊢ x ↓ v` for some `δ`. The `δ` that we choose shall be the
environment that maps `x` to `v` and every other variable to `⊥`.

Next we define the environment that maps `x` to `v` and every other
variable to `⊥`, that is `const-env x v`. To tell variables apart, we
define the following function for deciding equality of variables.

```
_var≟_ : ∀ {Γ} → (x y : Γ ∋ ★) → Dec (x ≡ y)
Z var≟ Z  =  yes refl
Z var≟ (S _)  =  no λ()
(S _) var≟ Z  =  no λ()
(S x) var≟ (S y) with  x var≟ y
...                 |  yes refl =  yes refl
...                 |  no neq   =  no λ{refl → neq refl}

var≟-refl : ∀ {Γ} (x : Γ ∋ ★) → (x var≟ x) ≡ yes refl
var≟-refl Z = refl
var≟-refl (S x) rewrite var≟-refl x = refl
```

Now we use `var≟` to define `const-env`.

```
const-env : ∀{Γ} → (x : Γ ∋ ★) → Value → Env Γ
const-env x v y with x var≟ y
...             | yes _       = v
...             | no _        = ⊥
```

Of course, `const-env x v` maps `x` to value `v`

```
same-const-env : ∀{Γ} {x : Γ ∋ ★} {v} → (const-env x v) x ≡ v
same-const-env {x = x} rewrite var≟-refl x = refl
```

and `const-env x v` maps `y` to `⊥, so long as `x ≢ y`.

```
diff-const-env : ∀{Γ} {x y : Γ ∋ ★} {v}
  → x ≢ y
    -------------------
  → const-env x v y ≡ ⊥
diff-const-env {Γ} {x} {y} neq with x var≟ y
...  | yes eq  =  ⊥-elim (neq eq)
...  | no _    =  refl
```

So we choose `const-env x v` for `δ` and obtain `δ ⊢ x ↓ v`
with the `var` rule.

It remains to prove that `γ ⊢ σ ↓ δ` and `δ ⊢ M ↓ v` for any `k`, given that
we have chosen `const-env x v` for `δ`.  We shall have two cases to
consider, `x ≡ y` or `x ≢ y`.

Now to finish the two cases of the proof.

* In the case where `x ≡ y`, we need to show
  that `γ ⊢ σ y ↓ v`, but that's just our premise.
* In the case where `x ≢ y,` we need to show
  that `γ ⊢ σ y ↓ ⊥`, which we do via rule `⊥-intro`.

Thus, we have completed the variable case of the proof that
simultaneous substitution reflects denotations.  Here is the proof
again, formally.

```
subst-reflect-var : ∀ {Γ Δ} {γ : Env Δ} {x : Γ ∋ ★} {v} {σ : Subst Γ Δ}
  → γ ⊢ σ x ↓ v
    -----------------------------------------
  → Σ[ δ ∈ Env Γ ] γ `⊢ σ ↓ δ  ×  δ ⊢ ` x ↓ v
subst-reflect-var {Γ}{Δ}{γ}{x}{v}{σ} xv
  rewrite sym (same-const-env {Γ}{x}{v}) =
    ⟨ const-env x v , ⟨ const-env-ok , var ⟩ ⟩
  where
  const-env-ok : γ `⊢ σ ↓ const-env x v
  const-env-ok y with x var≟ y
  ... | yes x≡y rewrite sym x≡y | same-const-env {Γ}{x}{v} = xv
  ... | no x≢y rewrite diff-const-env {Γ}{x}{y}{v} x≢y = ⊥-intro
```


### Substitutions and environment construction

Every substitution produces terms that can evaluate to `⊥`.

```
subst-⊥ : ∀{Γ Δ}{γ : Env Δ}{σ : Subst Γ Δ}
    -----------------
  → γ `⊢ σ ↓ `⊥
subst-⊥ x = ⊥-intro
```

If a substitution produces terms that evaluate to the values in
both `γ₁` and `γ₂`, then those terms also evaluate to the values in
`γ₁ ⊔ γ₂`.

```
subst-⊔ : ∀{Γ Δ}{γ : Env Δ}{γ₁ γ₂ : Env Γ}{σ : Subst Γ Δ}
           → γ `⊢ σ ↓ γ₁
           → γ `⊢ σ ↓ γ₂
             -------------------------
           → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
subst-⊔ γ₁-ok γ₂-ok x = ⊔-intro (γ₁-ok x) (γ₂-ok x)
```

### The Lambda constructor is injective

```
lambda-inj : ∀ {Γ} {M N : Γ , ★ ⊢ ★ }
  → _≡_ {A = Γ ⊢ ★} (ƛ M) (ƛ N)
    ---------------------------
  → M ≡ N
lambda-inj refl = refl
```

### Simultaneous substitution reflects denotations

In this section we prove a central lemma, that
substitution reflects denotations. That is, if `γ ⊢ subst σ M ↓ v`, then
`δ ⊢ M ↓ v` and `γ ⊢ σ ↓ δ` for some `δ`. We shall proceed by induction on
the derivation of `γ ⊢ subst σ M ↓ v`. This requires a minor
restatement of the lemma, changing the premise to `γ ⊢ L ↓ v` and
`L ≡ subst σ M`.

```
split : ∀ {Γ} {M : Γ , ★ ⊢ ★} {δ : Env (Γ , ★)} {v}
  → δ ⊢ M ↓ v
    --------------------------
  → (init δ `, last δ) ⊢ M ↓ v
split {δ = δ} δMv rewrite init-last δ = δMv

subst-reflect : ∀ {Γ Δ} {δ : Env Δ} {M : Γ ⊢ ★} {v} {L : Δ ⊢ ★} {σ : Subst Γ Δ}
  → δ ⊢ L ↓ v
  → subst σ M ≡ L
    ---------------------------------------
  → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  γ ⊢ M ↓ v

subst-reflect {M = M}{σ = σ} (var {x = y}) eqL with M
... | ` x  with var {x = y}
...           | yv  rewrite sym eqL = subst-reflect-var {σ = σ} yv
subst-reflect {M = M} (var {x = y}) () | M₁ · M₂
subst-reflect {M = M} (var {x = y}) () | ƛ M′

subst-reflect {M = M}{σ = σ} (↦-elim d₁ d₂) eqL
         with M
...    | ` x with ↦-elim d₁ d₂
...    | d′ rewrite sym eqL = subst-reflect-var {σ = σ} d′
subst-reflect (↦-elim d₁ d₂) () | ƛ M′
subst-reflect{Γ}{Δ}{γ}{σ = σ} (↦-elim d₁ d₂)
   refl | M₁ · M₂
     with subst-reflect {M = M₁} d₁ refl | subst-reflect {M = M₂} d₂ refl
...     | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
     ⟨ δ₁ `⊔ δ₂ , ⟨ subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂ ,
                    ↦-elim (⊑-env m1 (⊑-env-conj-R1 δ₁ δ₂))
                           (⊑-env m2 (⊑-env-conj-R2 δ₁ δ₂)) ⟩ ⟩

subst-reflect {M = M}{σ = σ} (↦-intro d) eqL with M
...    | ` x with (↦-intro d)
...             | d′ rewrite sym eqL = subst-reflect-var {σ = σ} d′
subst-reflect {σ = σ} (↦-intro d) eq | ƛ M′
      with subst-reflect {σ = exts σ} d (lambda-inj eq)
... | ⟨ δ′ , ⟨ exts-σ-δ′ , m′ ⟩ ⟩ =
    ⟨ init δ′ , ⟨ ((λ x → rename-inc-reflect (exts-σ-δ′ (S x)))) ,
             ↦-intro (up-env (split m′) (var-inv (exts-σ-δ′ Z))) ⟩ ⟩
subst-reflect (↦-intro d) () | M₁ · M₂

subst-reflect {σ = σ} ⊥-intro eq =
    ⟨ `⊥ , ⟨ subst-⊥ {σ = σ} , ⊥-intro ⟩ ⟩

subst-reflect {σ = σ} (⊔-intro d₁ d₂) eq
  with subst-reflect {σ = σ} d₁ eq | subst-reflect {σ = σ} d₂ eq
... | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
     ⟨ δ₁ `⊔ δ₂ , ⟨ subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂ ,
                    ⊔-intro (⊑-env m1 (⊑-env-conj-R1 δ₁ δ₂))
                            (⊑-env m2 (⊑-env-conj-R2 δ₁ δ₂)) ⟩ ⟩
subst-reflect (sub d lt) eq
    with subst-reflect d eq
... | ⟨ δ , ⟨ subst-δ , m ⟩ ⟩ = ⟨ δ , ⟨ subst-δ , sub m lt ⟩ ⟩
```

* Case `var`: We have subst `σ M ≡ y`, so `M` must also be a variable, say `x`.
  We apply the lemma `subst-reflect-var` to conclude.

* Case `↦-elim`: We have `subst σ M ≡ L₁ · L₂`. We proceed by cases on `M`.
  * Case `M ≡ x`: We apply the `subst-reflect-var` lemma again to conclude.

  * Case `M ≡ M₁ · M₂`: By the induction hypothesis, we have
    some `δ₁` and `δ₂` such that `δ₁ ⊢ M₁ ↓ v₁ ↦ v₃` and `γ ⊢ σ ↓ δ₁`,
    as well as `δ₂ ⊢ M₂ ↓ v₁` and `γ ⊢ σ ↓ δ₂`.
    By `⊑-env` we have `δ₁ ⊔ δ₂ ⊢ M₁ ↓ v₁ ↦ v₃` and `δ₁ ⊔ δ₂ ⊢ M₂ ↓ v₁`
    (using `⊑-env-conj-R1` and `⊑-env-conj-R2`), and therefore
    `δ₁ ⊔ δ₂ ⊢ M₁ · M₂ ↓ v₃`.
    We conclude this case by obtaining `γ ⊢ σ ↓ δ₁ ⊔ δ₂`
    by the `subst-⊔` lemma.

* Case `↦-intro`: We have `subst σ M ≡ ƛ L′`. We proceed by cases on `M`.
  * Case `M ≡ x`: We apply the `subst-reflect-var` lemma.

  * Case `M ≡ ƛ M′`: By the induction hypothesis, we have
    `(δ′ , v′) ⊢ M′ ↓ v₂` and `(δ , v₁) ⊢ exts σ ↓ (δ′ , v′)`.
    From the later we have `(δ , v₁) ⊢ # 0 ↓ v′`.
    By the lemma `var-inv` we have `v′ ⊑ v₁`, so by the `up-env` lemma we
    have `(δ′ , v₁) ⊢ M′ ↓ v₂` and therefore `δ′ ⊢ ƛ M′ ↓ v₁ → v₂`.  We
    also need to show that `δ `⊢ σ ↓ δ′`.  Fix `k`. We have
    `(δ , v₁) ⊢ rename S_ σ k ↓ δ k′`.  We then apply the lemma
    `rename-inc-reflect` to obtain `δ ⊢ σ k ↓ δ k′`, so this case is
    complete.

* Case `⊥-intro`: We choose `⊥` for `δ`.
  We have `⊥ ⊢ M ↓ ⊥` by `⊥-intro`.
  We have `δ ⊢ σ ↓ ⊥` by the lemma `subst-empty`.

* Case `⊔-intro`: By the induction hypothesis we have
  `δ₁ ⊢ M ↓ v₁`, `δ₂ ⊢ M ↓ v₂`, `δ ⊢ σ ↓ δ₁`, and `δ ⊢ σ ↓ δ₂`.
  We have `δ₁ ⊔ δ₂ ⊢ M ↓ v₁` and `δ₁ ⊔ δ₂ ⊢ M ↓ v₂`
  by `⊑-env` with `⊑-env-conj-R1` and `⊑-env-conj-R2`.
  So by `⊔-intro` we have `δ₁ ⊔ δ₂ ⊢ M ↓ v₁ ⊔ v₂`.
  By `subst-⊔` we conclude that `δ ⊢ σ ↓ δ₁ ⊔ δ₂`.


### Single substitution reflects denotations

Most of the work is now behind us. We have proved that simultaneous
substitution reflects denotations. Of course, β reduction uses single
substitution, so we need a corollary that proves that single
substitution reflects denotations. That is,
given terms `N : (Γ , ★ ⊢ ★)` and `M : (Γ ⊢ ★)`,
if `γ ⊢ N [ M ] ↓ w`, then `γ ⊢ M ↓ v` and `(γ , v) ⊢ N ↓ w`
for some value `v`. We have `N [ M ] = subst (subst-zero M) N`.

We first prove a lemma about `subst-zero`, that if
`δ ⊢ subst-zero M ↓ γ`, then
`γ ⊑ (δ , w) × δ ⊢ M ↓ w` for some `w`.

```
subst-zero-reflect : ∀ {Δ} {δ : Env Δ} {γ : Env (Δ , ★)} {M : Δ ⊢ ★}
  → δ `⊢ subst-zero M ↓ γ
    ----------------------------------------
  → Σ[ w ∈ Value ] γ `⊑ (δ `, w) × δ ⊢ M ↓ w
subst-zero-reflect {δ = δ} {γ = γ} δσγ = ⟨ last γ , ⟨ lemma , δσγ Z ⟩ ⟩
  where
  lemma : γ `⊑ (δ `, last γ)
  lemma Z  =  ⊑-refl
  lemma (S x) = var-inv (δσγ (S x))
```

We choose `w` to be the last value in `γ` and we obtain `δ ⊢ M ↓ w`
by applying the premise to variable `Z`. Finally, to prove
`γ ⊑ (δ , w)`, we prove a lemma by induction in the input variable.
The base case is trivial because of our choice of `w`.
In the induction case, `S x`, the premise
`δ ⊢ subst-zero M ↓ γ` gives us `δ ⊢ x ↓ γ (S x)` and then
using `var-inv` we conclude that `γ (S x) ⊑ (δ `, w) (S x)`.

Now to prove that substitution reflects denotations.

```
substitution-reflect : ∀ {Δ} {δ : Env Δ} {N : Δ , ★ ⊢ ★} {M : Δ ⊢ ★} {v}
  → δ ⊢ N [ M ] ↓ v
    ------------------------------------------------
  → Σ[ w ∈ Value ] δ ⊢ M ↓ w  ×  (δ `, w) ⊢ N ↓ v
substitution-reflect d with subst-reflect d refl
...  | ⟨ γ , ⟨ δσγ , γNv ⟩ ⟩ with subst-zero-reflect δσγ
...    | ⟨ w , ⟨ ineq , δMw ⟩ ⟩ = ⟨ w , ⟨ δMw , ⊑-env γNv ineq ⟩ ⟩
```

We apply the `subst-reflect` lemma to obtain
`δ ⊢ subst-zero M ↓ γ` and `γ ⊢ N ↓ v` for some `γ`.
Using the former, the `subst-zero-reflect` lemma gives
us `γ ⊑ (δ , w)` and `δ ⊢ M ↓ w`. We conclude that
`δ , w ⊢ N ↓ v` by applying the `⊑-env` lemma, using
`γ ⊢ N ↓ v` and `γ ⊑ (δ , w)`.


### Reduction reflects denotations

Now that we have proved that substitution reflects denotations, we can
easily prove that reduction does too.

```
reflect-beta : ∀{Γ}{γ : Env Γ}{M N}{v}
    → γ ⊢ (N [ M ]) ↓ v
    → γ ⊢ (ƛ N) · M ↓ v
reflect-beta d
    with substitution-reflect d
... | ⟨ v₂′ , ⟨ d₁′ , d₂′ ⟩ ⟩ = ↦-elim (↦-intro d₂′) d₁′


reflect : ∀ {Γ} {γ : Env Γ} {M M′ N v}
  → γ ⊢ N ↓ v  →  M —→ M′  →   M′ ≡ N
    ---------------------------------
  → γ ⊢ M ↓ v
reflect var (ξ₁ r) ()
reflect var (ξ₂ r) ()
reflect{γ = γ} (var{x = x}) β mn
    with var{γ = γ}{x = x}
... | d′ rewrite sym mn = reflect-beta d′
reflect var (ζ r) ()
reflect (↦-elim d₁ d₂) (ξ₁ r) refl = ↦-elim (reflect d₁ r refl) d₂
reflect (↦-elim d₁ d₂) (ξ₂ r) refl = ↦-elim d₁ (reflect d₂ r refl)
reflect (↦-elim d₁ d₂) β mn
    with ↦-elim d₁ d₂
... | d′ rewrite sym mn = reflect-beta d′
reflect (↦-elim d₁ d₂) (ζ r) ()
reflect (↦-intro d) (ξ₁ r) ()
reflect (↦-intro d) (ξ₂ r) ()
reflect (↦-intro d) β mn
    with ↦-intro d
... | d′ rewrite sym mn = reflect-beta d′
reflect (↦-intro d) (ζ r) refl = ↦-intro (reflect d r refl)
reflect ⊥-intro r mn = ⊥-intro
reflect (⊔-intro d₁ d₂) r mn rewrite sym mn =
   ⊔-intro (reflect d₁ r refl) (reflect d₂ r refl)
reflect (sub d lt) r mn = sub (reflect d r mn) lt
```

## Reduction implies denotational equality

We have proved that reduction both preserves and reflects
denotations. Thus, reduction implies denotational equality.

```
reduce-equal : ∀ {Γ} {M : Γ ⊢ ★} {N : Γ ⊢ ★}
  → M —→ N
    ---------
  → ℰ M ≃ ℰ N
reduce-equal {Γ}{M}{N} r γ v =
    ⟨ (λ m → preserve m r) , (λ n → reflect n r refl) ⟩
```

We conclude with the _soundness property_, that multi-step reduction
to a lambda abstraction implies denotational equivalence with a lambda
abstraction.

```
soundness : ∀{Γ} {M : Γ ⊢ ★} {N : Γ , ★ ⊢ ★}
  → M —↠ ƛ N
    -----------------
  → ℰ M ≃ ℰ (ƛ N)
soundness (.(ƛ _) ∎) γ v = ⟨ (λ x → x) , (λ x → x) ⟩
soundness {Γ} (L —→⟨ r ⟩ M—↠N) γ v =
   let ih = soundness M—↠N in
   let e = reduce-equal r in
   ≃-trans {Γ} e ih γ v
```


## Unicode

This chapter uses the following unicode:

    ≟  U+225F  QUESTIONED EQUAL TO (\?=)
