---
title     : "Call-by-name big-step evaluation"
layout    : page
prev      : /Confluence/
permalink : /CallByName/
next      : /Denotational/
---

\begin{code}
module plfa.CallByName where
\end{code}

## Introduction

The call-by-name evaluation strategy is a deterministic method for
computing the value of a program in the lambda calculus.  That is,
call-by-name produces a value if and only if beta reduction can reduce
the program to a lambda abstraction. In this chapter we define
call-by-name evaluation and prove the forward direction of this
if-and-only-if. We postpone the backward direction until after we have
developed a denotational semantics for the lambda calculus, at which
point the proof will be an easy corollary of properties of the
denotational semantics.

We present the call-by-name strategy as a relation between an an input
term and an output value. Such a relation is often called a _big-step
semantics_, as it relates the input term directly to the final result,
in contrast to the small-step reduction relation `—→` that maps a term
to another term in which a single sub-computation has been completed.

## Imports

\begin{code}
open import plfa.Untyped
  using (Context; _⊢_; _∋_; ★; ∅; _,_; Z; S_; `_; ƛ_; _·_; subst; subst-zero;
         exts; rename)
open import plfa.LambdaReduction
  using (β; ξ₁; ξ₂; ζ; _—→_; _—↠_; _—→⟨_⟩_; _[]; —↠-trans; appL-cong)
open import plfa.Substitution
  using (Subst; ⟪_⟫; _•_; _⨟_; ids; sub-id; sub-sub; subst-zero-exts-cons)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
\end{code}

## Environments

To handle variables and function application, there is the choice
between using substitution, as in `—→`, or to use an _environment_.
An environment in call-by-name is a map from variables to closures,
that is, to terms paired with their environments. We choose to use
environments instead of substitution because the point of the
call-by-name strategy is to be closer to an implementation of the
language. Also, the denotational semantics introduced in later
chapters uses environments and the proof of adequacy
is made easier by aligning these choices.

We define environments and closures as follows.

\begin{code}
ClosEnv : Context → Set

data Clos : Set where
  clos : ∀{Γ} → (M : Γ ⊢ ★) → ClosEnv Γ → Clos

ClosEnv Γ = ∀ (x : Γ ∋ ★) → Clos
\end{code}

As usual, we have the empty environment, and we can extend an
environment.

\begin{code}
∅' : ClosEnv ∅
∅' ()

_,'_ : ∀ {Γ} → ClosEnv Γ → Clos → ClosEnv (Γ , ★)
(γ ,' c) Z = c
(γ ,' c) (S x) = γ x
\end{code}

## Big-step evaluation

The big-step semantics is represented as a ternary relation,
written `γ ⊢ M ⇓ V`, where `γ` is the environment, `M` is the input
term, and `V` is the result value.  A _value_ is a closure whose term
is a lambda abstraction.

\begin{code}
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
\end{code}

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


## The big-step semantics is deterministic

If the big-step relation evaluates a term `M` to both `V` and
`V′`, then `V` and `V′` must be identical. In other words, the
call-by-name relation is a partial function. The proof is a
straightforward induction on the two big-step derivations.

\begin{code}
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
\end{code}


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
that `N` and `N′` are equivalent. In particular, that `N ≡ subst τ N′`
where `τ` is the substitution that is equivalent to `δ`. Therefore we
expand the conclusion of the statement, stating that the results are
equivalent.

We make the two notions of equivalence precise by defining the
following two mutually-recursive predicates `c ≈ M` and `γ ≈ₑ σ`.

\begin{code}
_≈_ : Clos → (∅ ⊢ ★) → Set
_≈ₑ_ : ∀{Γ} → ClosEnv Γ → Subst Γ ∅ → Set

(clos {Γ} M γ) ≈ N = Σ[ σ ∈ Subst Γ ∅ ] γ ≈ₑ σ × (N ≡ ⟪ σ ⟫ M)

γ ≈ₑ σ = ∀{x} → (γ x) ≈ (σ x)
\end{code}

We can now state the main lemma:

    If γ ⊢ M ⇓ c  and  γ ≈ₑ σ,
    then  ⟪ σ ⟫ M —↠ N  and  c ≈ N  for some N.

Before starting the proof, we establish a couple lemmas
about equivalent environments and substitutions.

The empty environment is equivalent to the identity substitution.

\begin{code}
≈ₑ-id : ∅' ≈ₑ ids
≈ₑ-id {()}
\end{code}

We define an auxilliary function for extending a substitution.

\begin{code}
ext-subst : ∀{Γ Δ} → Subst Γ Δ → Δ ⊢ ★ → Subst (Γ , ★) Δ
ext-subst{Γ}{Δ} σ N {A} = ⟪ subst-zero N ⟫ ∘ exts σ
\end{code}

The next lemma states that if you start with an equivalent
environment and substitution `γ ≈ₑ σ`, extending them with
an equivalent closure and term `c ≈ N` produces
an equivalent environment and substitution:
`(γ ,' c) ≈ₑ (ext-subst σ N)`. 

\begin{code}
≈ₑ-ext : ∀ {Γ} {γ : ClosEnv Γ} {σ : Subst Γ ∅} {c} {N : ∅ ⊢ ★}
      → γ ≈ₑ σ  →  c ≈ N
        --------------------------
      → (γ ,' c) ≈ₑ (ext-subst σ N)
≈ₑ-ext {Γ} {γ} {σ} {c} {N} γ≈ₑσ c≈N {x} = goal
   where
   ext-cons : (γ ,' c) ≈ₑ (N • σ)
   ext-cons {Z} = c≈N
   ext-cons {S x} = γ≈ₑσ

   goal : (γ ,' c) x ≈ ext-subst σ N x
   goal
       with ext-cons {x}
   ... | a rewrite sym (subst-zero-exts-cons{Γ}{∅}{σ}{★}{N}{★}) = a
\end{code}

To prove `≈ₑ-ext`, we make use of the fact that `ext-subst σ N` is
equivalent to `N • σ` (by `subst-zero-exts-cons`). So we just
need to prove that `(γ ,' c) ≈ₑ (N • σ)`, which is easy.
We proceed by cases on the input variable.

* If it is `Z`, then we immediately conclude using the
  premise `c ≈ N`.

* If it is `S x`, then we immediately conclude using
  premise `γ ≈ₑ σ`.


We arive at the main lemma: if `M` big steps to a
closure `c` in environment `γ`, and if `γ ≈ₑ σ`, then `⟪ σ ⟫ M` reduces
to some term `N` that is equivalent to `c`. We describe the proof
below.

\begin{code}
⇓→—↠×𝔹 : ∀{Γ}{γ : ClosEnv Γ}{σ : Subst Γ ∅}{M : Γ ⊢ ★}{c : Clos}
       → γ ⊢ M ⇓ c  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ ∅ ⊢ ★ ] (⟪ σ ⟫ M —↠ N) × c ≈ N
⇓→—↠×𝔹 {γ = γ} (⇓-var{x = x} γx≡Lδ δ⊢L⇓c) γ≈ₑσ
    with γ x | γ≈ₑσ {x} | γx≡Lδ
... | clos L δ | ⟨ τ , ⟨ δ≈ₑτ , σx≡τL ⟩ ⟩ | refl
    with ⇓→—↠×𝔹{σ = τ} δ⊢L⇓c δ≈ₑτ
... | ⟨ N , ⟨ τL—↠N , c≈N ⟩ ⟩ rewrite σx≡τL =
      ⟨ N , ⟨ τL—↠N , c≈N ⟩ ⟩
⇓→—↠×𝔹 {σ = σ} {c = clos (ƛ N) γ} ⇓-lam γ≈ₑσ =
    ⟨ ⟪ σ ⟫ (ƛ N) , ⟨ ⟪ σ ⟫ (ƛ N) [] , ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ ⟩ ⟩
⇓→—↠×𝔹{Γ}{γ} {σ = σ} {L · M} {c} (⇓-app {N = N} L⇓ƛNδ N⇓c) γ≈ₑσ
    with ⇓→—↠×𝔹{σ = σ} L⇓ƛNδ γ≈ₑσ
... | ⟨ _ , ⟨ σL—↠ƛτN , ⟨ τ , ⟨ δ≈ₑτ , ≡ƛτN ⟩ ⟩ ⟩ ⟩ rewrite ≡ƛτN
    with ⇓→—↠×𝔹 {σ = ext-subst τ (⟪ σ ⟫ M)} N⇓c
           (λ {x} → ≈ₑ-ext{σ = τ} δ≈ₑτ ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ {x})
       | β{∅}{⟪ exts τ ⟫ N}{⟪ σ ⟫ M}
... | ⟨ N' , ⟨ —↠N' , c≈N' ⟩ ⟩ | ƛτN·σM—→
    rewrite sub-sub{M = N}{σ₁ = exts τ}{σ₂ = subst-zero (⟪ σ ⟫ M)} =
    let rs = (ƛ ⟪ exts τ ⟫ N) · ⟪ σ ⟫ M —→⟨ ƛτN·σM—→ ⟩ —↠N' in
    let g = —↠-trans (appL-cong σL—↠ƛτN) rs in
    ⟨ N' , ⟨ g , c≈N' ⟩ ⟩
\end{code}

The proof is by induction on `γ ⊢ M ⇓ c`. We have three cases
to consider.

* Case `⇓-var`.
  So we have `γ x ≡ clos L δ` and `δ ⊢ L ⇓ c`.
  We need to show that `⟪ σ ⟫ x —↠ N` and `c ≈ N` for some `N`.
  The premise `γ ≈ₑ σ` tells us that `γ x ≈ σ x`, so `clos L δ ≈ σ x`.
  By the definition of `≈`, there exists a `τ` such that
  `δ ≈ₑ τ` and `σ x ≡ ⟪ τ ⟫ L `.
  Using `δ ⊢ L ⇓ c` and `δ ≈ₑ τ`, 
  the induction hypothesis gives us
  `⟪ τ ⟫ L —↠ N` and `c ≈ N` for some `N`.
  So we have shown that `⟪ σ ⟫ x —↠ N` and `c ≈ N` for some `N`.

* Case `⇓-lam`.
  We immediately have `⟪ σ ⟫ (ƛ N) —↠ ⟪ σ ⟫ (ƛ N)`
  and `clos (⟪ σ ⟫ (ƛ N)) γ ≈ ⟪ σ ⟫ (ƛ N)`.

* Case `⇓-app`.
  Using `γ ⊢ L ⇓ clos N δ` and `γ ≈ₑ σ`, 
  the induction hypothesis gives us
  
        ⟪ σ ⟫ L —↠ ƛ ⟪ exts τ ⟫ N                                           (1)
  
  and `δ ≈ₑ τ` for some `τ`.
  From `γ≈ₑσ` we have `clos M γ ≈ ⟪ σ ⟫ M`.
  Then with `(δ ,' clos M γ) ⊢ N ⇓ c`,
  the induction hypothesis gives us `c ≈ N'` and
  
        ⟪ exts τ ⨟ subst-zero (⟪ σ ⟫ M) ⟫ N —↠ N'                           (2)
  
  Meanwhile, by `β`, we have

        (ƛ ⟪ exts τ ⟫ N) · ⟪ σ ⟫ M —→ ⟪ subst-zero (⟪ σ ⟫ M) ⟫ (⟪ exts τ ⟫ N)

  which is the same as the following, by `sub-sub`.
  
        (ƛ ⟪ exts τ ⟫ N) · ⟪ σ ⟫ M —→ ⟪ exts τ ⨟ subst-zero (⟪ σ ⟫ M) ⟫  N  (3)

  Using (3) and (2) we have
  
        (ƛ ⟪ exts τ ⟫ N) · ⟪ σ ⟫ M —↠ N'                                    (4)

  From (1) we have

        ⟪ σ ⟫ L · ⟪ σ ⟫ M —↠ (ƛ ⟪ exts τ ⟫ N) · ⟪ σ ⟫ M

  which we combine with (4) to conclude that

        ⟪ σ ⟫ L · ⟪ σ ⟫ M —↠ N'


With the main lemma complete, we establish the forward direction
of the equivalence between the big-step semantics and beta reduction.

\begin{code}
cbn→reduce :  ∀{M : ∅ ⊢ ★}{Δ}{δ : ClosEnv Δ}{N′ : Δ , ★ ⊢ ★}
     → ∅' ⊢ M ⇓ clos (ƛ N′) δ
       -----------------------------
     → Σ[ N ∈ ∅ , ★ ⊢ ★ ] (M —↠ ƛ N)
cbn→reduce {M}{Δ}{δ}{N′} M⇓c
    with ⇓→—↠×𝔹{σ = ids} M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , ⟨ σ , ⟨ h , eq2 ⟩ ⟩ ⟩ ⟩
    rewrite sub-id{M = M} | eq2 =
    ⟨ ⟪ exts σ ⟫ N′ , rs ⟩
\end{code}

The proof of the backward direction, that beta reduction to a lambda
implies that the big-step semantics produces a result, will leverage the
denotational semantics defined in the next chapter, and appears in the
chapter on Adequacy.

## Notes

In the seminal article _Call-by-name, call-by-value, and the
λ-calculus_, Plotkin defined a call-by-name partial function similar
to the big-step semantics in this chapter, except that it used
substitution instead of environments. Corollary 2 (page 146) of his
article states that a term `M` beta reduces to a lambda abstraction if
and only if call-by-name produces a value. His proof is quite
different from ours in that it relies on two auxilliary reduction
relations called _left reduction_ and _standard reduction_. Theorem 1
(Standardisation) states that `M —↠ L` if and only if `M` goes to `L`
via standard reductions.  Corollary 1 then establishes that `M —↠ ƛ N`
if and only if `M` goes to `ƛ N′`, for some `N′`, by left
reduction. Theorem 2 then connects call-by-name evaluation to left
reduction.  Finally, Corollary 2 combines these results to show that
`M —↠ ƛ N` if and only if call-by-name produces a value.


## Unicode

This chapter uses the following unicode:

    ≈  U+2248  ALMOST EQUAL TO (\~~ or \approx)
    ₑ  U+2091  LATIN SUBSCRIPT SMALL LETTER E (\_e)
    ⊢  U+22A2  RIGHT TACK (\|- or \vdash)
    ⇓  U+21DB  DOWNWARDS DOUBLE ARROW (\d= or \Downarrow)
    
