---
title     : "The call-by-name evaluation strategy"
layout    : page
prev      : /Confluence/
permalink : /CallByName/
next      : /Denotational/
---

\begin{code}
module plfa.CallByName where
\end{code}

## Imports

\begin{code}
open import plfa.Untyped
  using (Context; _⊢_; _∋_; ★; ∅; _,_; Z; S_; `_; ƛ_; _·_; subst; subst-zero;
         exts; rename)
open import plfa.LambdaReduction
  using (β; _—↠_; _—→⟨_⟩_; _[]; —↠-trans; appL-cong)
open import plfa.Soundness
  using (Subst)
open import plfa.Substitution
  using (ids; rename-subst; sub-id; sub-sub)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
\end{code}

## Call-by-name evaluation strategy for the lambda calculus

The call-by-name evaluation strategy is a deterministic method for
computing the value of a program in the lambda calculus. We shall
prove that the call-by-name strategy produces a value if and only if
beta reduction can reduce the program to a lambda abstraction.

We present the call-by-name strategy as a relation between an an input
term and an output value. Such a relation is often called a _big-step
semantics_, as it relates the input term directly to the final result,
in contrast to the small-step reduction relation `—→` that maps a term
to another term in which a single sub-computation has been completed.

To handle variables and function application, there is the choice
between using substitution, as in `—→`, or to use an _environment_.
An environment in for call-by-name is a map from variables to closures,
that is, to terms paired with their environments. We choose to use
environments instead of substitution because the point of the call-by-name
strategy is to be closer to an implementation of the language.

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

The call-by-name strategy is represented as a ternary relation,
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


## Call-by-name is deterministic

If the call-by-name relation evaluates a term `M` to both `V` and
`V′`, then `V` and `V′` must be identical. In other words, the
call-by-name relation is a partial function. The proof is a
straightforward induction on the two call-by-name derivations.

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


## Call-by-name evaluation implies beta reduction to an abstraction

Call-by-name evaluation of a term produces a value if and only if the
term can reduce to a lambda abstraction by beta reduction. Here
we prove the forward direction, that call-by-name evaluation implies
beta reduction to a lambda.

      ∅' ⊢ M ⇓ clos (ƛ N′) δ
      -----------------------------
    → Σ[ N ∈ ∅ , ★ ⊢ ★ ] (M —↠ ƛ N)

We postpone the backward direction to the chapter Adequacy, where
the result will be an easy corollary of properties of a denotational
semantics.

We prove the forward direction by induction on the call-by-name
derivation. As is often necessary, one must generalize the statement
to get the induction to go through. In the case for `⇓-app` (function
application), we add the argument to the environment, so the
environment becomes non-empty. The corresponding β reduction will
substitute the argument into the body of the lambda abstraction.  So
we generalize the statement to allow an arbitrary environment `γ` and
we add a premise that relates the environment `γ` to an equivalent
substitution `σ`.

The case for `⇓-app` also requires that we strengthen the conclusion
of the statement. We have `γ ⊢ L ⇓ clos (λ N) δ` and the induction
hypothesis tells us that `L —↠ ƛ N′`, but we need to know that `N` and
`N′` are equivalent. In particular, that `N ≡ subst τ N′` where `τ` is
the substitution that is equivalent to `δ`. Therefore we add to the
conclusion of the statement, stating that the two results are
equivalent.

We make the two notions of equivalence precise by defining the
following two mutually-recursive predicates `c ≈ M` and `γ ≃ σ`.

\begin{code}
_≈_ : Clos → (∅ ⊢ ★) → Set
_≃_ : ∀{Γ} → ClosEnv Γ → Subst Γ ∅ → Set

(clos {Γ} M γ) ≈ N = Σ[ σ ∈ Subst Γ ∅ ] γ ≃ σ × (N ≡ subst σ M)

γ ≃ σ = ∀{x} → (γ x) ≈ (σ x)
\end{code}

We can now give the generalized statement:

    If γ ⊢ M ⇓ c  and  γ ≃ σ,
    then subst σ M —↠ N and c ≈ N for some N.

But before starting the proof, we establish a couple lemmas
about equivalent environments and substitutions.

The empty environment is equivalent to the identity substitution.

\begin{code}
≃-id : ∅' ≃ ids
≃-id {()}
\end{code}

We define an auxilliary function for extending a substitution.

\begin{code}
ext-subst : ∀{Γ Δ} → Subst Γ Δ → Δ ⊢ ★ → Subst (Γ , ★) Δ
ext-subst{Γ}{Δ} σ N {A} = (subst (subst-zero N)) ∘ (exts σ)
\end{code}

The next lemma states that if you start with an equivalent
environment and substitution `γ ≃ σ`, extending them with
an equivalent closure and term `c ≈ N` produces
an equivalent environment and substitution:
`(γ ,' c) ≃ (ext-subst σ N)`.

\begin{code}
≃-ext : ∀ {Γ} {γ : ClosEnv Γ} {σ : Subst Γ ∅} {c} {N : ∅ ⊢ ★}
      → γ ≃ σ  →  c ≈ N
        --------------------------
      → (γ ,' c) ≃ (ext-subst σ N)
≃-ext {Γ} {γ} {σ} γ≃σ e {Z} = e
≃-ext {Γ} {γ} {σ}{c}{N} γ≃σ e {S x} = G γ≃σ
  where
      eq : ext-subst σ N (S x) ≡ σ x
      eq =
        begin
          (subst (subst-zero N)) (exts σ (S x))
        ≡⟨⟩
          ((subst (subst-zero N)) ∘ (rename S_)) (σ x)
        ≡⟨ rename-subst{M = σ x} ⟩
          (subst ((subst-zero N) ∘ S_)) (σ x)        
        ≡⟨ sub-id ⟩
          σ x
        ∎
      G : (γ x) ≈ (σ x) → (γ x) ≈ (ext-subst σ N (S x))
      G b rewrite eq = b
\end{code}

The proof proceeds by case analysis on the input variable.

* If it is `Z`, then we immediately conclude using the
  premise `c ≈ N`.

* If it is `S x`, then we need to show that

        (γ ,' c) (S x) ≃ ext-subst σ N (S x)
        
  The left-hand side is equal to `γ x`.  The right-hand side is equal
  to `σ x`, which we prove using two propositions from the
  Substitution chapter `rename-subst` and `sub-id`. The premise
  that `γ ≃ σ` then allows us to conclude this case.

Now we come to the main lemma: if a term `M` evaluates under call-by-name
to a closure `c` in environment `γ`, and if `γ ≃ σ`, then `subst σ M`
reduces to some term `N` that is equivalent to `c`.

\begin{code}
⇓→—↠×𝔹 : ∀{Γ}{γ : ClosEnv Γ}{σ : Subst Γ ∅}{M : Γ ⊢ ★}{c : Clos}
       → γ ⊢ M ⇓ c → γ ≃ σ
       → Σ[ N ∈ ∅ ⊢ ★ ] (subst σ M —↠ N) × c ≈ N
⇓→—↠×𝔹 {γ = γ} (⇓-var{x = x} eq d) h
    with γ x | h {x} | eq
... | clos M' γ' | ⟨ σ' , ⟨ h' , eq' ⟩ ⟩ | refl
    with ⇓→—↠×𝔹{σ = σ'} d h'
... | ⟨ N , ⟨ r' , bn ⟩ ⟩ rewrite eq' =    
      ⟨ N , ⟨ r' , bn ⟩ ⟩
⇓→—↠×𝔹 {σ = σ} {c = clos (ƛ N) γ} ⇓-lam h =
    ⟨ subst σ (ƛ N) , ⟨ subst σ (ƛ N) [] , ⟨ σ , ⟨ h , refl ⟩ ⟩ ⟩ ⟩
⇓→—↠×𝔹 {σ = σ} {L · M} {c} (⇓-app {N = N} d₁ d₂) h
    with ⇓→—↠×𝔹{σ = σ} d₁ h
... | ⟨ L' , ⟨ σL—↠L' , ⟨ σ₁ , ⟨ Hδσ₁ , eq ⟩ ⟩ ⟩ ⟩ rewrite eq
    with ⇓→—↠×𝔹{σ = ext-subst σ₁ (subst σ M)} d₂
           (λ {x} → ≃-ext{σ = σ₁} Hδσ₁ ⟨ σ , ⟨ h , refl ⟩ ⟩ {x})
       | β{∅}{subst (exts σ₁) N}{subst σ M}
... | ⟨ N' , ⟨ r' , bl ⟩ ⟩ | r 
    rewrite sub-sub{M = N}{σ₁ = exts σ₁}{σ₂ = subst-zero (subst σ M)} =
    let rs = (ƛ subst (exts σ₁) N) · subst σ M —→⟨ r ⟩ r' in
    ⟨ N' , ⟨ —↠-trans (appL-cong σL—↠L') rs , bl ⟩ ⟩
\end{code}

The proof is by induction on `γ ⊢ M ⇓ c`. We have three cases
to consider.

* Case `⇓-var`.
  So we have `γ x ≡ clos M' γ'` and `γ' ⊢ M' ⇓ c`.
  We need to show that `subst σ x —↠ N` and `c ≈ N` for some `N`.
  

  The premise `γ ≃ σ` tells us that `clos M' γ' ≈ σ x`,
  so there exists a `σ'` such that `γ' ≃ σ'` and `σ x ≡ subst σ' M' `.
  The induction hypothesis for `γ' ⊢ M' ⇓ c` then gives us
  `subst σ M' —↠ N` and `clos M' γ' ≈ N` for some `N`.
  

* Case `⇓-lam`.

* Case `⇓-app`.


[JGS: to do: write explanation]

\begin{code}
cbn→reduce :  ∀{M : ∅ ⊢ ★}{Δ}{δ : ClosEnv Δ}{N′ : Δ , ★ ⊢ ★}
     → ∅' ⊢ M ⇓ clos (ƛ N′) δ
     → Σ[ N ∈ ∅ , ★ ⊢ ★ ] (M —↠ ƛ N)
cbn→reduce {M}{Δ}{δ}{N′} M⇓c
    with ⇓→—↠×𝔹{σ = ids} M⇓c ≃-id
... | ⟨ N , ⟨ rs , ⟨ σ , ⟨ h , eq2 ⟩ ⟩ ⟩ ⟩
    rewrite sub-id{M = M} | eq2 =
    ⟨ subst (λ {A} → exts σ) N′ , rs ⟩
\end{code}


