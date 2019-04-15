---
title     : "DenotAdequacy: Adequacy of denotational semantics with respect to operational semantics"
layout    : page
prev      : /DenotSound/
permalink : /DenotAdequate/
next      : /Acknowledgements/
---

\begin{code}
module plfa.DenotAdequate where
\end{code}

## Imports

\begin{code}
open import plfa.Untyped
open import plfa.Denot

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit
open import Relation.Nullary using (Dec; yes; no)
\end{code}


In this chapter we prove that the denotational semantics is adequate,
that is, if a term M is denotationally equal to a lambda abstraction,
then M multi-step reduces to a lambda abstraction.

    ℰ M ≃ ℰ (ƛ N)  implies M —↠ ƛ N' for some N'

It is well known that a term can reduce to a lambda abstraction using
full β reduction if and only if it can reduce to a lambda abstraction
using the call-by-name reduction strategy. So we shall prove that ℰ M
≃ ℰ (ƛ N) implies that M halts under call-by-name evaluation, which we
define with a big-step semantics written γ' ⊢ M ⇓ c, where c is a
closure (a term paired with an environment) and γ' is an environment
that maps variables to closures

Recall that ℰ M ≃ ℰ (ƛ N) is equivalent to saying that γ ⊢ M ↓ (v ↦
v') for some v and v'.  We will show that γ ⊢ M ↓ (v ↦ v') implies
that M halts under call-by-name.  The proof will be an induction on
the derivation of γ ⊢ M ↓ v, and to strengthen the induction
hypothesis, we will relate semantic values to closures using a
_logical relation_ 𝕍.

The rest of this chapter is organized as follows.

* We loosen the requirement that M result in a function value to
  instead require that M result in a value that is greater than or
  equal to a function value. We establish several properties about
  being ``greater than a function''.

* We define the call-by-name big-step semantics of the lambda calculus
  and prove that it is deterministic.

* We define the logical relation 𝕍 that relates values and closures,
  and extend it to a relation on terms 𝔼 and environments 𝔾.

* We prove the main lemma,
  that if 𝔾 γ γ' and γ ⊢ M ↓ v, then 𝔼 v (clos M γ').

* We prove adequacy as a corollary to the main lemma.


## The property of being greater or equal to a function

We define the following short-hand for saying that a value is
greather-than or equal to a function value.

\begin{code}
AboveFun : Value → Set
AboveFun v = Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] v₁ ↦ v₂ ⊑ v
\end{code}

If a value v is greater than a function, then an even greater value v'
is too.

\begin{code}
AboveFun-⊑ : ∀{v v' : Value}
      → AboveFun v → v ⊑ v'
        -------------------
      → AboveFun v'
AboveFun-⊑ ⟨ v₁ , ⟨ v₂ , lt' ⟩ ⟩ lt = ⟨ v₁ , ⟨ v₂ , Trans⊑ lt' lt ⟩ ⟩
\end{code}

The bottom value ⊥ is not greater than a function.

\begin{code}
AboveFun⊥ : ¬ AboveFun ⊥
AboveFun⊥ ⟨ v₁ , ⟨ v₂ , lt ⟩ ⟩
    with sub-inv-fun lt
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆⊥ , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ A , ⟨ B , m ⟩ ⟩
    with Γ⊆⊥ m
... | ()
\end{code}

If the join of two values v₁ and v₂ is greater than a function, then
at least one of them is too.

\begin{code}
AboveFun-⊔ : ∀{v₁ v₂}
           → AboveFun (v₁ ⊔ v₂)
           → AboveFun v₁ ⊎ AboveFun v₂
AboveFun-⊔{v₁}{v₂} ⟨ v , ⟨ v' , v↦v'⊑v₁⊔v₂ ⟩ ⟩ 
    with sub-inv-fun v↦v'⊑v₁⊔v₂
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v₁⊔v₂ , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ A , ⟨ B , m ⟩ ⟩
    with Γ⊆v₁⊔v₂ m
... | inj₁ x = inj₁ ⟨ A , ⟨ B , (∈→⊑ x) ⟩ ⟩
... | inj₂ x = inj₂ ⟨ A , ⟨ B , (∈→⊑ x) ⟩ ⟩
\end{code}

On the other hand, if neither of v₁ and v₂ is greater than a function,
then their join is also not greater than a function.

\begin{code}
not-AboveFun-⊔ : ∀{v₁ v₂ : Value}
               → ¬ AboveFun v₁ → ¬ AboveFun v₂
               → ¬ AboveFun (v₁ ⊔ v₂)
not-AboveFun-⊔ af1 af2 af12
    with AboveFun-⊔ af12
... | inj₁ x = contradiction x af1
... | inj₂ x = contradiction x af2
\end{code}

The converse is also true. If the join of two values is not above a
function, then neither of them is individually.

\begin{code}
not-AboveFun-⊔-inv : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂)
              → ¬ AboveFun v₁ × ¬ AboveFun v₂
not-AboveFun-⊔-inv af = ⟨ f af , g af ⟩
  where
    f : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂) → ¬ AboveFun v₁
    f{v₁}{v₂} af12 ⟨ v , ⟨ v' , lt ⟩ ⟩ =
        contradiction ⟨ v , ⟨ v' , ConjR1⊑ lt ⟩ ⟩ af12
    g : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂) → ¬ AboveFun v₂
    g{v₁}{v₂} af12 ⟨ v , ⟨ v' , lt ⟩ ⟩ =
        contradiction ⟨ v , ⟨ v' , ConjR2⊑ lt ⟩ ⟩ af12
\end{code}

The property of being greater than a function value is decidable, as
exhibited by the following function.

\begin{code}
AboveFun? : (v : Value) → Dec (AboveFun v)
AboveFun? ⊥ = no AboveFun⊥
AboveFun? (v ↦ v') = yes ⟨ v , ⟨ v' , Refl⊑ ⟩ ⟩
AboveFun? (v₁ ⊔ v₂)
    with AboveFun? v₁ | AboveFun? v₂
... | yes ⟨ v , ⟨ v' , lt ⟩ ⟩ | _ = yes ⟨ v , ⟨ v' , (ConjR1⊑ lt) ⟩ ⟩
... | no _ | yes ⟨ v , ⟨ v' , lt ⟩ ⟩ = yes ⟨ v , ⟨ v' , (ConjR2⊑ lt) ⟩ ⟩
... | no x | no y = no (not-AboveFun-⊔ x y)
\end{code}


## Big-step semantics for call-by-name lambda calculus

To better align with the denotational semantics, we shall use an
environment-passing big-step semantics. Because this is call-by-name,
an environment maps each variable to a closure, that is, to a term
paired with its environment. (Environments and closures are mutually
recursive.) We define environments and closures as follows.

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

The following is the big-step semantics for call-by-name evaluation,
which we describe below.

\begin{code}
data _⊢_⇓_ : ∀{Γ} → ClosEnv Γ → (Γ ⊢ ★) → Clos → Set where

  ⇓-var : ∀{Γ}{γ : ClosEnv Γ}{x : Γ ∋ ★}{Δ}{δ : ClosEnv Δ}{M : Δ ⊢ ★}{c}
        → γ x ≡ clos M δ
        → δ ⊢ M ⇓ c
          -----------
        → γ ⊢ ` x ⇓ c

  ⇓-lam : ∀{Γ}{γ : ClosEnv Γ}{M : Γ , ★ ⊢ ★}
        → γ ⊢ ƛ M ⇓ clos (ƛ M) γ

  ⇓-app : ∀{Γ}{γ : ClosEnv Γ}{L M : Γ ⊢ ★}{Δ}{δ : ClosEnv Δ}{L' : Δ , ★ ⊢ ★}{c}
       → γ ⊢ L ⇓ clos (ƛ L') δ   →   (δ ,' clos M γ) ⊢ L' ⇓ c
         ----------------------------------------------------
       → γ ⊢ L · M ⇓ c
\end{code}

* The (⇓-var) rule evaluates a variable by finding the associated
  closure in the environment and then evaluating the closure.

* The (⇓-lam) rule turns a lambda abstraction into a closure
  by packaging it up with its environment.

* The (⇓-app) rule performs function application by first evaluating
  the term L in operator position. If that produces a closure containing
  a lambda abstraction (ƛ L'), then we evaluate the body L' in an
  environment extended with the argument M. Note that M is not
  evaluated in rule (⇓-app) because this is call-by-name and not
  call-by-value.

If the big-step semantics says that a term M evaluates to both c and
c', then c and c' are identical. In other words, the big-step relation
is a partial function.

\begin{code}
⇓-determ : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{c c' : Clos}
         → γ ⊢ M ⇓ c → γ ⊢ M ⇓ c'
         → c ≡ c'
⇓-determ (⇓-var eq1 mc) (⇓-var eq2 mc')
      with trans (sym eq1) eq2
... | refl = ⇓-determ mc mc'
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc mc₁) (⇓-app mc' mc'') 
    with ⇓-determ mc mc'
... | refl = ⇓-determ mc₁ mc''
\end{code}


## Relating values to closures

Next we relate semantic values to closures.  The relation 𝕍 is for
closures whose term is a lambda abstraction (i.e. in WHNF), whereas
the relation 𝔼 is for any closure. Roughly speaking, 𝔼 v c will hold
if, when v is greater than a function value, c evaluates to a closure
c' in WHNF and 𝕍 v c'. Regarding 𝕍 v c, it will hold when c is in
WHNF, and if v is a function, the body of c evaluates according to v.

\begin{code}
𝕍 : Value → Clos → Set
𝔼 : Value → Clos → Set
\end{code}

We define 𝕍 as a function from values and closures to Set and not as a
data type because it is mutually recursive with 𝔼 in a negative
position (to the left of an implication).  We first perform case
analysis on the term in the closure. If the term is a variable or
application, then 𝕍 is false (Bot). If the term is a lambda
abstraction, we define 𝕍 by recursion on the value, which we
describe below.

\begin{code}
𝕍 v (clos (` x₁) γ) = Bot
𝕍 v (clos (M · M₁) γ) = Bot
𝕍 ⊥ (clos (ƛ M) γ) = ⊤
𝕍 (v ↦ v') (clos (ƛ M) γ) =
    (∀{c : Clos} → 𝔼 v c → AboveFun v' → Σ[ c' ∈ Clos ]
        (γ ,' c) ⊢ M ⇓ c'  ×  𝕍 v' c')
𝕍 (v₁ ⊔ v₂) (clos (ƛ M) γ) = 𝕍 v₁ (clos (ƛ M) γ) × 𝕍 v₂ (clos (ƛ M) γ)
\end{code}

* If the value is ⊥, then the result is true (⊤).

* If the value is a join (v₁ ⊔ v₂), then the result is the pair
  (conjunction) of 𝕍 is true for both v₁ and v₂.

* The important case is for a function value (v ↦ v') and closure
  (clos (ƛ M) γ). Given any closure c such that 𝔼 v c, if v' is
  greater than a function, then M evaluates (with γ extended with c)
  to some closure c' and we have 𝕍 v' c'.


The definition of 𝔼 is straightforward. If v is a greater than a
function, then M evaluates to a closure related to v.

\begin{code}
𝔼 v (clos M γ') = AboveFun v → Σ[ c ∈ Clos ] γ' ⊢ M ⇓ c × 𝕍 v c
\end{code}

The proof of the main lemma is by induction on γ ⊢ M ↓ v, so it goes
underneath lambda abstractions and must therefore reason about open
terms (terms with variables). Thus, we must relate environments of
semantic values to environments of closures.  In the following, 𝔾
relates γ to γ' if the corresponding values and closures are related
by 𝔼.

\begin{code}
𝔾 : ∀{Γ} → Env Γ → ClosEnv Γ → Set
𝔾 {Γ} γ γ' = ∀{x : Γ ∋ ★} → 𝔼 (γ x) (γ' x)

𝔾-∅ : 𝔾 `∅ ∅'
𝔾-∅ {()}

𝔾-ext : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{v c}
      → 𝔾 γ γ' → 𝔼 v c → 𝔾 (γ `, v) (γ' ,' c)
𝔾-ext {Γ} {γ} {γ'} g e {Z} = e
𝔾-ext {Γ} {γ} {γ'} g e {S x} = g
\end{code}


We need a few properties of the 𝕍 and 𝔼 relations.  The first is that
a closure in the 𝕍 relation must be in weak-head normal form.  We
define WHNF has follows.

\begin{code}
data WHNF : ∀ {Γ A} → Γ ⊢ A → Set where
  ƛ_ : ∀ {Γ} {N : Γ , ★ ⊢ ★}
     → WHNF (ƛ N)
\end{code}

The proof goes by cases on the term in the closure.

\begin{code}
𝕍→WHNF : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{v}
       → 𝕍 v (clos M γ) → WHNF M
𝕍→WHNF {M = ` x} {v} ()
𝕍→WHNF {M = ƛ M} {v} vc = ƛ_
𝕍→WHNF {M = M · M₁} {v} ()
\end{code}

Next we have an introduction rule for 𝕍 that mimics the (⊔-intro)
rule. If both v₁ and v₂ are related to a closure c, then their join is
too.

\begin{code}
𝕍⊔-intro : ∀{c v₁ v₂}
         → 𝕍 v₁ c → 𝕍 v₂ c
           ---------------
         → 𝕍 (v₁ ⊔ v₂) c
𝕍⊔-intro {clos (` x₁) x} () v2c
𝕍⊔-intro {clos (ƛ M) x} v1c v2c = ⟨ v1c , v2c ⟩
𝕍⊔-intro {clos (M · M₁) x} () v2c
\end{code}

In a moment we prove that 𝕍 is preserved when going from a greater
value to a lesser value: if 𝕍 v c and v' ⊑ v, then 𝕍 v' c.
This property, named 𝕍-sub, is needed by the main lemma in
the case for the (sub) rule.

To prove 𝕍-sub, we in turn need the following property concerning
values that are not greater than a function, that is, values that are
equivalent to ⊥. In such cases, 𝕍 v (clos (ƛ M) γ') is trivially true.

\begin{code}
not-AboveFun-𝕍 : ∀{v : Value}{Γ}{γ' : ClosEnv Γ}{M : Γ , ★ ⊢ ★ }
    → ¬ AboveFun v
      -------------------
    → 𝕍 v (clos (ƛ M) γ')
not-AboveFun-𝕍 {⊥} af = tt
not-AboveFun-𝕍 {v ↦ v'} af = ⊥-elim (contradiction ⟨ v , ⟨ v' , Refl⊑ ⟩ ⟩ af)
not-AboveFun-𝕍 {v₁ ⊔ v₂} af
    with not-AboveFun-⊔-inv af
... | ⟨ af1 , af2 ⟩ = ⟨ not-AboveFun-𝕍 af1 , not-AboveFun-𝕍 af2 ⟩
\end{code}

The proofs of 𝕍-sub and 𝔼-sub are intertwined.

\begin{code}
sub-𝕍 : ∀{c : Clos}{v v'} → 𝕍 v c → v' ⊑ v → 𝕍 v' c
sub-𝔼 : ∀{c : Clos}{v v'} → 𝔼 v c → v' ⊑ v → 𝔼 v' c
\end{code}

We prove 𝕍-sub by case analysis on the closure's term, to dispatch the
cases for variables and application. We then proceed by induction on
v' ⊑ v. We describe each case below.

\begin{code}
sub-𝕍 {clos (` x) γ} {v} () lt
sub-𝕍 {clos (M₁ · M₂) γ} () lt
sub-𝕍 {clos (ƛ M) γ} vc Bot⊑ = tt
sub-𝕍 {clos (ƛ M) γ} vc (ConjL⊑ lt1 lt2) = ⟨ (sub-𝕍 vc lt1) , sub-𝕍 vc lt2 ⟩
sub-𝕍 {clos (ƛ M) γ} ⟨ vv1 , vv2 ⟩ (ConjR1⊑ lt) = sub-𝕍 vv1 lt
sub-𝕍 {clos (ƛ M) γ} ⟨ vv1 , vv2 ⟩ (ConjR2⊑ lt) = sub-𝕍 vv2 lt
sub-𝕍 {clos (ƛ M) γ} vc (Trans⊑{v₂ = v₂} lt1 lt2) = sub-𝕍 (sub-𝕍 vc lt2) lt1
sub-𝕍 {clos (ƛ M) γ} vc (Fun⊑ lt1 lt2) ev1 sf
    with vc (sub-𝔼 ev1 lt1) (AboveFun-⊑ sf lt2)
... | ⟨ c , ⟨ Mc , v4 ⟩ ⟩ = ⟨ c , ⟨ Mc , sub-𝕍 v4 lt2 ⟩ ⟩
sub-𝕍 {clos (ƛ M) γ} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩ Dist⊑ ev1c sf
    with AboveFun? v₂ | AboveFun? v₃
... | yes af2 | yes af3
    with vc12 ev1c af2 | vc13 ev1c af3
... | ⟨ clos N δ , ⟨ M⇓c₂ , 𝕍v₂ ⟩ ⟩
    | ⟨ c₃ , ⟨ M⇓c₃ , 𝕍v₃ ⟩ ⟩ rewrite ⇓-determ M⇓c₃ M⇓c₂ with 𝕍→WHNF 𝕍v₂
... | ƛ_ =
      ⟨ clos N δ , ⟨ M⇓c₂ , ⟨ 𝕍v₂ , 𝕍v₃ ⟩ ⟩ ⟩
sub-𝕍 {c} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩  Dist⊑ ev1c sf
    | yes af2 | no naf3
    with vc12 ev1c af2
... | ⟨ clos {Γ'} N γ₁ , ⟨ M⇓c2 , 𝕍v₂ ⟩ ⟩
    with 𝕍→WHNF 𝕍v₂
... | ƛ_ {N = N'} =
      let 𝕍v₃ = not-AboveFun-𝕍{v₃}{Γ'}{γ₁}{N'} naf3 in
      ⟨ clos (ƛ N') γ₁ , ⟨ M⇓c2 , 𝕍⊔-intro 𝕍v₂ 𝕍v₃ ⟩ ⟩
sub-𝕍 {c} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩ Dist⊑ ev1c sf
    | no naf2 | yes af3
    with vc13 ev1c af3
... | ⟨ clos {Γ'} N γ₁ , ⟨ M⇓c3 , 𝕍3c ⟩ ⟩ 
    with 𝕍→WHNF 𝕍3c
... | ƛ_ {N = N'} =
      let 𝕍2c = not-AboveFun-𝕍{v₂}{Γ'}{γ₁}{N'} naf2 in
      ⟨ clos (ƛ N') γ₁ , ⟨ M⇓c3 , 𝕍⊔-intro 𝕍2c 𝕍3c ⟩ ⟩
sub-𝕍 {c} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩  Dist⊑ ev1c ⟨ v , ⟨ v' , lt ⟩ ⟩
    | no naf2 | no naf3
    with AboveFun-⊔ ⟨ v , ⟨ v' , lt ⟩ ⟩
... | inj₁ af2 = ⊥-elim (contradiction af2 naf2)
... | inj₂ af3 = ⊥-elim (contradiction af3 naf3)
\end{code}

* Case (Bot⊑). We immediately have 𝕍 ⊥ (clos (ƛ M) γ).

* Case (ConjL⊑).

        v₁' ⊑ v     v₂' ⊑ v
        -------------------
        (v₁' ⊔ v₂') ⊑ v

  The induction hypotheses gives us 𝕍 v₁' (clos (ƛ M) γ)
  and 𝕍 v₂' (clos (ƛ M) γ), which is all we need for this case. 

* Case (ConjR1⊑).

        v' ⊑ v₁
        -------------
        v' ⊑ (v₁ ⊔ v₂)

  The induction hypothesis gives us 𝕍 v' (clos (ƛ M) γ).

* Case (ConjR2⊑).

        v' ⊑ v₂
        -------------
        v' ⊑ (v₁ ⊔ v₂)

  Again, the induction hypothesis gives us 𝕍 v' (clos (ƛ M) γ).

* Case (Trans⊑).

        v' ⊑ v₂   v₂ ⊑ v
        -----------------
             v' ⊑ v

  The induction hypothesis for v₂ ⊑ v gives us
  𝕍 v₂ (clos (ƛ M) γ). We apply the induction hypothesis
  for v' ⊑ v₂ to conclude that 𝕍 v' (clos (ƛ M) γ).

* Case (Dist⊑). This case  is the most difficult. We have

        𝕍 (v₁ ↦ v₂) (clos (ƛ M) γ)
        𝕍 (v₁ ↦ v₃) (clos (ƛ M) γ)

  and need to show that 

        𝕍 (v₁ ↦ (v₂ ⊔ v₃)) (clos (ƛ M) γ)
  
  Let c be an arbtrary closure such that 𝔼 v₁ c.
  Assume (v₂ ⊔ v₃) is greater than a function.
  Unfortunately, this does not mean that both v₂ and v₃
  are above functions. But thanks to the lemma AboveFun-⊔,
  we know that at least one of them is greater than a function.
  
  * Suppose both of them are greater than a function.  Then we have
    γ ⊢ M ⇓ clos N δ and 𝕍 v₂ (clos N δ).  We also have γ ⊢ M ⇓ c₃ and
    𝕍 v₃ c₃.  Because the big-step semantics is deterministic, we have
    c₃ ≡ clos N δ. Also, from 𝕍 v₂ (clos N δ) we know that N ≡ ƛ N'
    for some N'. We conclude that 𝕍 (v₂ ⊔ v₃) (clos (ƛ N') δ).

  * Suppose one of them is greater than a function and the other is
    not: say AboveFun v₂ and ¬ AboveFun v₃. Then from 𝕍 (v₁ ↦ v₂) (clos (ƛ M) γ)
    we have γ ⊢ M ⇓ clos N γ₁ and 𝕍 v₂ (clos N γ₁). From this we have
    N ≡ ƛ N' for some N'. Meanwhile, from ¬ AboveFun v₃ we have
    𝕍 v₃ (clos N γ₁). We conclude that We conclude that
    𝕍 (v₂ ⊔ v₃) (clos (ƛ N') γ₁).
    

The proof of sub-𝔼 is direct.

\begin{code}
sub-𝔼 {clos M γ} {v} {v'} 𝔼v v'⊑v fv'
    with 𝔼v (AboveFun-⊑ fv' v'⊑v)
... | ⟨ c , ⟨ M⇓c , 𝕍v ⟩ ⟩ =
      ⟨ c , ⟨ M⇓c , sub-𝕍 𝕍v v'⊑v ⟩ ⟩
\end{code}

From AboveFun v' and v' ⊑ v we have AboveFun v.  Then with 𝔼 v c we
obtain a closure c such that γ ⊢ M ⇓ c and 𝕍 v c. We conclude with an
application of sub-𝕍 with v' ⊑ v to show 𝕍 v' c.


## Programs with function denotation terminate via call-by-name

The main lemma proves that if a term has a denotation that is above a
function, then it terminates via call-by-name. In more detail, if γ ⊢
M ↓ v and 𝔾 γ γ', then 𝔼 v (clos M γ'). The proof is by induction on
the derivation of γ ⊢ M ↓ v we discuss each case below.

The following lemma, kth-x, is used in the case for the (var) rule.

\begin{code}
kth-x : ∀{Γ}{γ' : ClosEnv Γ}{x : Γ ∋ ★}
     → Σ[ Δ ∈ Context ] Σ[ δ ∈ ClosEnv Δ ] Σ[ M ∈ Δ ⊢ ★ ]
                 γ' x ≡ clos M δ
kth-x{γ' = γ'}{x = x} with γ' x
... | clos{Γ = Δ} M δ = ⟨ Δ , ⟨ δ , ⟨ M , refl ⟩ ⟩ ⟩
\end{code}

\begin{code}
↓→𝔼 : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{M : Γ ⊢ ★ }{v}
            → 𝔾 γ γ' → γ ⊢ M ↓ v → 𝔼 v (clos M γ')
↓→𝔼 {Γ} {γ} {γ'} {`_ x} {v} 𝔾γγ' var fγx
    with kth-x{Γ}{γ'}{x} | 𝔾γγ'{x = x}
... | ⟨ Δ , ⟨ δ , ⟨ L , eq ⟩ ⟩ ⟩ | 𝔾γγ'x rewrite eq
    with 𝔾γγ'x fγx
... | ⟨ c , ⟨ L⇓c , 𝕍γx ⟩ ⟩ =
      ⟨ c , ⟨ (⇓-var eq L⇓c) , 𝕍γx ⟩ ⟩
↓→𝔼 {Γ} {γ} {γ'} {L · M} {v} 𝔾γγ' (↦-elim{v₁ = v₁} d₁ d₂) fv
    with ↓→𝔼 𝔾γγ' d₁ ⟨ v₁ , ⟨ v , Refl⊑ ⟩ ⟩
... | ⟨ clos L' δ , ⟨ L⇓L' , 𝕍v₁↦v ⟩ ⟩ 
    with 𝕍→WHNF 𝕍v₁↦v
... | ƛ_ {N = L''} 
    with 𝕍v₁↦v {clos M γ'} (↓→𝔼 𝔾γγ' d₂) fv
... | ⟨ c' , ⟨ L''⇓c' , 𝕍v ⟩ ⟩ =
    ⟨ c' , ⟨ ⇓-app L⇓L' L''⇓c' , 𝕍v ⟩ ⟩
↓→𝔼 {Γ} {γ} {γ'} {ƛ M} {v ↦ v'} 𝔾γγ' (↦-intro d) fv↦v' =
    ⟨ (clos (ƛ M) γ') , ⟨ ⇓-lam , E ⟩ ⟩
    where E : {c : Clos} → 𝔼 v c → AboveFun v'
            → Σ[ c' ∈ Clos ] (γ' ,' c) ⊢ M ⇓ c'  ×  𝕍 v' c'
          E {c} 𝔼vc fv' = ↓→𝔼 (λ {x} → 𝔾-ext{Γ}{γ}{γ'} 𝔾γγ' 𝔼vc {x}) d fv'
↓→𝔼 {Γ} {γ} {γ'} {M} {⊥} 𝔾γγ' ⊥-intro f⊥ = ⊥-elim (AboveFun⊥ f⊥)
↓→𝔼 {Γ} {γ} {γ'} {M} {v₁ ⊔ v₂} 𝔾γγ' (⊔-intro d₁ d₂) fv12
    with AboveFun? v₁ | AboveFun? v₂
... | yes fv1 | yes fv2
    with ↓→𝔼 𝔾γγ' d₁ fv1 | ↓→𝔼 𝔾γγ' d₂ fv2 
... | ⟨ c₁ , ⟨ M⇓c₁ , 𝕍v₁ ⟩ ⟩ | ⟨ c₂ , ⟨ M⇓c₂ , 𝕍v₂ ⟩ ⟩
    rewrite ⇓-determ M⇓c₂ M⇓c₁ =
    ⟨ c₁ , ⟨ M⇓c₁ , 𝕍⊔-intro 𝕍v₁ 𝕍v₂ ⟩ ⟩
↓→𝔼 𝔾γγ' (⊔-intro{v₁ = v₁}{v₂ = v₂} d₁ d₂) fv12 | yes fv1 | no nfv2
    with ↓→𝔼 𝔾γγ' d₁ fv1 
... | ⟨ clos {Γ'} M' γ₁ , ⟨ M⇓c₁ , 𝕍v₁ ⟩ ⟩
    with 𝕍→WHNF 𝕍v₁
... | ƛ_ {N = M''} =
    let 𝕍v₂ = not-AboveFun-𝕍{v₂}{Γ'}{γ₁}{M''} nfv2 in
    ⟨ clos (ƛ M'') γ₁ , ⟨ M⇓c₁ , 𝕍⊔-intro 𝕍v₁ 𝕍v₂ ⟩ ⟩
↓→𝔼 𝔾γγ' (⊔-intro{v₁ = v₁}{v₂ = v₂} d₁ d₂) fv12 | no nfv1  | yes fv2
    with ↓→𝔼 𝔾γγ' d₂ fv2
... | ⟨ clos {Γ'} M' γ₁ , ⟨ M⇓c₂ , 𝕍2c ⟩ ⟩
    with 𝕍→WHNF 𝕍2c
... | ƛ_ {N = M} =
    let 𝕍1c = not-AboveFun-𝕍{v₁}{Γ'}{γ₁}{M} nfv1 in
    ⟨ clos (ƛ M) γ₁ , ⟨ M⇓c₂ , 𝕍⊔-intro 𝕍1c 𝕍2c ⟩ ⟩
↓→𝔼 𝔾γγ' (⊔-intro d₁ d₂) fv12 | no nfv1  | no nfv2
    with AboveFun-⊔ fv12
... | inj₁ fv1 = ⊥-elim (contradiction fv1 nfv1)
... | inj₂ fv2 = ⊥-elim (contradiction fv2 nfv2)
↓→𝔼 {Γ} {γ} {γ'} {M} {v'} 𝔾γγ' (sub{v₁ = v} d v'⊑v) fv'
    with ↓→𝔼 {Γ} {γ} {γ'} {M} 𝔾γγ' d (AboveFun-⊑ fv' v'⊑v)
... | ⟨ c , ⟨ M⇓c , 𝕍v ⟩ ⟩ =
      ⟨ c , ⟨ M⇓c , sub-𝕍 𝕍v v'⊑v ⟩ ⟩
\end{code}

* Case (var). Looking up x in γ' yields some closure, clos L δ,
  and from 𝔾 γ γ' we have 𝔼 (γ x) (clos L δ). With the premise
  AboveFun (γ x), we obtain a closure c such that δ ⊢ L ⇓ c
  and 𝕍 (γ x) c. To conclude γ' ⊢ ` x ⇓ c via (⇓-var), we 
  need γ' x ≡ clos L δ, which is obvious, but it requires some
  Agda shananigans via the kth-x lemma to get our hands on it.

* Case (↦-elim). We have γ ⊢ L · M ↓ v.
  The induction hypothesis for γ ⊢ L ↓ v₁ ↦ v
  gives us γ' ⊢ L ⇓ clos L' δ and 𝕍 v (clos L' δ).
  Of course, L' ≡ ƛ L'' for some L''.
  By the induction hypothesis for γ ⊢ M ↓ v₁,
  we have 𝔼 v₁ (clos M γ').
  Together with the premise AboveFun v and 𝕍 v (clos L' δ),
  we obtain a closure c' such that δ ⊢ L'' ⇓ c' and 𝕍 v c'.
  We conclude that γ' ⊢ L · M ⇓ c' by rule (⇓-app).

* Case (↦-intro). We have γ ⊢ ƛ M ↓ v ↦ v'.
  We immediately have γ' ⊢ ƛ M ⇓ clos (ƛ M) γ' by rule (⇓-lam).
  But we also need to prove 𝕍 (v ↦ v') (clos (ƛ M) γ').
  Let c by an arbitrary closure such that 𝔼 v c.
  Suppose v' is greater than a function value.
  We need to show that γ' , c ⊢ M ⇓ c' and 𝕍 v' c' for some c'.
  We prove this by the induction hypothesis for γ , v ⊢ M ↓ v'
  but we must first show that 𝔾 (γ , v) (γ' , c). We prove
  that by the lemma 𝔾-ext, using facts 𝔾 γ γ' and 𝔼 v c.

* Case (⊥-intro). We have the premise AboveFun ⊥, but that's impossible.

* Case (⊔-intro). We have γ ⊢ M ↓ (v₁ ⊔ v₂) and AboveFun (v₁ ⊔ v₂)
  and need to show γ' ⊢ M ↓ c and 𝕍 (v₁ ⊔ v₂) c for some c.
  Again, by AboveFun-⊔, at least one of v₁ or v₂ is greater than a function.

  * Suppose both v₁ and v₂ are greater than a function value.
    By the induction hypotheses for γ ⊢ M ↓ v₁ and γ ⊢ M ↓ v₂
    we have γ' ⊢ M ⇓ c₁, 𝕍 v₁ c₁, γ' ⊢ M ⇓ c₂, and 𝕍 v₂ c₂ for some c₁ and c₂.
    Because ⇓ is deterministic, we have c₂ ≡ c₁.
    Then by 𝕍⊔-intro we conclude that 𝕍 (v₁ ⊔ v₂) c₁.

  * Without loss of generality, suppose v₁ is greater than a function
    value but v₂ is not.  By the induction hypotheses for γ ⊢ M ↓ v₁,
    and using 𝕍→WHNF, we have γ' ⊢ M ⇓ clos (ƛ M'') γ₁
    and 𝕍 v₁ (clos (ƛ M'') γ₁).
    Then because v₂ is not greater than a function, we also have
    𝕍 v₂ (clos (ƛ M'') γ₁). We conclude that 𝕍 (v₁ ⊔ v₂) (clos (ƛ M'') γ₁).
    
* Case (sub). We have γ ⊢ M ↓ v, v' ⊑ v, and AboveFun v'.
  We need to show that γ' ⊢ M ⇓ c and 𝕍 v' c for some c.
  We have AboveFun v by AboveFun-⊑,
  so the induction hypothesis for γ ⊢ M ↓ v gives us a closure c
  such that γ' ⊢ M ⇓ c and 𝕍 v c. We conclude that 𝕍 v' c by sub-𝕍.


## Proof of denotational adequacy

The adequacy property is a corollary of the main lemma.
We have ∅ ⊢ ƛ N ↓ ⊥ ↦ ⊥, so ℰ M ≃ ℰ (ƛ N)
gives us ∅ ⊢ M ↓ ⊥ ↦ ⊥. Then the main lemma gives us ∅ ⊢ M ⇓ c for some c.

\begin{code}
adequacy : ∀{M : ∅ ⊢ ★}{N : ∅ , ★ ⊢ ★}  →  ℰ M ≃ ℰ (ƛ N)
         →  Σ[ c ∈ Clos ] ∅' ⊢ M ⇓ c
adequacy{M}{N} eq 
    with ↓→𝔼 𝔾-∅ ((proj₂ eq) (↦-intro ⊥-intro)) ⟨ ⊥ , ⟨ ⊥ , Refl⊑ ⟩ ⟩
... | ⟨ c , ⟨ M⇓c , Vc ⟩ ⟩ = ⟨ c , M⇓c ⟩
\end{code}
