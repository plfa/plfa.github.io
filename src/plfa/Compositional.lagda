---
title     : "Compositional: The denotational semantics is compositional"
layout    : page
prev      : /Denotational/
permalink : /Compositional/
next      : /Soundness/
---

\begin{code}
module plfa.Compositional where
\end{code}

## Imports

\begin{code}
open import plfa.Untyped
open import plfa.Denotational
open plfa.Denotational.≃-Reasoning

open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Data.Unit
\end{code}

## Semantic Equations

To prove that the denotational semantics is compositional, we need to
fill in the ellipses in the following equations.

    ℰ (ƛ M) ≃ ... ℰ M ...
    ℰ (M · N) ≃ ... ℰ M ... ℰ N ...

Regarding the first equation, we need a function that maps a
`Denotation (Γ , ★)` to a `Denotation Γ`. This function, let us name it `ℱ`,
should mimic the non-recursive part of the semantics when applied to a
lambda term.  In particular, we need to consider the rules `↦-intro`,
`⊥-intro`, and `⊔-intro`. So `ℱ` has three parameters, the denotation `D`
of the subterm `M`, an environment `γ`, and a value `v`.  If we define `ℱ` by
recursion on the value `v`, then it matches up nicely with the three
rules `↦-intro`, `⊥-intro`, and `⊔-intro`.

\begin{code}
ℱ : ∀{Γ} → Denotation (Γ , ★) → Denotation Γ
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)
\end{code}

Using this `ℱ`, we hope to prove that

    ℰ (ƛ N) ≃ ℱ (ℰ N)

The function `ℱ` is preserved when going from a larger value `v` to a
smaller value `u`. The proof is a straightforward induction on the
derivation of `u ⊑ v`, using the `up-env` lemma in the case for the
`Fun⊑` rule.

\begin{code}
sub-ℱ : ∀{Γ}{N : Γ , ★ ⊢ ★}{γ v u}
      → ℱ (ℰ N) γ v
      → u ⊑ v
        ------------
      → ℱ (ℰ N) γ u
sub-ℱ d Bot⊑ = tt
sub-ℱ d (Fun⊑ lt lt') = sub (up-env d lt) lt'
sub-ℱ d (ConjL⊑ lt lt₁) = ⟨ sub-ℱ d lt , sub-ℱ d lt₁ ⟩
sub-ℱ d (ConjR1⊑ lt) = sub-ℱ (proj₁ d) lt
sub-ℱ d (ConjR2⊑ lt) = sub-ℱ (proj₂ d) lt
sub-ℱ {v = v₁ ↦ v₂ ⊔ v₁ ↦ v₃} {v₁ ↦ (v₂ ⊔ v₃)} ⟨ N2 , N3 ⟩ Dist⊑ =
   ⊔-intro N2 N3
sub-ℱ d (Trans⊑ x₁ x₂) = sub-ℱ (sub-ℱ d x₂) x₁
\end{code}

[PLW:
  If denotations were strengthened to be downward closed,
  we could rewrite the signature replacing (ℰ N) by d : Denotation (Γ , ★)]
  
With this subsumption property in hand, we can prove the forward
direction of the semantic equation for lambda.  The proof is by
induction on the semantics, using `sub-ℱ` in the case for the `sub`
rule.

\begin{code}
ℰƛ→ℱℰ : ∀{Γ}{γ : Env Γ}{N : Γ , ★ ⊢ ★}{v : Value}
        → ℰ (ƛ N) γ v
          ------------
        → ℱ (ℰ N) γ v
ℰƛ→ℱℰ (↦-intro d) = d
ℰƛ→ℱℰ ⊥-intro = tt
ℰƛ→ℱℰ (⊔-intro d₁ d₂) = ⟨ ℰƛ→ℱℰ d₁ , ℰƛ→ℱℰ d₂ ⟩
ℰƛ→ℱℰ (sub d lt) = sub-ℱ (ℰƛ→ℱℰ d) lt
\end{code}

The "inversion lemma" for lambda abstraction is a special case of the
above. The inversion lemma is useful in proving that denotations are
preserved by reduction.

\begin{code}
lambda-inversion : ∀{Γ}{γ : Env Γ}{N : Γ , ★ ⊢ ★}{v₁ v₂ : Value}
  → γ ⊢ ƛ N ↓ v₁ ↦ v₂
    -----------------
  → (γ `, v₁) ⊢ N ↓ v₂
lambda-inversion{v₁ = v₁}{v₂ = v₂} d = ℰƛ→ℱℰ{v = v₁ ↦ v₂} d
\end{code}

The backward direction of the semantic equation for lambda is even
easier to prove than the forward direction. We proceed by induction on
the value v.

\begin{code}
ℱℰ→ℰƛ : ∀{Γ}{γ : Env Γ}{N : Γ , ★ ⊢ ★}{v : Value}
        → ℱ (ℰ N) γ v
          ------------
        → ℰ (ƛ N) γ v
ℱℰ→ℰƛ {v = ⊥} d = ⊥-intro
ℱℰ→ℰƛ {v = v₁ ↦ v₂} d = ↦-intro d
ℱℰ→ℰƛ {v = v₁ ⊔ v₂} ⟨ d1 , d2 ⟩ = ⊔-intro (ℱℰ→ℰƛ d1) (ℱℰ→ℰƛ d2)
\end{code}

So indeed, the denotational semantics is compositional with respect
to lambda abstraction, as witnessed by the function `ℱ`.

\begin{code}
lam-equiv : ∀{Γ}{N : Γ , ★ ⊢ ★}
          → ℰ (ƛ N) ≃ ℱ (ℰ N)
lam-equiv γ v = ⟨ ℰƛ→ℱℰ , ℱℰ→ℰƛ ⟩
\end{code}

Next we consider function application. For this we need to define a
function that takes two denotations, both in context `Γ`, and produces
another one in context `Γ`. This function, let us name it `●`, needs to
mimic the non-recursive aspects of the semantics of an application `L · M`.
We cannot proceed as easily as for `ℱ` and define the function by
recursion on value `v` because, for example, the rule `↦-elim` applies
to any value. Instead we shall define `●` in a way that directly deals
with the `↦-elim` and `⊥-intro` rules but ignores `⊔-intro`. This
makes the forward direction of the proof more difficult, and the case
for `⊔-intro` demonstrates why the `Dist⊑` rule is important.

So we define the application of `D₁` to `D₂`, written `D₁ ● D₂`, to include
any value `w` equivalent to `⊥`, for the `⊥-intro` rule, and to include any
value `w` that is the output of an entry `v ↦ w` in `D₁`, provided the
input `v` is in `D₂`, for the `↦-elim` rule.

\begin{code}
infixl 7 _●_

_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
(D₁ ● D₂) γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ]( D₁ γ (v ↦ w) × D₂ γ v )
\end{code}

Next we consider the inversion lemma for application, which is also
the forward direction of the semantic equation for application.  We
describe the proof below.

\begin{code}
ℰ·→●ℰ : ∀{Γ}{γ : Env Γ}{L M : Γ ⊢ ★}{v : Value}
        → ℰ (L · M) γ v
          ----------------
        → (ℰ L ● ℰ M) γ v
ℰ·→●ℰ (↦-elim{v = v'} d₁ d₂) = inj₂ ⟨ v' , ⟨ d₁ , d₂ ⟩ ⟩
ℰ·→●ℰ {v = ⊥} ⊥-intro = inj₁ Bot⊑
ℰ·→●ℰ {Γ}{γ}{L}{M}{v} (⊔-intro{v = v₁}{w = v₂} d₁ d₂) 
    with ℰ·→●ℰ d₁ | ℰ·→●ℰ d₂
... | inj₁ lt1 | inj₁ lt2 = inj₁ (ConjL⊑ lt1 lt2)    
... | inj₁ lt1 | inj₂ ⟨ v₁' , ⟨ L↓v12 , M↓v3 ⟩ ⟩ =
      inj₂ ⟨ v₁' , ⟨ sub L↓v12 lt , M↓v3 ⟩ ⟩
      where lt : v₁' ↦ (v₁ ⊔ v₂) ⊑ v₁' ↦ v₂
            lt = (Fun⊑ Refl⊑ (ConjL⊑ (Trans⊑ lt1 Bot⊑) Refl⊑))
... | inj₂ ⟨ v₁' , ⟨ L↓v12 , M↓v3 ⟩ ⟩ | inj₁ lt2 =
      inj₂ ⟨ v₁' , ⟨ sub L↓v12 lt , M↓v3 ⟩ ⟩
      where lt : v₁' ↦ (v₁ ⊔ v₂) ⊑ v₁' ↦ v₁
            lt = (Fun⊑ Refl⊑ (ConjL⊑ Refl⊑ (Trans⊑ lt2 Bot⊑)))
... | inj₂ ⟨ v₁' , ⟨ L↓v12 , M↓v3 ⟩ ⟩ | inj₂ ⟨ v₁'' , ⟨ L↓v12' , M↓v3' ⟩ ⟩ =
      let L↓⊔ = ⊔-intro L↓v12 L↓v12' in
      let M↓⊔ = ⊔-intro M↓v3 M↓v3' in
      let x = inj₂ ⟨ v₁' ⊔ v₁'' , ⟨ sub L↓⊔ Dist⊔↦⊔ , M↓⊔ ⟩ ⟩ in
      x
ℰ·→●ℰ {Γ}{γ}{L}{M}{v} (sub d lt)
    with ℰ·→●ℰ d
... | inj₁ lt2 = inj₁ (Trans⊑ lt lt2)
... | inj₂ ⟨ v₁ , ⟨ L↓v12 , M↓v3 ⟩ ⟩ =
      inj₂ ⟨ v₁ , ⟨ sub L↓v12 (Fun⊑ Refl⊑ lt) , M↓v3 ⟩ ⟩
\end{code}

We proceed by induction on the semantics.

* In case `↦-elim` we have `γ ⊢ L ↓ (v' ↦ v)` and `γ ⊢ M ↓ v'`,
  which is all we need to show `(ℰ L ● ℰ M) γ v`.

* In case `⊥-intro` we have `v = ⊥`. We conclude that `v ⊑ ⊥`.

* In case `⊔-intro` we have `ℰ (L · M) γ v₁` and `ℰ (L · M) γ v₂`
  and need to show `(ℰ L ● ℰ M) γ (v₁ ⊔ v₂)`. By the induction
  hypothesis, we have `(ℰ L ● ℰ M) γ v₁` and `(ℰ L ● ℰ M) γ v₂`.
  We have four subcases to consider.

    * Suppose `v₁ ⊑ ⊥` and `v₂ ⊑ ⊥`. Then `v₁ ⊔ v₂ ⊑ ⊥`.
    * Suppose `v₁ ⊑ ⊥`, `γ ⊢ L ↓ v₁' ↦ v₂`, and `γ ⊢ M ↓ v₁'`.
      We have `γ ⊢ L ↓ v₁' ↦ (v₁ ⊔ v₂)` by rule `sub`
      because `v₁' ↦ (v₁ ⊔ v₂) ⊑ v₁' ↦ v₂`.
    * Suppose `γ ⊢ L ↓ v₁' ↦ v₁`, `γ ⊢ M ↓ v₁'`, and `v₂ ⊑ ⊥`.
      We have `γ ⊢ L ↓ v₁' ↦ (v₁ ⊔ v₂)` by rule `sub`
      because `v₁' ↦ (v₁ ⊔ v₂) ⊑ v₁' ↦ v₁`.
    * Suppose `γ ⊢ L ↓ v₁'' ↦ v₁, γ ⊢ M ↓ v₁''`,
      `γ ⊢ L ↓ v₁' ↦ v₂`, and `γ ⊢ M ↓ v₁'`.
      This case is the most interesting.
      By two uses of the rule `⊔-intro` we have
      `γ ⊢ L ↓ (v₁' ↦ v₂) ⊔ (v₁'' ↦ v₁)` and
      `γ ⊢ M ↓ (v₁' ⊔ v₁'')`. But this does not yet match
      what we need for `ℰ L ● ℰ M` because the result of
      `L` must be an `↦` whose input entry is `v₁' ⊔ v₁''`.
      So we use the `sub` rule to obtain 
      `γ ⊢ L ↓ (v₁' ⊔ v₁'') ↦ (v₁ ⊔ v₂)`,
      using the `Dist⊔→⊔` lemma (thanks to the `Dist⊑` rule) to
      show that
   
            (v₁' ⊔ v₁'') ↦ (v₁ ⊔ v₂) ⊑ (v₁' ↦ v₂) ⊔ (v₁'' ↦ v₁)
   
      So we have proved what is needed for this case.

* In case `sub` we have `Γ ⊢ L · M ↓ v₁` and `v ⊑ v₁`.
  By the induction hypothesis, we have `(ℰ L ● ℰ M) γ v₁`.
  We have two subcases to consider.

    * Suppose `v₁ ⊑ ⊥`. We conclude that `v ⊑ ⊥`.
    * Suppose `Γ ⊢ L ↓ v' → v₁` and `Γ ⊢ M ↓ v'`.
      We conclude with `Γ ⊢ L ↓ v' → v` by rule `sub`, because
      `v' → v ⊑ v' → v₁`. 


The forward direction is proved by cases on the premise `(ℰ L ● ℰ M) γ v`.
In case `v ⊑ ⊥`, we obtain `Γ ⊢ L · M ↓ ⊥` by rule `⊥-intro`.
Otherwise, we conclude immediately by rule `↦-elim`.

\begin{code}
●ℰ→ℰ· : ∀{Γ}{γ : Env Γ}{L M : Γ ⊢ ★}{v}
      → (ℰ L ● ℰ M) γ v
        ----------------
      → ℰ (L · M) γ v
●ℰ→ℰ· {γ}{v} (inj₁ lt) = sub ⊥-intro lt
●ℰ→ℰ· {γ}{v} (inj₂ ⟨ v₁ , ⟨ d1 , d2 ⟩ ⟩) = ↦-elim d1 d2
\end{code}

So we have proved that the semantics is compositional with respect to
function application, as witnessed by the `●` function.

\begin{code}
app-equiv : ∀{Γ}{L M : Γ ⊢ ★}
          → ℰ (L · M) ≃ (ℰ L) ● (ℰ M)
app-equiv γ v = ⟨ ℰ·→●ℰ , ●ℰ→ℰ· ⟩ 
\end{code}

We also need an inversion lemma for variables.
If `Γ ⊢ x ↓ v`, then `v ⊑ nth x γ`. The proof is a straightforward
induction on the semantics.

\begin{code}
var-inv : ∀ {Γ v x} {γ : Env Γ}
  → ℰ (` x) γ v
    -------------------
  → v ⊑ γ x
var-inv (var) = Refl⊑
var-inv (⊔-intro d₁ d₂) = ConjL⊑ (var-inv d₁) (var-inv d₂)
var-inv (sub d lt) = Trans⊑ lt (var-inv d)
var-inv ⊥-intro = Bot⊑
\end{code}

To round-out the semantic equations, we establish the following one
for variables.

\begin{code}
var-equiv : ∀{Γ}{γ : Env Γ}{x : Γ ∋ ★}
          → ℰ (` x) ≃ (λ γ v → v ⊑ nth x γ)
var-equiv γ v = ⟨ var-inv , (λ lt → sub var lt) ⟩
\end{code}


## Congruence

The main work of this chapter is complete: we have established
semantic equations that show how the denotational semantics is
compositional. In this section and the next we make use of these
equations to prove some corollaries: that denotational equality is a
_congruence_ and to prove the _compositionality property_, which states
that surrounding two denotationally-equal terms in the same context
produces two programs that are denotationally equal.

We begin by showing that denotational equality is a congruence with
respect to lambda abstraction: that `ℰ N ≃ ℰ N'` implies `ℰ (ƛ N) ≃ ℰ
(ƛ N')`. We shall use the `lam-equiv` equation to reduce this question to
whether `ℱ` is a congruence.

\begin{code}
ℱ-cong : ∀{Γ}{D D' : Denotation (Γ , ★)}
       → D ≃ D'
         -----------
       → ℱ D ≃ ℱ D'
ℱ-cong{Γ} D≃D' γ v =
   ⟨ (λ x → ℱ≃{γ}{v} x D≃D') , (λ x → ℱ≃{γ}{v} x (≃-sym D≃D')) ⟩
   where 
   ℱ≃ : ∀{γ : Env Γ}{v}{D D' : Denotation (Γ , ★)}
      → ℱ D γ v  →  D ≃ D' → ℱ D' γ v
   ℱ≃ {v = ⊥} fd dd' = tt
   ℱ≃ {γ}{v ↦ w} fd dd' = proj₁ (dd' (γ `, v) w) fd
   ℱ≃ {γ}{u ⊔ w} fd dd' = ⟨ ℱ≃{γ}{u} (proj₁ fd) dd' , ℱ≃{γ}{w} (proj₂ fd) dd' ⟩
\end{code}

The proof of `ℱ-cong` uses the lemma `ℱ≃` to handle both directions of
the if-and-only-if. That lemma is proved by a straightforward
induction on the value `v`.

We now prove that lambda abstraction is a congruence by direct
equational reasoning.

\begin{code}
lam-cong : ∀{Γ}{N N' : Γ , ★ ⊢ ★}
         → ℰ N ≃ ℰ N'
           -----------------
         → ℰ (ƛ N) ≃ ℰ (ƛ N')
lam-cong {Γ}{N}{N'} N≃N' =
  start
  ℰ (ƛ N)
  ≃⟨ lam-equiv ⟩
  ℱ (ℰ N)
  ≃⟨ ℱ-cong N≃N' ⟩
  ℱ (ℰ N')
  ≃⟨ ≃-sym lam-equiv ⟩
  ℰ (ƛ N')
  ☐
\end{code}

Next we prove that denotational equality is a congruence for
application: that `ℰ L ≃ ℰ L'` and `ℰ M ≃ ℰ M'` imply
`ℰ (L · M) ≃ ℰ (L' · M')`. The `app-equiv` equation
reduces this to the question of whether the `●` operator
is a congruence.

\begin{code}
●-cong : ∀{Γ}{D₁ D₁' D₂ D₂' : Denotation Γ}
   → D₁ ≃ D₁' → D₂ ≃ D₂'
   → (D₁ ● D₂) ≃ (D₁' ● D₂')
●-cong {Γ} d1 d2 γ v = ⟨ (λ x → ●≃ x d1 d2) ,
                         (λ x → ●≃ x (≃-sym d1) (≃-sym d2)) ⟩
   where
   ●≃ : ∀{γ : Env Γ}{v}{D₁ D₁' D₂ D₂' : Denotation Γ}
      → (D₁ ● D₂) γ v  →  D₁ ≃ D₁'  →  D₂ ≃ D₂'
      → (D₁' ● D₂') γ v
   ●≃ (inj₁ v⊑⊥) eq₁ eq₂ = inj₁ v⊑⊥
   ●≃ {γ} {w} (inj₂ ⟨ v , ⟨ Dv↦w , Dv ⟩ ⟩) eq₁ eq₂ =
      inj₂ ⟨ v , ⟨ proj₁ (eq₁ γ (v ↦ w)) Dv↦w , proj₁ (eq₂ γ v) Dv ⟩ ⟩
\end{code}

Again, both directions of the if-and-only-if are proved via a lemma.
This time the lemma is proved by cases on `(D₁ ● D₂) γ v`.

With the congruence of `●`, we can prove that application is a
congruence by direct equational reasoning.

\begin{code}
app-cong : ∀{Γ}{L L' M M' : Γ ⊢ ★}
         → ℰ L ≃ ℰ L'
         → ℰ M ≃ ℰ M'
           -------------------------
         → ℰ (L · M) ≃ ℰ (L' · M')
app-cong {Γ}{L}{L'}{M}{M'} L≅L' M≅M' =
  start
  ℰ (L · M)
  ≃⟨ app-equiv ⟩
  ℰ L ● ℰ M
  ≃⟨ ●-cong L≅L' M≅M' ⟩
  ℰ L' ● ℰ M'
  ≃⟨ ≃-sym app-equiv ⟩  
  ℰ (L' · M')
  ☐
\end{code}


## Compositionality

The _compositionality property_ states that surrounding two terms that
are denotationally equal in the same context produces two programs
that are denotationally equal. To make this precise, we define what we
mean by "context" and "surround".

A _context_ is a program with one hole in it. The following data
definition `Ctx` makes this idea explicit. We index the `Ctx` data
type with two contexts for variables: one for the the hole and one for
terms that result from filling the hole.

\begin{code}
data Ctx : Context → Context → Set where
  CHole : ∀{Γ} → Ctx Γ Γ
  CLam :  ∀{Γ Δ} → Ctx (Γ , ★) (Δ , ★) → Ctx (Γ , ★) Δ
  CAppL : ∀{Γ Δ} → Ctx Γ Δ → Δ ⊢ ★ → Ctx Γ Δ
  CAppR : ∀{Γ Δ} → Δ ⊢ ★ → Ctx Γ Δ → Ctx Γ Δ
\end{code}

* The constructor `CHole` represents the hole, and in this case the
  variable context for the hole is the same as the variable context
  for the term that results from filling the hole.

* The constructor `CLam` takes a `Ctx` and produces a larger one that
  adds a lambda abstraction at the top. The variable context of the
  hole stays the same, whereas we remove one variable from the context
  of the resulting term because it is bound by this lambda
  abstraction.

* There are two constructions for application, `CAppL` and
  `CAppR`. The `CAppL` is for when the hole is inside the left-hand
  term (the operator) and the later is when the hole is inside the
  right-hand term (the operand).
  
The action of surrounding a term with a context is defined by the
following `plug` function. It is defined by recursion on the context.

\begin{code}
plug : ∀{Γ}{Δ} → Ctx Γ Δ → Γ ⊢ ★ → Δ ⊢ ★
plug CHole M = M
plug (CLam C) N = ƛ plug C N
plug (CAppL C N) L = (plug C L) · N
plug (CAppR L C) M = L · (plug C M)
\end{code}

We are ready to state and prove the compositionality principle.  Given
two terms `M` and `N` that are denotationally equal, plugging them both
into an arbitrary context `C` produces two programs that are
denotationally equal.

\begin{code}
compositionality : ∀{Γ Δ}{C : Ctx Γ Δ} {M N : Γ ⊢ ★}
              → ℰ M ≃ ℰ N
                ---------------------------
              → ℰ (plug C M) ≃ ℰ (plug C N)
compositionality {C = CHole} M≃N =
   M≃N
compositionality {C = CLam C'} M≃N =
   lam-cong (compositionality {C = C'} M≃N)
compositionality {C = CAppL C' L} M≃N =
   app-cong (compositionality {C = C'} M≃N) λ γ v → ⟨ (λ x → x) , (λ x → x) ⟩
compositionality {C = CAppR L C'} M≃N =
   app-cong (λ γ v → ⟨ (λ x → x) , (λ x → x) ⟩) (compositionality {C = C'} M≃N) 
\end{code}

The proof is a straightforward induction on the context `C`, using the
congruence properties `lam-cong` and `app-cong` that we established
above.
