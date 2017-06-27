---
title     : "StlcProp: Properties of STLC"
layout    : page
permalink : /StlcProp
---

\begin{code}
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃₂; _,_; ,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)
open import Maps
open Maps.PartialMap
open import Stlc
\end{code}

In this chapter, we develop the fundamental theory of the Simply
Typed Lambda Calculus---in particular, the type safety
theorem.


## Canonical Forms

As we saw for the simple calculus in the [Stlc]({{ "Stlc" | relative_url }})
chapter, the first step in establishing basic properties of reduction and types
is to identify the possible _canonical forms_ (i.e., well-typed closed values)
belonging to each type.  For `bool`, these are the boolean values `true` and
`false`.  For arrow types, the canonical forms are lambda-abstractions. 

\begin{code}
data canonical_for_ : Term → Type → Set where
  canonical-λᵀ : ∀ {x A N B} → canonical (λᵀ x ∈ A ⇒ N) for (A ⇒ B)
  canonical-trueᵀ : canonical trueᵀ for 𝔹
  canonical-falseᵀ : canonical falseᵀ for 𝔹
  
-- canonical_for_ : Term → Type → Set
-- canonical L for 𝔹       = L ≡ trueᵀ ⊎ L ≡ falseᵀ
-- canonical L for (A ⇒ B) = ∃₂ λ x N → L ≡ λᵀ x ∈ A ⇒ N

canonicalFormsLemma : ∀ {L A} → ∅ ⊢ L ∈ A → value L → canonical L for A
canonicalFormsLemma (Ax ⊢x) ()
canonicalFormsLemma (⇒-I ⊢N) value-λᵀ = canonical-λᵀ      -- _ , _ , refl
canonicalFormsLemma (⇒-E ⊢L ⊢M) ()
canonicalFormsLemma 𝔹-I₁ value-trueᵀ = canonical-trueᵀ    -- inj₁ refl
canonicalFormsLemma 𝔹-I₂ value-falseᵀ = canonical-falseᵀ  -- inj₂ refl
canonicalFormsLemma (𝔹-E ⊢L ⊢M ⊢N) ()
\end{code}

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term is a value, or it
can take a reduction step.  The proof is a relatively
straightforward extension of the progress proof we saw in the
[Stlc]({{ "Stlc" | relative_url }}) chapter.  We'll give the proof in English
first, then the formal version.

\begin{code}
progress : ∀ {M A} → ∅ ⊢ M ∈ A → value M ⊎ ∃ λ N → M ⟹ N
\end{code}

_Proof_: By induction on the derivation of `\vdash t : A`.

  - The last rule of the derivation cannot be `var`,
    since a variable is never well typed in an empty context.

  - The `true`, `false`, and `abs` cases are trivial, since in
    each of these cases we can see by inspecting the rule that `t`
    is a value.

  - If the last rule of the derivation is `app`, then `t` has the
    form `t_1\;t_2` for som e`t_1` and `t_2`, where we know that
    `t_1` and `t_2` are also well typed in the empty context; in particular,
    there exists a type `B` such that `\vdash t_1 : A\to T` and
    `\vdash t_2 : B`.  By the induction hypothesis, either `t_1` is a
    value or it can take a reduction step.

  - If `t_1` is a value, then consider `t_2`, which by the other
    induction hypothesis must also either be a value or take a step.

    - Suppose `t_2` is a value.  Since `t_1` is a value with an
      arrow type, it must be a lambda abstraction; hence `t_1\;t_2`
      can take a step by `red`.

    - Otherwise, `t_2` can take a step, and hence so can `t_1\;t_2`
      by `app2`.

  - If `t_1` can take a step, then so can `t_1 t_2` by `app1`.

  - If the last rule of the derivation is `if`, then `t = \text{if }t_1
    \text{ then }t_2\text{ else }t_3`, where `t_1` has type `bool`.  By
    the IH, `t_1` either is a value or takes a step.

  - If `t_1` is a value, then since it has type `bool` it must be
    either `true` or `false`.  If it is `true`, then `t` steps
    to `t_2`; otherwise it steps to `t_3`.

  - Otherwise, `t_1` takes a step, and therefore so does `t` (by `if`).

\begin{code}
progress (Ax ())
progress (⇒-I ⊢N) = inj₁ value-λᵀ
progress (⇒-E {Γ} {L} {M} {A} {B} ⊢L ⊢M) with progress ⊢L
... | inj₂ (L′ , L⟹L′) = inj₂ (L′ ·ᵀ M , γ⇒₁ L⟹L′)
... | inj₁ valueL with progress ⊢M
... | inj₂ (M′ , M⟹M′) = inj₂ (L ·ᵀ M′ , γ⇒₂ valueL M⟹M′)
... | inj₁ valueM with canonicalFormsLemma ⊢L valueL
... | canonical-λᵀ {x} {.A} {N} {.B} = inj₂ ((N [ x := M ]) , β⇒ valueM)
progress 𝔹-I₁ = inj₁ value-trueᵀ
progress 𝔹-I₂ = inj₁ value-falseᵀ
progress (𝔹-E {Γ} {L} {M} {N} {A} ⊢L ⊢M ⊢N) with progress ⊢L
... | inj₂ (L′ , L⟹L′) = inj₂ ((ifᵀ L′ then M else N) , γ𝔹 L⟹L′)
... | inj₁ valueL with canonicalFormsLemma ⊢L valueL
... | canonical-trueᵀ = inj₂ (M , β𝔹₁)
... | canonical-falseᵀ = inj₂ (N , β𝔹₂)
\end{code}

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

\begin{code}
postulate
  progress′ : ∀ {M A} → ∅ ⊢ M ∈ A → value M ⊎ ∃ λ N → M ⟹ N
\end{code}

## Preservation

The other half of the type soundness property is the preservation
of types during reduction.  For this, we need to develop some
technical machinery for reasoning about variables and
substitution.  Working from top to bottom (from the high-level
property we are actually interested in to the lowest-level
technical lemmas that are needed by various cases of the more
interesting proofs), the story goes like this:

  - The _preservation theorem_ is proved by induction on a typing
    derivation, pretty much as we did in the [Stlc]({{ "Stlc" | relative_url }})
    chapter.  The one case that is significantly different is the one for the
    `red` rule, whose definition uses the substitution operation.  To see that
    this step preserves typing, we need to know that the substitution itself
    does.  So we prove a... 

  - _substitution lemma_, stating that substituting a (closed)
    term `s` for a variable `x` in a term `t` preserves the type
    of `t`.  The proof goes by induction on the form of `t` and
    requires looking at all the different cases in the definition
    of substitition.  This time, the tricky cases are the ones for
    variables and for function abstractions.  In both cases, we
    discover that we need to take a term `s` that has been shown
    to be well-typed in some context `\Gamma` and consider the same
    term `s` in a slightly different context `\Gamma'`.  For this
    we prove a...

  - _context invariance_ lemma, showing that typing is preserved
    under "inessential changes" to the context `\Gamma`---in
    particular, changes that do not affect any of the free
    variables of the term.  And finally, for this, we need a
    careful definition of...

  - the _free variables_ of a term---i.e., those variables
    mentioned in a term and not in the scope of an enclosing
    function abstraction binding a variable of the same name.

To make Agda happy, we need to formalize the story in the opposite
order...


### Free Occurrences

A variable `x` _appears free in_ a term `M` if `M` contains some
occurrence of `x` that is not under an abstraction over `x`.
For example:

  - `y` appears free, but `x` does not, in `λᵀ x ∈ (A ⇒ B) ⇒ x ·ᵀ y`
  - both `x` and `y` appear free in `(λᵀ x ∈ (A ⇒ B) ⇒ x ·ᵀ y) ·ᵀ x`
  - no variables appear free in `λᵀ x ∈ (A ⇒ B) ⇒ (λᵀ y ∈ A ⇒ x ·ᵀ y)`

Formally:

\begin{code}
data _FreeIn_ : Id → Term → Set where
  free-varᵀ  : ∀ {x} → x FreeIn (varᵀ x)
  free-λᵀ  : ∀ {x y A N} → y ≢ x → x FreeIn N → x FreeIn (λᵀ y ∈ A ⇒ N)
  free-·ᵀ₁ : ∀ {x L M} → x FreeIn L → x FreeIn (L ·ᵀ M)
  free-·ᵀ₂ : ∀ {x L M} → x FreeIn M → x FreeIn (L ·ᵀ M)
  free-ifᵀ₁ : ∀ {x L M N} → x FreeIn L → x FreeIn (ifᵀ L then M else N)
  free-ifᵀ₂ : ∀ {x L M N} → x FreeIn M → x FreeIn (ifᵀ L then M else N)
  free-ifᵀ₃ : ∀ {x L M N} → x FreeIn N → x FreeIn (ifᵀ L then M else N)
\end{code}

A term in which no variables appear free is said to be _closed_.

\begin{code}
closed : Term → Set
closed M = ∀ {x} → ¬ (x FreeIn M)
\end{code}

#### Exercise: 1 star (free-in)
If the definition of `_FreeIn_` is not crystal clear to
you, it is a good idea to take a piece of paper and write out the
rules in informal inference-rule notation.  (Although it is a
rather low-level, technical definition, understanding it is
crucial to understanding substitution and its properties, which
are really the crux of the lambda-calculus.)

### Substitution
To prove that substitution preserves typing, we first need a
technical lemma connecting free variables and typing contexts: If
a variable `x` appears free in a term `M`, and if we know `M` is
well typed in context `Γ`, then it must be the case that
`Γ` assigns a type to `x`.

\begin{code}
freeLemma : ∀ {x M A Γ} → x FreeIn M → Γ ⊢ M ∈ A → ∃ λ B → Γ x ≡ just B
\end{code}

_Proof_: We show, by induction on the proof that `x` appears
  free in `P`, that, for all contexts `Γ`, if `P` is well
  typed under `Γ`, then `Γ` assigns some type to `x`.

  - If the last rule used was `free-varᵀ`, then `P = x`, and from
    the assumption that `M` is well typed under `Γ` we have
    immediately that `Γ` assigns a type to `x`.

  - If the last rule used was `free-·₁`, then `P = L ·ᵀ M` and `x`
    appears free in `L`.  Since `L` is well typed under `\Gamma`,
    we can see from the typing rules that `L` must also be, and
    the IH then tells us that `Γ` assigns `x` a type.

  - Almost all the other cases are similar: `x` appears free in a
    subterm of `P`, and since `P` is well typed under `Γ`, we
    know the subterm of `M` in which `x` appears is well typed
    under `Γ` as well, and the IH gives us exactly the
    conclusion we want.

  - The only remaining case is `free-λᵀ`.  In this case `P =
    λᵀ y ∈ A ⇒ N`, and `x` appears free in `N`; we also know that
    `x` is different from `y`.  The difference from the previous
    cases is that whereas `P` is well typed under `\Gamma`, its
    body `N` is well typed under `(Γ , y ↦ A)`, so the IH
    allows us to conclude that `x` is assigned some type by the
    extended context `(Γ , y ↦ A)`.  To conclude that `Γ`
    assigns a type to `x`, we appeal the decidable equality for names
    `_≟_`, noting that `x` and `y` are different variables.

\begin{code}
freeLemma free-varᵀ (Ax Γx≡justA) = (_ , Γx≡justA)
freeLemma (free-·ᵀ₁ x∈L) (⇒-E ⊢L ⊢M) = freeLemma x∈L ⊢L
freeLemma (free-·ᵀ₂ x∈M) (⇒-E ⊢L ⊢M) = freeLemma x∈M ⊢M
freeLemma (free-ifᵀ₁ x∈L) (𝔹-E ⊢L ⊢M ⊢N) = freeLemma x∈L ⊢L
freeLemma (free-ifᵀ₂ x∈M) (𝔹-E ⊢L ⊢M ⊢N) = freeLemma x∈M ⊢M
freeLemma (free-ifᵀ₃ x∈N) (𝔹-E ⊢L ⊢M ⊢N) = freeLemma x∈N ⊢N
freeLemma (free-λᵀ {x} {y} y≢x x∈N) (⇒-I ⊢N) with freeLemma x∈N ⊢N
... | Γx=justC with y ≟ x
... | yes y≡x = ⊥-elim (y≢x y≡x)
... | no  _   = Γx=justC
\end{code}

[A subtle point: if the first argument of `free-λᵀ` was of type
`x ≢ y` rather than of type `y ≢ x`, then the type of the
term `Γx=justC` would not simplify properly.]

Next, we'll need the fact that any term `M` which is well typed in
the empty context is closed (it has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

\begin{code}
postulate
  ∅⊢-closed : ∀ {M A} → ∅ ⊢ M ∈ A → closed M
\end{code}

<div class="hidden">
\begin{code}
contradiction : ∀ {X : Set} → ∀ {x : X} → ¬ (_≡_ {A = Maybe X} (just x) nothing)
contradiction ()

∅⊢-closed′ : ∀ {M A} → ∅ ⊢ M ∈ A → closed M
∅⊢-closed′ {M} {A} ⊢M {x} x∈M with freeLemma x∈M ⊢M
... | (B , ∅x≡justB) = contradiction (trans (sym ∅x≡justB) (apply-∅ x))
\end{code}
</div>

Sometimes, when we have a proof `Γ ⊢ M ∈ A`, we will need to
replace `Γ` by a different context `Γ′`.  When is it safe
to do this?  Intuitively, it must at least be the case that
`Γ′` assigns the same types as `Γ` to all the variables
that appear free in `M`. In fact, this is the only condition that
is needed.

\begin{code}
weaken : ∀ {Γ Γ′ M A}
        → (∀ {x} → x FreeIn M → Γ x ≡ Γ′ x)
        → Γ  ⊢ M ∈ A
        → Γ′ ⊢ M ∈ A
\end{code}

_Proof_: By induction on the derivation of
`Γ ⊢ M ∈ A`.

  - If the last rule in the derivation was `var`, then `t = x`
    and `\Gamma x = T`.  By assumption, `\Gamma' x = T` as well, and
    hence `\Gamma' \vdash t : T` by `var`.

  - If the last rule was `abs`, then `t = \lambda y:A. t'`, with
    `T = A\to B` and `\Gamma, y : A \vdash t' : B`.  The
    induction hypothesis is that, for any context `\Gamma''`, if
    `\Gamma, y:A` and `\Gamma''` assign the same types to all the
    free variables in `t'`, then `t'` has type `B` under
    `\Gamma''`.  Let `\Gamma'` be a context which agrees with
    `\Gamma` on the free variables in `t`; we must show
    `\Gamma' \vdash \lambda y:A. t' : A\to B`.

    By `abs`, it suffices to show that `\Gamma', y:A \vdash t' : t'`.
    By the IH (setting `\Gamma'' = \Gamma', y:A`), it suffices to show
    that `\Gamma, y:A` and `\Gamma', y:A` agree on all the variables
    that appear free in `t'`.

    Any variable occurring free in `t'` must be either `y` or
    some other variable.  `\Gamma, y:A` and `\Gamma', y:A`
    clearly agree on `y`.  Otherwise, note that any variable other
    than `y` that occurs free in `t'` also occurs free in
    `t = \lambda y:A. t'`, and by assumption `\Gamma` and
    `\Gamma'` agree on all such variables; hence so do `\Gamma, y:A` and
    `\Gamma', y:A`.

  - If the last rule was `app`, then `t = t_1\;t_2`, with
    `\Gamma \vdash t_1:A\to T` and `\Gamma \vdash t_2:A`.
    One induction hypothesis states that for all contexts `\Gamma'`,
    if `\Gamma'` agrees with `\Gamma` on the free variables in `t_1`,
    then `t_1` has type `A\to T` under `\Gamma'`; there is a similar IH
    for `t_2`.  We must show that `t_1\;t_2` also has type `T` under
    `\Gamma'`, given the assumption that `\Gamma'` agrees with
    `\Gamma` on all the free variables in `t_1\;t_2`.  By `app`, it
    suffices to show that `t_1` and `t_2` each have the same type
    under `\Gamma'` as under `\Gamma`.  But all free variables in
    `t_1` are also free in `t_1\;t_2`, and similarly for `t_2`;
    hence the desired result follows from the induction hypotheses.

\begin{code}
weaken Γ~Γ′ (Ax Γx≡justA) rewrite (Γ~Γ′ free-varᵀ) = Ax Γx≡justA
weaken {Γ} {Γ′} {λᵀ x ∈ A ⇒ N} Γ~Γ′ (⇒-I ⊢N) = ⇒-I (weaken Γx~Γ′x ⊢N)
  where
  Γx~Γ′x : ∀ {y} → y FreeIn N → (Γ , x ↦ A) y ≡ (Γ′ , x ↦ A) y
  Γx~Γ′x {y} y∈N with x ≟ y
  ... | yes refl = refl
  ... | no  x≢y  = Γ~Γ′ (free-λᵀ x≢y y∈N)
weaken Γ~Γ′ (⇒-E ⊢L ⊢M) = ⇒-E (weaken (Γ~Γ′ ∘ free-·ᵀ₁)  ⊢L) (weaken (Γ~Γ′ ∘ free-·ᵀ₂) ⊢M) 
weaken Γ~Γ′ 𝔹-I₁ = 𝔹-I₁
weaken Γ~Γ′ 𝔹-I₂ = 𝔹-I₂
weaken Γ~Γ′ (𝔹-E ⊢L ⊢M ⊢N)
  = 𝔹-E (weaken (Γ~Γ′ ∘ free-ifᵀ₁) ⊢L) (weaken (Γ~Γ′ ∘ free-ifᵀ₂) ⊢M) (weaken (Γ~Γ′ ∘ free-ifᵀ₃) ⊢N)

{-
replaceCtxt f (var x x∶A
) rewrite f var = var x x∶A
replaceCtxt f (app t₁∶A⇒B t₂∶A)
  = app (replaceCtxt (f ∘ app1) t₁∶A⇒B) (replaceCtxt (f ∘ app2) t₂∶A)
replaceCtxt {Γ} {Γ′} f (abs {.Γ} {x} {A} {B} {t′} t′∶B)
  = abs (replaceCtxt f′ t′∶B)
  where
    f′ : ∀ {y} → y FreeIn t′ → (Γ , x ∶ A) y ≡ (Γ′ , x ∶ A) y
    f′ {y} y∈t′ with x ≟ y
    ... | yes _   = refl
    ... | no  x≠y = f (abs x≠y y∈t′)
replaceCtxt _ true  = true
replaceCtxt _ false = false
replaceCtxt f (if t₁∶bool then t₂∶A else t₃∶A)
  = if   replaceCtxt (f ∘ if1) t₁∶bool
    then replaceCtxt (f ∘ if2) t₂∶A
    else replaceCtxt (f ∘ if3) t₃∶A
-}
\end{code}


Now we come to the conceptual heart of the proof that reduction
preserves types---namely, the observation that _substitution_
preserves types.

Formally, the so-called _Substitution Lemma_ says this: Suppose we
have a term `N` with a free variable `x`, and suppose we've been
able to assign a type `B` to `N` under the assumption that `x` has
some type `A`.  Also, suppose that we have some other term `V` and
that we've shown that `V` has type `A`.  Then, since `V` satisfies
the assumption we made about `x` when typing `N`, we should be
able to substitute `V` for each of the occurrences of `x` in `N`
and obtain a new term that still has type `B`.

_Lemma_: If `Γ , x ↦ A ⊢ N ∈ B` and `∅ ⊢ V ∈ A`, then
`Γ ⊢ (N [ x := V ]) ∈ B`.

\begin{code}
preservation-[:=] : ∀ {Γ x A N B V}
                 → (Γ , x ↦ A) ⊢ N ∈ B
                 → ∅ ⊢ V ∈ A
                 → Γ ⊢ (N [ x := V ]) ∈ B
\end{code}

One technical subtlety in the statement of the lemma is that
we assign `V` the type `A` in the _empty_ context---in other
words, we assume `V` is closed.  This assumption considerably
simplifies the `λᵀ` case of the proof (compared to assuming
`Γ ⊢ V ∈ A`, which would be the other reasonable assumption
at this point) because the context invariance lemma then tells us
that `V` has type `A` in any context at all---we don't have to
worry about free variables in `V` clashing with the variable being
introduced into the context by `λᵀ`.

The substitution lemma can be viewed as a kind of "commutation"
property.  Intuitively, it says that substitution and typing can
be done in either order: we can either assign types to the terms
`N` and `V` separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to `N [ x := V ]`---the result is the same either
way.

_Proof_: We show, by induction on `N`, that for all `A` and
`Γ`, if `Γ , x ↦ A \vdash N ∈ B` and `∅ ⊢ V ∈ A`, then
`Γ \vdash N [ x := V ] ∈ B`.

  - If `N` is a variable there are two cases to consider,
    depending on whether `N` is `x` or some other variable.

      - If `N = varᵀ x`, then from the fact that `Γ , x ↦ A ⊢ N ∈ B`
        we conclude that `A = B`.  We must show that `x [ x := V] =
        V` has type `A` under `Γ`, given the assumption that
        `V` has type `A` under the empty context.  This
        follows from context invariance: if a closed term has type
        `A` in the empty context, it has that type in any context.

      - If `N` is some variable `x′` different from `x`, then
        we need only note that `x′` has the same type under `Γ , x ↦ A`
        as under `Γ`.

  - If `N` is an abstraction `λᵀ x′ ∈ A′ ⇒ N′`, then the IH tells us,
    for all `Γ′`́ and `B′`, that if `Γ′ , x ↦ A ⊢ N′ ∈ B′`
    and `∅ ⊢ V ∈ A`, then `Γ′ ⊢ N′ [ x := V ] ∈ B′`.

    The substitution in the conclusion behaves differently
    depending on whether `x` and `x′` are the same variable.

    First, suppose `x ≡ x′`.  Then, by the definition of
    substitution, `N [ x := V] = N`, so we just need to show `Γ ⊢ N ∈ B`.
    But we know `Γ , x ↦ A ⊢ N ∈ B` and, since `x ≡ x′`
    does not appear free in `λᵀ x′ ∈ A′ ⇒ N′`, the context invariance
    lemma yields `Γ ⊢ N ∈ B`.

    Second, suppose `x ≢ x′`.  We know `Γ , x ↦ A , x′ ↦ A′ ⊢ N′ ∈ B′`
    by inversion of the typing relation, from which
    `Γ , x′ ↦ A′ , x ↦ A ⊢ N′ ∈ B′` follows by update permute,
    so the IH applies, giving us `Γ , x′ ↦ A′ ⊢ N′ [ x := V ] ∈ B′`
    By `⇒-I`, we have `Γ ⊢ λᵀ x′ ∈ A′ ⇒ (N′ [ x := V ]) ∈ A′ ⇒ B′`
    and the definition of substitution (noting `x ≢ x′`) gives
    `Γ ⊢ (λᵀ x′ ∈ A′ ⇒ N′) [ x := V ] ∈ A′ ⇒ B′` as required.

  - If `N` is an application `L′ ·ᵀ M′`, the result follows
    straightforwardly from the definition of substitution and the
    induction hypotheses.

  - The remaining cases are similar to the application case.

We need a couple of lemmas. A closed term can be weakened to any context, and just is injective.
\begin{code}
weaken-closed : ∀ {V A Γ} → ∅ ⊢ V ∈ A → Γ ⊢ V ∈ A
weaken-closed {V} {A} {Γ} ⊢V = weaken Γ~Γ′ ⊢V
  where
  Γ~Γ′ : ∀ {x} → x FreeIn V → ∅ x ≡ Γ x
  Γ~Γ′ {x} x∈V = ⊥-elim (x∉V x∈V)
    where
    x∉V : ¬ (x FreeIn V)
    x∉V = ∅⊢-closed ⊢V {x}

just-injective : ∀ {X : Set} {x y : X} → _≡_ {A = Maybe X} (just x) (just y) → x ≡ y
just-injective refl = refl
\end{code}

\begin{code}
preservation-[:=] {_} {x} (Ax {_} {x′} [Γ,x↦A]x′≡B) ⊢V with x ≟ x′
...| yes x≡x′ rewrite just-injective [Γ,x↦A]x′≡B  =  weaken-closed ⊢V
...| no  x≢x′  =  Ax [Γ,x↦A]x′≡B
preservation-[:=] {Γ} {x} {A} {λᵀ x′ ∈ A′ ⇒ N′} {.A′ ⇒ B′} {V} (⇒-I ⊢N′) ⊢V with x ≟ x′
...| yes x≡x′ rewrite x≡x′ = weaken Γ′~Γ (⇒-I ⊢N′)
  where
  Γ′~Γ : ∀ {y} → y FreeIn (λᵀ x′ ∈ A′ ⇒ N′) → (Γ , x′ ↦ A) y ≡ Γ y
  Γ′~Γ {y} (free-λᵀ x′≢y y∈N′) with x′ ≟ y
  ...| yes x′≡y  = ⊥-elim (x′≢y x′≡y)
  ...| no  _     = refl
...| no  x≢x′ = ⇒-I ⊢N′V
  where
  x′x⊢N′ : Γ , x′ ↦ A′ , x ↦ A ⊢ N′ ∈ B′
  x′x⊢N′ rewrite update-permute Γ x A x′ A′ x≢x′ = ⊢N′
  ⊢N′V : (Γ , x′ ↦ A′) ⊢ N′ [ x := V ] ∈ B′
  ⊢N′V = preservation-[:=] x′x⊢N′ ⊢V
preservation-[:=] (⇒-E ⊢L ⊢M) ⊢V = ⇒-E (preservation-[:=] ⊢L ⊢V) (preservation-[:=] ⊢M ⊢V)
preservation-[:=] 𝔹-I₁ ⊢V = 𝔹-I₁
preservation-[:=] 𝔹-I₂ ⊢V = 𝔹-I₂
preservation-[:=] (𝔹-E ⊢L ⊢M ⊢N) ⊢V =
  𝔹-E (preservation-[:=] ⊢L ⊢V) (preservation-[:=] ⊢M ⊢V) (preservation-[:=] ⊢N ⊢V)
\end{code}


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

\begin{code}
preservation : ∀ {M N A} → ∅ ⊢ M ∈ A → M ⟹ N → ∅ ⊢ N ∈ A
\end{code}

_Proof_: By induction on the derivation of `\vdash t : T`.

- We can immediately rule out `var`, `abs`, `T_True`, and
  `T_False` as the final rules in the derivation, since in each of
  these cases `t` cannot take a step.

- If the last rule in the derivation was `app`, then `t = t_1
  t_2`.  There are three cases to consider, one for each rule that
  could have been used to show that `t_1 t_2` takes a step to `t'`.

    - If `t_1 t_2` takes a step by `Sapp1`, with `t_1` stepping to
      `t_1'`, then by the IH `t_1'` has the same type as `t_1`, and
      hence `t_1' t_2` has the same type as `t_1 t_2`.

    - The `Sapp2` case is similar.

    - If `t_1 t_2` takes a step by `Sred`, then `t_1 =
      \lambda x:t_{11}.t_{12}` and `t_1 t_2` steps to ``x:=t_2`t_{12}`; the
      desired result now follows from the fact that substitution
      preserves types.

    - If the last rule in the derivation was `if`, then `t = if t_1
      then t_2 else t_3`, and there are again three cases depending on
      how `t` steps.

    - If `t` steps to `t_2` or `t_3`, the result is immediate, since
      `t_2` and `t_3` have the same type as `t`.

    - Otherwise, `t` steps by `Sif`, and the desired conclusion
      follows directly from the induction hypothesis.

\begin{code}
preservation (Ax x₁) ()
preservation (⇒-I ⊢N) ()
preservation (⇒-E (⇒-I ⊢N) ⊢V) (β⇒ valueV) = preservation-[:=] ⊢N ⊢V
preservation (⇒-E ⊢L ⊢M) (γ⇒₁ L⟹L′) with preservation ⊢L L⟹L′
...| ⊢L′ = ⇒-E ⊢L′ ⊢M
preservation (⇒-E ⊢L ⊢M) (γ⇒₂ valueL M⟹M′) with preservation ⊢M M⟹M′
...| ⊢M′ = ⇒-E ⊢L ⊢M′
preservation 𝔹-I₁ ()
preservation 𝔹-I₂ ()
preservation (𝔹-E 𝔹-I₁ ⊢M ⊢N) β𝔹₁ = ⊢M
preservation (𝔹-E 𝔹-I₂ ⊢M ⊢N) β𝔹₂ = ⊢N
preservation (𝔹-E ⊢L ⊢M ⊢N) (γ𝔹 L⟹L′) with preservation ⊢L L⟹L′
...| ⊢L′ = 𝔹-E ⊢L′ ⊢M ⊢N

-- Writing out implicit parameters in full
-- preservation (⇒-E {Γ} {λᵀ x ∈ A ⇒ N} {M} {.A} {B} (⇒-I {.Γ} {.x} {.N} {.A} {.B} ⊢N) ⊢M) (β⇒ {.x} {.A} {.N} {.M} valueM)
--  =  preservation-[:=] {Γ} {x} {A} {M} {N} {B} ⊢M ⊢N
\end{code}

Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Gamma; subst;
       try solve `inversion HE; subst; auto`.
  - (* app
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and `eauto` takes care of them
    + (* Sred
      apply substitution_preserves_typing with t_{11}...
      inversion HT_1...
Qed.

#### Exercise: 2 stars, recommended (subject_expansion_stlc)
An exercise in the [Stlc]({{ "Stlc" | relative_url }}) chapter asked about the
subject expansion property for the simple language of arithmetic and boolean
expressions.  Does this property hold for STLC?  That is, is it always the case
that, if `t ==> t'` and `has_type t' T`, then `empty \vdash t : T`?  If
so, prove it.  If not, give a counter-example not involving conditionals. 


## Type Soundness

#### Exercise: 2 stars, optional (type_soundness)
Put progress and preservation together and show that a well-typed
term can _never_ reach a stuck state.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty \vdash t : T →
  t ==>* t' →
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros `Hnf Hnot_val`. unfold normal_form in Hnf.
  induction Hmulti.


## Uniqueness of Types

#### Exercise: 3 stars (types_unique)
Another nice property of the STLC is that types are unique: a
given term (in a given context) has at most one type.
Formalize this statement and prove it.


## Additional Exercises

#### Exercise: 1 star (progress_preservation_statement)
Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.
``

#### Exercise: 2 stars (stlc_variation1)
Suppose we add a new term `zap` with the following reduction rule

                     ---------                  (ST_Zap)
                     t ==> zap

and the following typing rule:

                  ----------------               (T_Zap)
                  Gamma \vdash zap : T

Which of the following properties of the STLC remain true in
the presence of these rules?  For each property, write either
"remains true" or "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation


#### Exercise: 2 stars (stlc_variation2)
Suppose instead that we add a new term `foo` with the following
reduction rules:

                   -----------------                (ST_Foo1)
                   (\lambda x:A. x) ==> foo

                     ------------                   (ST_Foo2)
                     foo ==> true

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation

#### Exercise: 2 stars (stlc_variation3)
Suppose instead that we remove the rule `Sapp1` from the `step`
relation. Which of the following properties of the STLC remain
true in the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation

#### Exercise: 2 stars, optional (stlc_variation4)
Suppose instead that we add the following new rule to the
reduction relation:

        ----------------------------------        (ST_FunnyIfTrue)
        (if true then t_1 else t_2) ==> true

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation



#### Exercise: 2 stars, optional (stlc_variation5)
Suppose instead that we add the following new rule to the typing
relation:

             Gamma \vdash t_1 : bool→bool→bool
                 Gamma \vdash t_2 : bool
             ------------------------------          (T_FunnyApp)
                Gamma \vdash t_1 t_2 : bool

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation



#### Exercise: 2 stars, optional (stlc_variation6)
Suppose instead that we add the following new rule to the typing
relation:

                 Gamma \vdash t_1 : bool
                 Gamma \vdash t_2 : bool
                ---------------------               (T_FunnyApp')
                Gamma \vdash t_1 t_2 : bool

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation



#### Exercise: 2 stars, optional (stlc_variation7)
Suppose we add the following new rule to the typing relation
of the STLC:

                     ------------------- (T_FunnyAbs)
                     \vdash \lambda x:bool.t : bool

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation


### Exercise: STLC with Arithmetic

To see how the STLC might function as the core of a real
programming language, let's extend it with a concrete base
type of numbers and some constants and primitive
operators.

To types, we add a base type of natural numbers (and remove
booleans, for brevity).

Inductive ty : Type :=
  | TArrow : ty → ty → ty
  | TNat   : ty.

To terms, we add natural number constants, along with
successor, predecessor, multiplication, and zero-testing.

Inductive tm : Type :=
  | tvar : id → tm
  | tapp : tm → tm → tm
  | tabs : id → ty → tm → tm
  | tnat  : nat → tm
  | tsucc : tm → tm
  | tpred : tm → tm
  | tmult : tm → tm → tm
  | tif0  : tm → tm → tm → tm.

#### Exercise: 4 stars (stlc_arith)
Finish formalizing the definition and properties of the STLC extended
with arithmetic.  Specifically:

  - Copy the whole development of STLC that we went through above (from
    the definition of values through the Type Soundness theorem), and
    paste it into the file at this point.

  - Extend the definitions of the `subst` operation and the `step`
     relation to include appropriate clauses for the arithmetic operators.

  - Extend the proofs of all the properties (up to `soundness`) of
    the original STLC to deal with the new syntactic forms.  Make
    sure Agda accepts the whole file.

