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
belonging to each type.  For $$bool$$, these are the boolean values $$true$$ and
$$false$$.  For arrow types, the canonical forms are lambda-abstractions. 

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

_Proof_: By induction on the derivation of $$\vdash t : A$$.

  - The last rule of the derivation cannot be `var`,
    since a variable is never well typed in an empty context.

  - The `true`, `false`, and `abs` cases are trivial, since in
    each of these cases we can see by inspecting the rule that $$t$$
    is a value.

  - If the last rule of the derivation is `app`, then $$t$$ has the
    form $$t_1\;t_2$$ for som e$$t_1$$ and $$t_2$$, where we know that
    $$t_1$$ and $$t_2$$ are also well typed in the empty context; in particular,
    there exists a type $$B$$ such that $$\vdash t_1 : A\to T$$ and
    $$\vdash t_2 : B$$.  By the induction hypothesis, either $$t_1$$ is a
    value or it can take a reduction step.

  - If $$t_1$$ is a value, then consider $$t_2$$, which by the other
    induction hypothesis must also either be a value or take a step.

    - Suppose $$t_2$$ is a value.  Since $$t_1$$ is a value with an
      arrow type, it must be a lambda abstraction; hence $$t_1\;t_2$$
      can take a step by `red`.

    - Otherwise, $$t_2$$ can take a step, and hence so can $$t_1\;t_2$$
      by `app2`.

  - If $$t_1$$ can take a step, then so can $$t_1 t_2$$ by `app1`.

  - If the last rule of the derivation is `if`, then $$t = \text{if }t_1
    \text{ then }t_2\text{ else }t_3$$, where $$t_1$$ has type $$bool$$.  By
    the IH, $$t_1$$ either is a value or takes a step.

  - If $$t_1$$ is a value, then since it has type $$bool$$ it must be
    either $$true$$ or $$false$$.  If it is $$true$$, then $$t$$ steps
    to $$t_2$$; otherwise it steps to $$t_3$$.

  - Otherwise, $$t_1$$ takes a step, and therefore so does $$t$$ (by `if`).

\begin{code}
progress (Ax ())
progress (⇒-I ⊢N) = inj₁ value-λᵀ
progress (⇒-E ⊢L ⊢M) with progress ⊢L
... | inj₂ (_ , L⟹L′) = inj₂ (_ , γ⇒₁ L⟹L′)
... | inj₁ valueL with progress ⊢M
... | inj₂ (_ , M⟹M′) = inj₂ (_ , γ⇒₂ valueL M⟹M′)
... | inj₁ valueM with canonicalFormsLemma ⊢L valueL
... | canonical-λᵀ = inj₂ (_ , β⇒ valueM)
progress 𝔹-I₁ = inj₁ value-trueᵀ
progress 𝔹-I₂ = inj₁ value-falseᵀ
progress (𝔹-E ⊢L ⊢M ⊢N) with progress ⊢L
... | inj₂ (_ , L⟹L′) = inj₂ (_ , γ𝔹 L⟹L′)
... | inj₁ valueL with canonicalFormsLemma ⊢L valueL
... | canonical-trueᵀ = inj₂ (_ , β𝔹₁)
... | canonical-falseᵀ = inj₂ (_ , β𝔹₂)
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
    $$red$$ rule, whose definition uses the substitution operation.  To see that
    this step preserves typing, we need to know that the substitution itself
    does.  So we prove a... 

  - _substitution lemma_, stating that substituting a (closed)
    term $$s$$ for a variable $$x$$ in a term $$t$$ preserves the type
    of $$t$$.  The proof goes by induction on the form of $$t$$ and
    requires looking at all the different cases in the definition
    of substitition.  This time, the tricky cases are the ones for
    variables and for function abstractions.  In both cases, we
    discover that we need to take a term $$s$$ that has been shown
    to be well-typed in some context $$\Gamma$$ and consider the same
    term $$s$$ in a slightly different context $$\Gamma'$$.  For this
    we prove a...

  - _context invariance_ lemma, showing that typing is preserved
    under "inessential changes" to the context $$\Gamma$$---in
    particular, changes that do not affect any of the free
    variables of the term.  And finally, for this, we need a
    careful definition of...

  - the _free variables_ of a term---i.e., those variables
    mentioned in a term and not in the scope of an enclosing
    function abstraction binding a variable of the same name.

To make Agda happy, we need to formalize the story in the opposite
order...


### Free Occurrences

A variable $$x$$ _appears free in_ a term $$M$$ if $$M$$ contains some
occurrence of $$x$$ that is not under an abstraction over $$x$$.
For example:

  - $$y$$ appears free, but $$x$$ does not, in $$λᵀ x ∈ (A ⇒ B) ⇒ x ·ᵀ y$$
  - both $$x$$ and $$y$$ appear free in $$(λᵀ x ∈ (A ⇒ B) ⇒ x ·ᵀ y) ·ᵀ x$$
  - no variables appear free in $$λᵀ x ∈ (A ⇒ B) ⇒ (λᵀ y ∈ A ⇒ x ·ᵀ y)$$

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
a variable $$x$$ appears free in a term $$M$$, and if we know $$M$$ is
well typed in context $$Γ$$, then it must be the case that
$$Γ$$ assigns a type to $$x$$.

\begin{code}
freeLemma : ∀ {x M A Γ} → x FreeIn M → Γ ⊢ M ∈ A → ∃ λ B → Γ x ≡ just B
\end{code}

_Proof_: We show, by induction on the proof that $$x$$ appears
  free in $$P$$, that, for all contexts $$Γ$$, if $$P$$ is well
  typed under $$Γ$$, then $$Γ$$ assigns some type to $$x$$.

  - If the last rule used was `free-varᵀ`, then $$P = x$$, and from
    the assumption that $$M$$ is well typed under $$Γ$$ we have
    immediately that $$Γ$$ assigns a type to $$x$$.

  - If the last rule used was `free-·₁`, then $$P = L ·ᵀ M$$ and $$x$$
    appears free in $$L$$.  Since $$L$$ is well typed under $$\Gamma$$,
    we can see from the typing rules that $$L$$ must also be, and
    the IH then tells us that $$Γ$$ assigns $$x$$ a type.

  - Almost all the other cases are similar: $$x$$ appears free in a
    subterm of $$P$$, and since $$P$$ is well typed under $$Γ$$, we
    know the subterm of $$M$$ in which $$x$$ appears is well typed
    under $$Γ$$ as well, and the IH gives us exactly the
    conclusion we want.

  - The only remaining case is `free-λᵀ`.  In this case $$P =
    λᵀ y ∈ A ⇒ N$$, and $$x$$ appears free in $$N$$; we also know that
    $$x$$ is different from $$y$$.  The difference from the previous
    cases is that whereas $$P$$ is well typed under $$\Gamma$$, its
    body $$N$$ is well typed under $$(Γ , y ↦ A)$$, so the IH
    allows us to conclude that $$x$$ is assigned some type by the
    extended context $$(Γ , y ↦ A)$$.  To conclude that $$Γ$$
    assigns a type to $$x$$, we appeal the decidable equality for names
    `_≟_`, noting that $$x$$ and $$y$$ are different variables.

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

[A subtle point: if the first argument of $$free-λᵀ$$ was of type
$$x ≢ y$$ rather than of type $$y ≢ x$$, then the type of the
term $$Γx=justC$$ would not simplify properly.]

Next, we'll need the fact that any term $$M$$ which is well typed in
the empty context is closed (it has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

\begin{code}
postulate
  ∅⊢-closed : ∀ {M A} → ∅ ⊢ M ∈ A → closed M
\end{code}

<div class="hidden">
\begin{code}
contradiction : ∀ {A : Set} → ∀ {v : A} → ¬ (_≡_ {A = Maybe A} (just v) nothing)
contradiction ()

-- ∅⊢-closed′ : ∀ {M A} → ∅ ⊢ M ∈ A → closed M
-- ∅⊢-closed′ {M} {A} ⊢M {x} x∈M with freeLemma x∈M ⊢M
-- ... | (B , ∅x≡justB) = contradiction (trans (sym ∅x≡justB) apply-∅)

{-
∅⊢-closed′ : ∀ {t A} → ∅ ⊢ t ∶ A → Closed t
∅⊢-closed′ (var x ())
∅⊢-closed′ (app t₁∶A⇒B t₂∶A) (app1 x∈t₁) = ∅⊢-closed′ t₁∶A⇒B x∈t₁
∅⊢-closed′ (app t₁∶A⇒B t₂∶A) (app2 x∈t₂) = ∅⊢-closed′ t₂∶A x∈t₂
∅⊢-closed′ true  ()
∅⊢-closed′ false ()
∅⊢-closed′ (if t₁∶bool then t₂∶A else t₃∶A) (if1 x∈t₁) = ∅⊢-closed′ t₁∶bool x∈t₁
∅⊢-closed′ (if t₁∶bool then t₂∶A else t₃∶A) (if2 x∈t₂) = ∅⊢-closed′ t₂∶A x∈t₂
∅⊢-closed′ (if t₁∶bool then t₂∶A else t₃∶A) (if3 x∈t₃) = ∅⊢-closed′ t₃∶A x∈t₃
∅⊢-closed′ (abs {x = x} t′∶A) {y} (abs x≠y y∈t′) with freeInCtxt y∈t′ t′∶A
∅⊢-closed′ (abs {x = x} t′∶A) {y} (abs x≠y y∈t′) | A , y∶A with x ≟ y
∅⊢-closed′ (abs {x = x} t′∶A) {y} (abs x≠y y∈t′) | A , y∶A | yes x=y = x≠y x=y
∅⊢-closed′ (abs {x = x} t′∶A) {y} (abs x≠y y∈t′) | A , ()  | no  _
-}
\end{code}
</div>

Sometimes, when we have a proof $$Γ ⊢ M ∈ A$$, we will need to
replace $$Γ$$ by a different context $$Γ′$$.  When is it safe
to do this?  Intuitively, it must at least be the case that
$$Γ′$$ assigns the same types as $$Γ$$ to all the variables
that appear free in $$M$$. In fact, this is the only condition that
is needed.

\begin{code}
weaken : ∀ {Γ Γ′ M A}
        → (∀ {x} → x FreeIn M → Γ x ≡ Γ′ x)
        → Γ  ⊢ M ∈ A
        → Γ′ ⊢ M ∈ A
\end{code}

_Proof_: By induction on the derivation of
$$Γ ⊢ M ∈ A$$.

  - If the last rule in the derivation was `var`, then $$t = x$$
    and $$\Gamma x = T$$.  By assumption, $$\Gamma' x = T$$ as well, and
    hence $$\Gamma' \vdash t : T$$ by `var`.

  - If the last rule was `abs`, then $$t = \lambda y:A. t'$$, with
    $$T = A\to B$$ and $$\Gamma, y : A \vdash t' : B$$.  The
    induction hypothesis is that, for any context $$\Gamma''$$, if
    $$\Gamma, y:A$$ and $$\Gamma''$$ assign the same types to all the
    free variables in $$t'$$, then $$t'$$ has type $$B$$ under
    $$\Gamma''$$.  Let $$\Gamma'$$ be a context which agrees with
    $$\Gamma$$ on the free variables in $$t$$; we must show
    $$\Gamma' \vdash \lambda y:A. t' : A\to B$$.

    By $$abs$$, it suffices to show that $$\Gamma', y:A \vdash t' : t'$$.
    By the IH (setting $$\Gamma'' = \Gamma', y:A$$), it suffices to show
    that $$\Gamma, y:A$$ and $$\Gamma', y:A$$ agree on all the variables
    that appear free in $$t'$$.

    Any variable occurring free in $$t'$$ must be either $$y$$ or
    some other variable.  $$\Gamma, y:A$$ and $$\Gamma', y:A$$
    clearly agree on $$y$$.  Otherwise, note that any variable other
    than $$y$$ that occurs free in $$t'$$ also occurs free in
    $$t = \lambda y:A. t'$$, and by assumption $$\Gamma$$ and
    $$\Gamma'$$ agree on all such variables; hence so do $$\Gamma, y:A$$ and
    $$\Gamma', y:A$$.

  - If the last rule was `app`, then $$t = t_1\;t_2$$, with
    $$\Gamma \vdash t_1:A\to T$$ and $$\Gamma \vdash t_2:A$$.
    One induction hypothesis states that for all contexts $$\Gamma'$$,
    if $$\Gamma'$$ agrees with $$\Gamma$$ on the free variables in $$t_1$$,
    then $$t_1$$ has type $$A\to T$$ under $$\Gamma'$$; there is a similar IH
    for $$t_2$$.  We must show that $$t_1\;t_2$$ also has type $$T$$ under
    $$\Gamma'$$, given the assumption that $$\Gamma'$$ agrees with
    $$\Gamma$$ on all the free variables in $$t_1\;t_2$$.  By `app`, it
    suffices to show that $$t_1$$ and $$t_2$$ each have the same type
    under $$\Gamma'$$ as under $$\Gamma$$.  But all free variables in
    $$t_1$$ are also free in $$t_1\;t_2$$, and similarly for $$t_2$$;
    hence the desired result follows from the induction hypotheses.

-- weaken : ∀ {Γ Γ′ M A}
--            → (∀ {x} → x FreeIn M → Γ x ≡ Γ′ x)
--            → Γ  ⊢ M ∈ A
--            → Γ′ ⊢ M ∈ A


\begin{code}
weaken Γ⊆Γ′ (Ax Γx≡justA) rewrite (Γ⊆Γ′ free-varᵀ) = Ax Γx≡justA
weaken {Γ} {Γ′} {λᵀ x ∈ A ⇒ N} Γ⊆Γ′ (⇒-I ⊢N) = ⇒-I (weaken Γx⊆Γ′x ⊢N)
  where
  Γx⊆Γ′x : ∀ {y} → y FreeIn N → (Γ , x ↦ A) y ≡ (Γ′ , x ↦ A) y
  Γx⊆Γ′x {y} y∈N with x ≟ y
  ... | yes refl = refl
  ... | no  x≢y  = Γ⊆Γ′ (free-λᵀ x≢y y∈N)
weaken Γ⊆Γ′ (⇒-E ⊢L ⊢M) = ⇒-E (weaken (Γ⊆Γ′ ∘ free-·ᵀ₁)  ⊢L) (weaken (Γ⊆Γ′ ∘ free-·ᵀ₂) ⊢M) 
weaken Γ⊆Γ′ 𝔹-I₁ = 𝔹-I₁
weaken Γ⊆Γ′ 𝔹-I₂ = 𝔹-I₂
weaken Γ⊆Γ′ (𝔹-E ⊢L ⊢M ⊢N)
  = 𝔹-E (weaken (Γ⊆Γ′ ∘ free-ifᵀ₁) ⊢L) (weaken (Γ⊆Γ′ ∘ free-ifᵀ₂) ⊢M) (weaken (Γ⊆Γ′ ∘ free-ifᵀ₃) ⊢N)

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
have a term $$t$$ with a free variable $$x$$, and suppose we've been
able to assign a type $$T$$ to $$t$$ under the assumption that $$x$$ has
some type $$U$$.  Also, suppose that we have some other term $$v$$ and
that we've shown that $$v$$ has type $$U$$.  Then, since $$v$$ satisfies
the assumption we made about $$x$$ when typing $$t$$, we should be
able to substitute $$v$$ for each of the occurrences of $$x$$ in $$t$$
and obtain a new term that still has type $$T$$.

_Lemma_: If $$\Gamma,x:U \vdash t : T$$ and $$\vdash v : U$$, then
$$\Gamma \vdash [x:=v]t : T$$.

\begin{code}
{-
[:=]-preserves-⊢ : ∀ {Γ x A t v B}
                 → ∅ ⊢ v ∶ A
                 → Γ , x ∶ A ⊢ t ∶ B
                 → Γ , x ∶ A ⊢ [ x := v ] t ∶ B
-}
\end{code}

One technical subtlety in the statement of the lemma is that
we assign $$v$$ the type $$U$$ in the _empty_ context---in other
words, we assume $$v$$ is closed.  This assumption considerably
simplifies the $$abs$$ case of the proof (compared to assuming
$$\Gamma \vdash v : U$$, which would be the other reasonable assumption
at this point) because the context invariance lemma then tells us
that $$v$$ has type $$U$$ in any context at all---we don't have to
worry about free variables in $$v$$ clashing with the variable being
introduced into the context by $$abs$$.

The substitution lemma can be viewed as a kind of "commutation"
property.  Intuitively, it says that substitution and typing can
be done in either order: we can either assign types to the terms
$$t$$ and $$v$$ separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to $$ $$x:=v$$ t $$---the result is the same either
way.

_Proof_: We show, by induction on $$t$$, that for all $$T$$ and
$$\Gamma$$, if $$\Gamma,x:U \vdash t : T$$ and $$\vdash v : U$$, then $$\Gamma
\vdash $$x:=v$$t : T$$.

  - If $$t$$ is a variable there are two cases to consider,
    depending on whether $$t$$ is $$x$$ or some other variable.

      - If $$t = x$$, then from the fact that $$\Gamma, x:U \vdash x :
        T$$ we conclude that $$U = T$$.  We must show that $$[x:=v]x =
        v$$ has type $$T$$ under $$\Gamma$$, given the assumption that
        $$v$$ has type $$U = T$$ under the empty context.  This
        follows from context invariance: if a closed term has type
        $$T$$ in the empty context, it has that type in any context.

      - If $$t$$ is some variable $$y$$ that is not equal to $$x$$, then
        we need only note that $$y$$ has the same type under $$\Gamma,
        x:U$$ as under $$\Gamma$$.

  - If $$t$$ is an abstraction $$\lambda y:t_{11}. t_{12}$$, then the IH tells us,
    for all $$\Gamma'$$ and $$T'$$, that if $$\Gamma',x:U \vdash t_{12}:T'$$
    and $$\vdash v:U$$, then $$\Gamma' \vdash [x:=v]t_{12}:T'$$.

    The substitution in the conclusion behaves differently
    depending on whether $$x$$ and $$y$$ are the same variable.

    First, suppose $$x = y$$.  Then, by the definition of
    substitution, $$[x:=v]t = t$$, so we just need to show $$\Gamma \vdash
    t : T$$.  But we know $$\Gamma,x:U \vdash t : T$$, and, since $$y$$
    does not appear free in $$\lambda y:t_{11}. t_{12}$$, the context invariance
    lemma yields $$\Gamma \vdash t : T$$.

    Second, suppose $$x \neq y$$.  We know $$\Gamma,x:U,y:t_{11} \vdash
    t_{12}:t_{12}$$ by inversion of the typing relation, from which
    $$\Gamma,y:t_{11},x:U \vdash t_{12}:t_{12}$$ follows by the context invariance
    lemma, so the IH applies, giving us $$\Gamma,y:t_{11} \vdash
    [x:=v]t_{12}:t_{12}$$.  By $$abs$$, $$\Gamma \vdash \lambda y:t_{11}.
    [x:=v]t_{12}:t_{11}\to t_{12}$$, and by the definition of substitution (noting
    that $$x \neq y$$), $$\Gamma \vdash \lambda y:t_{11}. [x:=v]t_{12}:t_{11}\to
    t_{12}$$ as required. 

  - If $$t$$ is an application $$t_1 t_2$$, the result follows
    straightforwardly from the definition of substitution and the
    induction hypotheses.

  - The remaining cases are similar to the application case.

One more technical note: This proof is a rare case where an
induction on terms, rather than typing derivations, yields a
simpler argument.  The reason for this is that the assumption
$$update Gamma x U \vdash t : T$$ is not completely generic, in the
sense that one of the "slots" in the typing relation---namely the
context---is not just a variable, and this means that Agda's
native induction tactic does not give us the induction hypothesis
that we want.  It is possible to work around this, but the needed
generalization is a little tricky.  The term $$t$$, on the other
hand, _is_ completely generic.

\begin{code}
{-
[:=]-preserves-⊢ {Γ} {x} v∶A (var y y∈Γ) with x ≟ y
... | yes x=y = {!!}
... | no  x≠y = {!!}
[:=]-preserves-⊢ v∶A (abs t′∶B) = {!!}
[:=]-preserves-⊢ v∶A (app t₁∶A⇒B t₂∶A) =
  app ([:=]-preserves-⊢ v∶A t₁∶A⇒B) ([:=]-preserves-⊢ v∶A t₂∶A)
[:=]-preserves-⊢ v∶A true  = true
[:=]-preserves-⊢ v∶A false = false
[:=]-preserves-⊢ v∶A (if t₁∶bool then t₂∶B else t₃∶B) =
  if   [:=]-preserves-⊢ v∶A t₁∶bool
  then [:=]-preserves-⊢ v∶A t₂∶B
  else [:=]-preserves-⊢ v∶A t₃∶B
-}
\end{code}


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term $$t$$ has type $$T$$ and takes a step to $$t'$$, then $$t'$$
is also a closed term with type $$T$$.  In other words, the small-step
reduction relation preserves types.

Theorem preservation : forall t t' T,
     empty \vdash t : T  →
     t ==> t'  →
     empty \vdash t' : T.

_Proof_: By induction on the derivation of $$\vdash t : T$$.

- We can immediately rule out $$var$$, $$abs$$, $$T_True$$, and
  $$T_False$$ as the final rules in the derivation, since in each of
  these cases $$t$$ cannot take a step.

- If the last rule in the derivation was $$app$$, then $$t = t_1
  t_2$$.  There are three cases to consider, one for each rule that
  could have been used to show that $$t_1 t_2$$ takes a step to $$t'$$.

    - If $$t_1 t_2$$ takes a step by $$Sapp1$$, with $$t_1$$ stepping to
      $$t_1'$$, then by the IH $$t_1'$$ has the same type as $$t_1$$, and
      hence $$t_1' t_2$$ has the same type as $$t_1 t_2$$.

    - The $$Sapp2$$ case is similar.

    - If $$t_1 t_2$$ takes a step by $$Sred$$, then $$t_1 =
      \lambda x:t_{11}.t_{12}$$ and $$t_1 t_2$$ steps to $$$$x:=t_2$$t_{12}$$; the
      desired result now follows from the fact that substitution
      preserves types.

    - If the last rule in the derivation was $$if$$, then $$t = if t_1
      then t_2 else t_3$$, and there are again three cases depending on
      how $$t$$ steps.

    - If $$t$$ steps to $$t_2$$ or $$t_3$$, the result is immediate, since
      $$t_2$$ and $$t_3$$ have the same type as $$t$$.

    - Otherwise, $$t$$ steps by $$Sif$$, and the desired conclusion
      follows directly from the induction hypothesis.

Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Gamma; subst;
       try solve $$inversion HE; subst; auto$$.
  - (* app
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and $$eauto$$ takes care of them
    + (* Sred
      apply substitution_preserves_typing with t_{11}...
      inversion HT_1...
Qed.

#### Exercise: 2 stars, recommended (subject_expansion_stlc)
An exercise in the [Stlc]({{ "Stlc" | relative_url }}) chapter asked about the
subject expansion property for the simple language of arithmetic and boolean
expressions.  Does this property hold for STLC?  That is, is it always the case
that, if $$t ==> t'$$ and $$has_type t' T$$, then $$empty \vdash t : T$$?  If
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
  intros $$Hnf Hnot_val$$. unfold normal_form in Hnf.
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
$$$$

#### Exercise: 2 stars (stlc_variation1)
Suppose we add a new term $$zap$$ with the following reduction rule

                     ---------                  (ST_Zap)
                     t ==> zap

and the following typing rule:

                  ----------------               (T_Zap)
                  Gamma \vdash zap : T

Which of the following properties of the STLC remain true in
the presence of these rules?  For each property, write either
"remains true" or "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of $$step$$

  - Progress

  - Preservation


#### Exercise: 2 stars (stlc_variation2)
Suppose instead that we add a new term $$foo$$ with the following
reduction rules:

                   -----------------                (ST_Foo1)
                   (\lambda x:A. x) ==> foo

                     ------------                   (ST_Foo2)
                     foo ==> true

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of $$step$$

  - Progress

  - Preservation

#### Exercise: 2 stars (stlc_variation3)
Suppose instead that we remove the rule $$Sapp1$$ from the $$step$$
relation. Which of the following properties of the STLC remain
true in the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of $$step$$

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

  - Determinism of $$step$$

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

  - Determinism of $$step$$

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

  - Determinism of $$step$$

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

  - Determinism of $$step$$

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

  - Extend the definitions of the $$subst$$ operation and the $$step$$
     relation to include appropriate clauses for the arithmetic operators.

  - Extend the proofs of all the properties (up to $$soundness$$) of
    the original STLC to deal with the new syntactic forms.  Make
    sure Agda accepts the whole file.

