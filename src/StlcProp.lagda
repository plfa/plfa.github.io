---
title     : "StlcProp: Properties of STLC"
layout    : page
permalink : /StlcProp
---

In this chapter, we develop the fundamental theory of the Simply
Typed Lambda Calculus---in particular, the type safety
theorem.

## Imports

\begin{code}
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; ∃; ∃₂; _,_; ,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)
open import Maps using (Id; _≟_; PartialMap)
open Maps.PartialMap using (∅; apply-∅; update-permute; just≢nothing; just-injective)
                     renaming (_,_↦_ to _,_∶_)
open import Stlc
import Data.Nat using (ℕ)
\end{code}


## Canonical Forms

<!--
As we saw for the simple calculus in Chapter [Types]({{ "Types" | relative_url }}),
-->

The first step in establishing basic properties of reduction and typing
is to identify the possible _canonical forms_ (i.e., well-typed closed values)
belonging to each type.  For function types the canonical forms are lambda-abstractions,
while for boolean types they are values `true` and `false`.  

\begin{code}
data canonical_for_ : Term → Type → Set where
  canonical-λ : ∀ {x A N B} → canonical (λ[ x ∶ A ] N) for (A ⇒ B)
  canonical-true : canonical true for 𝔹
  canonical-false : canonical false for 𝔹

canonical-forms : ∀ {L A} → ∅ ⊢ L ∶ A → Value L → canonical L for A
canonical-forms (Ax ()) ()
canonical-forms (⇒-I ⊢N) value-λ = canonical-λ
canonical-forms (⇒-E ⊢L ⊢M) ()
canonical-forms 𝔹-I₁ value-true = canonical-true
canonical-forms 𝔹-I₂ value-false = canonical-false
canonical-forms (𝔹-E ⊢L ⊢M ⊢N) ()
\end{code}

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term can take a reduction
step or it is a value.

\begin{code}
data Progress : Term → Set where
  steps : ∀ {M N} → M ⟹ N → Progress M
  done  : ∀ {M} → Value M → Progress M

progress : ∀ {M A} → ∅ ⊢ M ∶ A → Progress M
\end{code}

<!--
The proof is a relatively straightforward extension of the progress proof we saw in
[Types]({{ "Types" | relative_url }}).
-->

We give the proof in English first, then the formal version.

_Proof_: By induction on the derivation of `∅ ⊢ M ∶ A`.

  - The last rule of the derivation cannot be `Ax`,
    since a variable is never well typed in an empty context.

  - If the last rule of the derivation is `⇒-I`, `𝔹-I₁`, or `𝔹-I₂`
    then, trivially, the term is a value.

  - If the last rule of the derivation is `⇒-E`, then the term has the
    form `L · M` for some `L` and `M`, where we know that `L` and `M`
    are also well typed in the empty context, giving us two induction
    hypotheses.  By the first induction hypothesis, either `L`
    can take a step or is a value.

    - If `L` can take a step, then so can `L · M` by `ξ·₁`.

    - If `L` is a value then consider `M`. By the second induction
      hypothesis, either `M` can take a step or is a value.

      - If `M` can take a step, then so can `L · M` by `ξ·₂`.

      - If `M` is a value, then since `L` is a value with a
        function type we know from the canonical forms lemma
        that it must be a lambda abstraction,
        and hence `L · M` can take a step by `βλ·`.

  - If the last rule of the derivation is `𝔹-E`, then the term has
    the form `if L then M else N` where `L` has type `𝔹`.
    By the induction hypothesis, either `L` can take a step or is
    a value.

    - If `L` can take a step, then so can `if L then M else N` by `ξif`.

    - If `L` is a value, then since it has type boolean we know from
      the canonical forms lemma that it must be either `true` or
      `false`.

      - If `L` is `true`, then `if L then M else N` steps by `βif-true`

      - If `L` is `false`, then `if L then M else N` steps by `βif-false`

This completes the proof.

\begin{code}
progress (Ax ())
progress (⇒-I ⊢N) = done value-λ
progress (⇒-E ⊢L ⊢M) with progress ⊢L
... | steps L⟹L′ = steps (ξ·₁ L⟹L′)
... | done valueL with progress ⊢M
... | steps M⟹M′ = steps (ξ·₂ valueL M⟹M′)
... | done valueM with canonical-forms ⊢L valueL
... | canonical-λ = steps (βλ· valueM)
progress 𝔹-I₁ = done value-true
progress 𝔹-I₂ = done value-false
progress (𝔹-E ⊢L ⊢M ⊢N) with progress ⊢L
... | steps L⟹L′ = steps (ξif L⟹L′)
... | done valueL with canonical-forms ⊢L valueL
... | canonical-true = steps βif-true
... | canonical-false = steps βif-false
\end{code}

This code reads neatly in part because we consider the
`steps` option before the `done` option. We could, of course,
do it the other way around, but then the `...` abbreviation
no longer works, and we will need to write out all the arguments
in full. In general, the rule of thumb is to consider the easy case
(here `steps`) before the hard case (here `done`).
If you have two hard cases, you will have to expand out `...`
or introduce subsidiary functions.

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

\begin{code}
postulate
  progress′ : ∀ M {A} → ∅ ⊢ M ∶ A → Progress M
\end{code}

## Preservation

The other half of the type soundness property is the preservation
of types during reduction.  For this, we need to develop
technical machinery for reasoning about variables and
substitution.  Working from top to bottom (from the high-level
property we are actually interested in to the lowest-level
technical lemmas), the story goes like this:

  - The _preservation theorem_ is proved by induction on a typing derivation.
    derivation, pretty much as we did in chapter [Types]({{ "Types" | relative_url }})

  - The one case that is significantly different is the one for the
    `βλ·` rule, whose definition uses the substitution operation.  To see that
    this step preserves typing, we need to know that the substitution itself
    does.  So we prove a ... 

  - _substitution lemma_, stating that substituting a (closed) term
    `V` for a variable `x` in a term `N` preserves the type of `N`.
    The proof goes by induction on the form of `N` and requires
    looking at all the different cases in the definition of
    substitition. The lemma does not require that `V` be a value,
    though in practice we only substitute values.  The tricky cases
    are the ones for variables and for function abstractions.  In both
    cases, we discover that we need to take a term `V` that has been
    shown to be well-typed in some context `Γ` and consider the same
    term in a different context `Γ′`.  For this we prove a ...

  - _context invariance_ lemma, showing that typing is preserved
    under "inessential changes" to the context---a term `M`
    well typed in `Γ` is also well typed in `Γ′`, so long as
    all the free variables of `M` appear in both contexts.
    And finally, for this, we need a careful definition of ...

  - _free variables_ of a term---i.e., those variables
    mentioned in a term and not bound in an enclosing
    lambda abstraction.

To make Agda happy, we need to formalize the story in the opposite
order.


### Free Occurrences

A variable `x` appears _free_ in a term `M` if `M` contains an
occurrence of `x` that is not bound in an enclosing lambda abstraction.
For example:

  - Variable `x` appears free, but `f` does not, in ``λ[ f ∶ (𝔹 ⇒ 𝔹) ] ` f · ` x``.
  - Both `f` and `x` appear free in ``(λ[ f ∶ (𝔹 ⇒ 𝔹) ] ` f · ` x) · ` f``.
    Indeed, `f` appears both bound and free in this term.
  - No variables appear free in ``λ[ f ∶ (𝔹 ⇒ 𝔹) ] λ[ x ∶ 𝔹 ] ` f · ` x``.

Formally:

\begin{code}
data _∈_ : Id → Term → Set where
  free-`  : ∀ {x} → x ∈ ` x
  free-λ  : ∀ {x y A N} → y ≢ x → x ∈ N → x ∈ (λ[ y ∶ A ] N)
  free-·₁ : ∀ {x L M} → x ∈ L → x ∈ (L · M)
  free-·₂ : ∀ {x L M} → x ∈ M → x ∈ (L · M)
  free-if₁ : ∀ {x L M N} → x ∈ L → x ∈ (if L then M else N)
  free-if₂ : ∀ {x L M N} → x ∈ M → x ∈ (if L then M else N)
  free-if₃ : ∀ {x L M N} → x ∈ N → x ∈ (if L then M else N)
\end{code}

A term in which no variables appear free is said to be _closed_.

\begin{code}
_∉_ : Id → Term → Set
x ∉ M = ¬ (x ∈ M)

closed : Term → Set
closed M = ∀ {x} → x ∉ M
\end{code}

Here are proofs corresponding to the first two examples above.

\begin{code}
f≢x : f ≢ x
f≢x ()

example-free₁ : x ∈ (λ[ f ∶ (𝔹 ⇒ 𝔹) ] ` f · ` x)
example-free₁ = free-λ f≢x (free-·₂ free-`)

example-free₂ : f ∉ (λ[ f ∶ (𝔹 ⇒ 𝔹) ] ` f · ` x)
example-free₂ (free-λ f≢f _) = f≢f refl
\end{code}


#### Exercise: 1 star (free-in)
Prove formally the remaining examples given above.

\begin{code}
postulate
  example-free₃ : x ∈ ((λ[ f ∶ (𝔹 ⇒ 𝔹) ] ` f · ` x) · ` f)
  example-free₄ : f ∈ ((λ[ f ∶ (𝔹 ⇒ 𝔹) ] ` f · ` x) · ` f)
  example-free₅ : x ∉ (λ[ f ∶ (𝔹 ⇒ 𝔹) ] λ[ x ∶ 𝔹 ] ` f · ` x)
  example-free₆ : f ∉ (λ[ f ∶ (𝔹 ⇒ 𝔹) ] λ[ x ∶ 𝔹 ] ` f · ` x)
\end{code}

Although `_∈_` may appear to be a low-level technical definition,
understanding it is crucial to understanding the properties of
substitution, which are really the crux of the lambda calculus.

### Substitution

To prove that substitution preserves typing, we first need a technical
lemma connecting free variables and typing contexts. If variable `x`
appears free in term `M`, and if `M` is well typed in context `Γ`,
then `Γ` must assign a type to `x`.

\begin{code}
free-lemma : ∀ {x M A Γ} → x ∈ M → Γ ⊢ M ∶ A → ∃ λ B → Γ x ≡ just B
\end{code}

_Proof_: We show, by induction on the proof that `x` appears
  free in `M`, that, for all contexts `Γ`, if `M` is well
  typed under `Γ`, then `Γ` assigns some type to `x`.

  - If the last rule used was `` free-` ``, then `M = `` `x ``, and from
    the assumption that `M` is well typed under `Γ` we have
    immediately that `Γ` assigns a type to `x`.

  - If the last rule used was `free-·₁`, then `M = L · M` and `x`
    appears free in `L`.  Since `L` is well typed under `Γ`,
    we can see from the typing rules that `L` must also be, and
    the IH then tells us that `Γ` assigns `x` a type.

  - Almost all the other cases are similar: `x` appears free in a
    subterm of `M`, and since `M` is well typed under `Γ`, we
    know the subterm of `M` in which `x` appears is well typed
    under `Γ` as well, and the IH yields the desired conclusion.

  - The only remaining case is `free-λ`.  In this case `M =
    λ[ y ∶ A ] N`, and `x` appears free in `N`; we also know that
    `x` is different from `y`.  The difference from the previous
    cases is that whereas `M` is well typed under `Γ`, its
    body `N` is well typed under `(Γ , y ∶ A)`, so the IH
    allows us to conclude that `x` is assigned some type by the
    extended context `(Γ , y ∶ A)`.  To conclude that `Γ`
    assigns a type to `x`, we appeal the decidable equality for names
    `_≟_`, and note that `x` and `y` are different variables.

\begin{code}
free-lemma free-` (Ax Γx≡A) = (_ , Γx≡A)
free-lemma (free-·₁ x∈L) (⇒-E ⊢L ⊢M) = free-lemma x∈L ⊢L
free-lemma (free-·₂ x∈M) (⇒-E ⊢L ⊢M) = free-lemma x∈M ⊢M
free-lemma (free-if₁ x∈L) (𝔹-E ⊢L ⊢M ⊢N) = free-lemma x∈L ⊢L
free-lemma (free-if₂ x∈M) (𝔹-E ⊢L ⊢M ⊢N) = free-lemma x∈M ⊢M
free-lemma (free-if₃ x∈N) (𝔹-E ⊢L ⊢M ⊢N) = free-lemma x∈N ⊢N
free-lemma (free-λ {x} {y} y≢x x∈N) (⇒-I ⊢N) with free-lemma x∈N ⊢N
... | Γx≡C with y ≟ x
... | yes y≡x = ⊥-elim (y≢x y≡x)
... | no  _   = Γx≡C
\end{code}

A subtle point: if the first argument of `free-λ` was of type
`x ≢ y` rather than of type `y ≢ x`, then the type of the
term `Γx≡C` would not simplify properly; instead, one would need
to rewrite with the symmetric equivalence.

As a second technical lemma, we need that any term `M` which is well
typed in the empty context is closed (has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

\begin{code}
postulate
  ∅⊢-closed : ∀ {M A} → ∅ ⊢ M ∶ A → closed M
\end{code}

<div class="hidden">
\begin{code}
∅⊢-closed′ : ∀ {M A} → ∅ ⊢ M ∶ A → closed M
∅⊢-closed′ {M} {A} ⊢M {x} x∈M with free-lemma x∈M ⊢M
... | (B , ∅x≡B) = just≢nothing (trans (sym ∅x≡B) (apply-∅ x))
\end{code}
</div>

Sometimes, when we have a proof `Γ ⊢ M ∶ A`, we will need to
replace `Γ` by a different context `Γ′`.  When is it safe
to do this?  Intuitively, the only variables we care about
in the context are those that appear free in `M`. So long
as the two contexts agree on those variables, one can be
exchanged for the other.

\begin{code}
context-lemma : ∀ {Γ Γ′ M A}
        → (∀ {x} → x ∈ M → Γ x ≡ Γ′ x)
        → Γ  ⊢ M ∶ A
        → Γ′ ⊢ M ∶ A
\end{code}

_Proof_: By induction on the derivation of `Γ ⊢ M ∶ A`.

  - If the last rule in the derivation was `Ax`, then `M = x`
    and `Γ x ≡ just A`.  By assumption, `Γ′ x = just A` as well, and
    hence `Γ′ ⊢ M : A` by `Ax`.

  - If the last rule was `⇒-I`, then `M = λ[ y : A] N`, with
    `A = A ⇒ B` and `Γ , y ∶ A ⊢ N ∶ B`.  The
    induction hypothesis is that, for any context `Γ″`, if
    `Γ , y : A` and `Γ″` assign the same types to all the
    free variables in `N`, then `N` has type `B` under
    `Γ″`.  Let `Γ′` be a context which agrees with
    `Γ` on the free variables in `N`; we must show
    `Γ′ ⊢ λ[ y ∶ A] N ∶ A ⇒ B`.

    By `⇒-I`, it suffices to show that `Γ′ , y:A ⊢ N ∶ B`.
    By the IH (setting `Γ″ = Γ′ , y : A`), it suffices to show
    that `Γ , y : A` and `Γ′ , y : A` agree on all the variables
    that appear free in `N`.

    Any variable occurring free in `N` must be either `y` or
    some other variable.  Clearly, `Γ , y : A` and `Γ′ , y : A`
    agree on `y`.  Otherwise, any variable other
    than `y` that occurs free in `N` also occurs free in
    `λ[ y : A] N`, and by assumption `Γ` and
    `Γ′` agree on all such variables; hence so do
    `Γ , y : A` and `Γ′ , y : A`.

  - If the last rule was `⇒-E`, then `M = L · M`, with `Γ ⊢ L ∶ A ⇒ B`
    and `Γ ⊢ M ∶ B`.  One induction hypothesis states that for all
    contexts `Γ′`, if `Γ′` agrees with `Γ` on the free variables in
    `L` then `L` has type `A ⇒ B` under `Γ′`; there is a similar IH
    for `M`.  We must show that `L · M` also has type `B` under `Γ′`,
    given the assumption that `Γ′` agrees with `Γ` on all the free
    variables in `L · M`.  By `⇒-E`, it suffices to show that `L` and
    `M` each have the same type under `Γ′` as under `Γ`.  But all free
    variables in `L` are also free in `L · M`; in the proof, this is
    expressed by composing `free-·₁ : ∀ {x} → x ∈ L → x ∈ L · M` with
    `Γ~Γ′ : (∀ {x} → x ∈ L · M → Γ x ≡ Γ′ x)` to yield `Γ~Γ′ ∘ free-·₁
    : ∀ {x} → x ∈ L → Γ x ≡ Γ′ x`.  Similarly for `M`; hence the
    desired result follows from the induction hypotheses.

  - The remaining cases are similar to `⇒-E`.

\begin{code}
context-lemma Γ~Γ′ (Ax Γx≡A) rewrite (Γ~Γ′ free-`) = Ax Γx≡A
context-lemma {Γ} {Γ′} {λ[ x ∶ A ] N} Γ~Γ′ (⇒-I ⊢N) = ⇒-I (context-lemma Γx~Γ′x ⊢N)
  where
  Γx~Γ′x : ∀ {y} → y ∈ N → (Γ , x ∶ A) y ≡ (Γ′ , x ∶ A) y
  Γx~Γ′x {y} y∈N with x ≟ y
  ... | yes refl = refl
  ... | no  x≢y  = Γ~Γ′ (free-λ x≢y y∈N)
context-lemma Γ~Γ′ (⇒-E ⊢L ⊢M) = ⇒-E (context-lemma (Γ~Γ′ ∘ free-·₁)  ⊢L)
                                       (context-lemma (Γ~Γ′ ∘ free-·₂) ⊢M) 
context-lemma Γ~Γ′ 𝔹-I₁ = 𝔹-I₁
context-lemma Γ~Γ′ 𝔹-I₂ = 𝔹-I₂
context-lemma Γ~Γ′ (𝔹-E ⊢L ⊢M ⊢N) = 𝔹-E (context-lemma (Γ~Γ′ ∘ free-if₁) ⊢L)
                                         (context-lemma (Γ~Γ′ ∘ free-if₂) ⊢M)
                                         (context-lemma (Γ~Γ′ ∘ free-if₃) ⊢N)
\end{code}


Now we come to the conceptual heart of the proof that reduction
preserves types---namely, the observation that _substitution_
preserves types.

Formally, the _Substitution Lemma_ says this: Suppose we
have a term `N` with a free variable `x`, where `N` has
type `B` under the assumption that `x` has some type `A`.
Also, suppose that we have some other term `V`,
where `V` has type `A`.  Then, since `V` satisfies
the assumption we made about `x` when typing `N`, we should be
able to substitute `V` for each of the occurrences of `x` in `N`
and obtain a new term that still has type `B`.

_Lemma_: If `Γ , x ∶ A ⊢ N ∶ B` and `∅ ⊢ V ∶ A`, then
`Γ ⊢ (N [ x := V ]) ∶ B`.

\begin{code}
preservation-[:=] : ∀ {Γ x A N B V}
                 → (Γ , x ∶ A) ⊢ N ∶ B
                 → ∅ ⊢ V ∶ A
                 → Γ ⊢ (N [ x := V ]) ∶ B
\end{code}

One technical subtlety in the statement of the lemma is that we assume
`V` is closed; it has type `A` in the _empty_ context.  This
assumption simplifies the `λ` case of the proof because the context
invariance lemma then tells us that `V` has type `A` in any context at
all---we don't have to worry about free variables in `V` clashing with
the variable being introduced into the context by `λ`. It is possible
to prove the theorem under the more general assumption `Γ ⊢ V ∶ A`,
but the proof is more difficult.

<!--
Intuitively, the substitution lemma says that substitution and typing can
be done in either order: we can either assign types to the terms
`N` and `V` separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to `N [ x := V ]`---the result is the same either
way.
-->

_Proof_:  By induction on the derivation of `Γ , x ∶ A ⊢ N ∶ B`,
we show that if `∅ ⊢ V ∶ A` then `Γ ⊢ N [ x := V ] ∶ B`.

  - If `N` is a variable there are two cases to consider,
    depending on whether `N` is `x` or some other variable.

      - If `N = `` `x ``, then from `Γ , x ∶ A ⊢ x ∶ B`
        we know that looking up `x` in `Γ , x : A` gives
        `just B`, but we already know it gives `just A`;
        applying injectivity for `just` we conclude that `A ≡ B`.
        We must show that `x [ x := V] = V`
        has type `A` under `Γ`, given the assumption that
        `V` has type `A` under the empty context.  This
        follows from context invariance: if a closed term has type
        `A` in the empty context, it has that type in any context.

      - If `N` is some variable `x′` different from `x`, then
        we need only note that `x′` has the same type under `Γ , x ∶ A`
        as under `Γ`.

  - If `N` is an abstraction `λ[ x′ ∶ A′ ] N′`, then the IH tells us,
    for all `Γ′`́ and `B′`, that if `Γ′ , x ∶ A ⊢ N′ ∶ B′`
    and `∅ ⊢ V ∶ A`, then `Γ′ ⊢ N′ [ x := V ] ∶ B′`.

    The substitution in the conclusion behaves differently
    depending on whether `x` and `x′` are the same variable.

    First, suppose `x ≡ x′`.  Then, by the definition of
    substitution, `N [ x := V] = N`, so we just need to show `Γ ⊢ N ∶ B`.
    But we know `Γ , x ∶ A ⊢ N ∶ B` and, since `x ≡ x′`
    does not appear free in `λ[ x′ ∶ A′ ] N′`, the context invariance
    lemma yields `Γ ⊢ N ∶ B`.

    Second, suppose `x ≢ x′`.  We know `Γ , x ∶ A , x′ ∶ A′ ⊢ N′ ∶ B′`
    by inversion of the typing relation, from which
    `Γ , x′ ∶ A′ , x ∶ A ⊢ N′ ∶ B′` follows by update permute,
    so the IH applies, giving us `Γ , x′ ∶ A′ ⊢ N′ [ x := V ] ∶ B′`
    By `⇒-I`, we have `Γ ⊢ λ[ x′ ∶ A′ ] (N′ [ x := V ]) ∶ A′ ⇒ B′`
    and the definition of substitution (noting `x ≢ x′`) gives
    `Γ ⊢ (λ[ x′ ∶ A′ ] N′) [ x := V ] ∶ A′ ⇒ B′` as required.

  - If `N` is an application `L′ · M′`, the result follows
    straightforwardly from the definition of substitution and the
    induction hypotheses.

  - The remaining cases are similar to application.

We need a lemmas stating that a closed term can be weakened to any context.
\begin{code}
weaken-closed : ∀ {V A Γ} → ∅ ⊢ V ∶ A → Γ ⊢ V ∶ A
weaken-closed {V} {A} {Γ} ⊢V = context-lemma Γ~Γ′ ⊢V
  where
  Γ~Γ′ : ∀ {x} → x ∈ V → ∅ x ≡ Γ x
  Γ~Γ′ {x} x∈V = ⊥-elim (x∉V x∈V)
    where
    x∉V : ¬ (x ∈ V)
    x∉V = ∅⊢-closed ⊢V {x}

\end{code}

\begin{code}
preservation-[:=] {Γ} {x} {A} (Ax {Γ,x∶A} {x′} {B} [Γ,x∶A]x′≡B) ⊢V with x ≟ x′
...| yes x≡x′ rewrite just-injective [Γ,x∶A]x′≡B  =  weaken-closed ⊢V
...| no  x≢x′  =  Ax [Γ,x∶A]x′≡B
preservation-[:=] {Γ} {x} {A} {λ[ x′ ∶ A′ ] N′} {.A′ ⇒ B′} {V} (⇒-I ⊢N′) ⊢V with x ≟ x′
...| yes x≡x′ rewrite x≡x′ = context-lemma Γ′~Γ (⇒-I ⊢N′)
  where
  Γ′~Γ : ∀ {y} → y ∈ (λ[ x′ ∶ A′ ] N′) → (Γ , x′ ∶ A) y ≡ Γ y
  Γ′~Γ {y} (free-λ x′≢y y∈N′) with x′ ≟ y
  ...| yes x′≡y  = ⊥-elim (x′≢y x′≡y)
  ...| no  _     = refl
...| no  x≢x′ = ⇒-I ⊢N′V
  where
  x′x⊢N′ : Γ , x′ ∶ A′ , x ∶ A ⊢ N′ ∶ B′
  x′x⊢N′ rewrite update-permute Γ x A x′ A′ x≢x′ = ⊢N′
  ⊢N′V : (Γ , x′ ∶ A′) ⊢ N′ [ x := V ] ∶ B′
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
preservation : ∀ {M N A} → ∅ ⊢ M ∶ A → M ⟹ N → ∅ ⊢ N ∶ A
\end{code}

_Proof_: By induction on the derivation of `∅ ⊢ M ∶ A`.

- We can immediately rule out `Ax`, `⇒-I`, `𝔹-I₁`, and
  `𝔹-I₂` as the final rules in the derivation, since in each of
  these cases `M` cannot take a step.

- If the last rule in the derivation was `⇒-E`, then `M = L · M`.
  There are three cases to consider, one for each rule that
  could have been used to show that `L · M` takes a step to `N`.

    - If `L · M` takes a step by `ξ·₁`, with `L` stepping to
      `L′`, then by the IH `L′` has the same type as `L`, and
      hence `L′ · M` has the same type as `L · M`.

    - The `ξ·₂` case is similar.

    - If `L · M` takes a step by `β⇒`, then `L = λ[ x ∶ A ] N` and `M
      = V` and `L · M` steps to `N [ x := V]`; the desired result now
      follows from the fact that substitution preserves types.

- If the last rule in the derivation was `if`, then `M = if L
  then M else N`, and there are again three cases depending on
  how `if L then M else N` steps.

    - If it steps via `β𝔹₁` or `βB₂`, the result is immediate, since
      `M` and `N` have the same type as `if L then M else N`.

    - Otherwise, `L` steps by `ξif`, and the desired conclusion
      follows directly from the induction hypothesis.

\begin{code}
preservation (Ax Γx≡A) ()
preservation (⇒-I ⊢N) ()
preservation (⇒-E (⇒-I ⊢N) ⊢V) (βλ· valueV) = preservation-[:=] ⊢N ⊢V
preservation (⇒-E ⊢L ⊢M) (ξ·₁ L⟹L′) with preservation ⊢L L⟹L′
...| ⊢L′ = ⇒-E ⊢L′ ⊢M
preservation (⇒-E ⊢L ⊢M) (ξ·₂ valueL M⟹M′) with preservation ⊢M M⟹M′
...| ⊢M′ = ⇒-E ⊢L ⊢M′
preservation 𝔹-I₁ ()
preservation 𝔹-I₂ ()
preservation (𝔹-E 𝔹-I₁ ⊢M ⊢N) βif-true = ⊢M
preservation (𝔹-E 𝔹-I₂ ⊢M ⊢N) βif-false = ⊢N
preservation (𝔹-E ⊢L ⊢M ⊢N) (ξif L⟹L′) with preservation ⊢L L⟹L′
...| ⊢L′ = 𝔹-E ⊢L′ ⊢M ⊢N
\end{code}


#### Exercise: 2 stars, recommended (subject_expansion_stlc)

<!--
An exercise in the [Types]({{ "Types" | relative_url }}) chapter asked about the
subject expansion property for the simple language of arithmetic and boolean
expressions.  Does this property hold for STLC?  That is, is it always the case
that, if `M ==> N` and `∅ ⊢ N ∶ A`, then `∅ ⊢ M ∶ A`?  It is easy to find a
counter-example with conditionals, find one not involving conditionals.
-->

We say that `M` _reduces_ to `N` if `M ⟹ N`,
and that `M` _expands_ to `N` if `N ⟹ M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M ==> N` and `∅ ⊢ N ∶ A`, then `∅ ⊢ M ∶ A`.
Find two counter-examples to subject expansion, one
with conditionals and one not involving conditionals.

## Type Soundness

#### Exercise: 2 stars, optional (type_soundness)

Put progress and preservation together and show that a well-typed
term can _never_ reach a stuck state.

\begin{code}
Normal : Term → Set
Normal M = ∀ {N} → ¬ (M ⟹ N)

Stuck : Term → Set
Stuck M = Normal M × ¬ Value M

postulate
  Soundness : ∀ {M N A} → ∅ ⊢ M ∶ A → M ⟹* N → ¬ (Stuck N)
\end{code}

<div class="hidden">
\begin{code}
Soundness′ : ∀ {M N A} → ∅ ⊢ M ∶ A → M ⟹* N → ¬ (Stuck N)
Soundness′ ⊢M (M ∎) (¬M⟹N , ¬ValueM) with progress ⊢M
... | steps M⟹N  = ¬M⟹N M⟹N
... | done ValueM  = ¬ValueM ValueM
Soundness′ {L} {N} {A} ⊢L (_⟹⟨_⟩_ .L {M} {.N} L⟹M M⟹*N) = Soundness′ ⊢M M⟹*N
  where
  ⊢M : ∅ ⊢ M ∶ A
  ⊢M = preservation ⊢L L⟹M
\end{code}
</div>


## Uniqueness of Types

#### Exercise: 3 stars (types_unique)

Another nice property of the STLC is that types are unique: a
given term (in a given context) has at most one type.
Formalize this statement and prove it.


## Additional Exercises

#### Exercise: 1 star (progress_preservation_statement)

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.

#### Exercise: 2 stars (stlc_variation1)

Suppose we add a new term `zap` with the following reduction rule

                     ---------                  (ST_Zap)
                     M ⟹ zap

and the following typing rule:

                    -----------                 (T_Zap)
                    Γ ⊢ zap : A

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

                 ----------------------             (ST_Foo1)
                 (λ[ x ∶ A ] ` x) ⟹ foo

                     -----------                    (ST_Foo2)
                     foo ⟹ true

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation

#### Exercise: 2 stars (stlc_variation3)

Suppose instead that we remove the rule `ξ·₁` from the `⟹`
relation. Which of the following properties of the STLC remain
true in the absence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation

#### Exercise: 2 stars, optional (stlc_variation4)
Suppose instead that we add the following new rule to the
reduction relation:

        ----------------------------------        (ST_FunnyIfTrue)
        (if true then t_1 else t_2) ⟹ true

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

             Γ ⊢ L ∶ 𝔹 ⇒ 𝔹 ⇒ 𝔹
             Γ ⊢ M ∶ 𝔹
             ------------------------------          (T_FunnyApp)
             Γ ⊢ L · M ∶ 𝔹

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

                Γ ⊢ L ∶ 𝔹
                Γ ⊢ M ∶ 𝔹
                ---------------------               (T_FunnyApp')
                Γ ⊢ L · M ∶ 𝔹

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

                --------------------              (T_FunnyAbs)
                ∅ ⊢ λ[ x ∶ 𝔹 ] N ∶ 𝔹

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

To types, we add a base type of numbers (and remove
booleans, for brevity).

\begin{code}
data Type′ : Set where
  _⇒_ : Type′ → Type′ → Type′
  ℕ : Type′
\end{code}

To terms, we add natural number constants, along with
plus, minus, and testing for zero.

\begin{code}
data Term′ : Set where
  `_ : Id → Term′
  λ[_∶_]_ : Id → Type′ → Term′ → Term′
  _·_ : Term′ → Term′ → Term′
  #_ : Data.Nat.ℕ → Term′
  _+_ : Term′ → Term′ → Term′
  _-_ : Term′ → Term′ → Term′
  if0_then_else_ : Term′ → Term′ → Term′ → Term′
\end{code}

(Assume that `m - n` returns `0` if `m` is less than `n`.)

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

