---
title     : "StlcPropNew: Properties of STLC"
permalink : /StlcPropNew
---

In this chapter, we develop the fundamental theory of the Simply
Typed Lambda Calculus---in particular, the type safety
theorem.

## Imports

\begin{code}
module StlcPropNew where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)
open import Data.String using (String; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import StlcNew
\end{code}


## Canonical Forms

The first step in establishing basic properties of reduction and typing
is to identify the possible _canonical forms_ (i.e., well-typed closed values)
belonging to each type.  For function types the canonical forms are lambda-abstractions,
while for boolean types they are values `true` and `false`.

\begin{code}
data canonical_for_ : Term → Type → Set where
  canonical-λ : ∀ {x A N B} → canonical (ƛ x ⇒ N) for (A ⇒ B)
  canonical-true : canonical true for 𝔹
  canonical-false : canonical false for 𝔹

canonical-forms : ∀ {L A} → ∅ ⊢ L ⦂ A → Value L → canonical L for A
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
data Progress (M : Term) : Set where
  steps : ∀ {N} → M ⟹ N → Progress M
  done  : Value M → Progress M

progress : ∀ {M A} → ∅ ⊢ M ⦂ A → Progress M
\end{code}

We give the proof in English first, then the formal version.

_Proof_: By induction on the derivation of `∅ ⊢ M ⦂ A`.

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
progress (⇒-I ⊢N)  =  done value-λ
progress (⇒-E ⊢L ⊢M) with progress ⊢L
... | steps L⟹L′  =  steps (ξ·₁ L⟹L′)
... | done valueL with progress ⊢M
...   | steps M⟹M′  =  steps (ξ·₂ valueL M⟹M′)
...   | done valueM with canonical-forms ⊢L valueL
...     | canonical-λ  =  steps (βλ· valueM)
progress 𝔹-I₁  =  done value-true
progress 𝔹-I₂  =  done value-false
progress (𝔹-E ⊢L ⊢M ⊢N) with progress ⊢L
... | steps L⟹L′  =  steps (ξif L⟹L′)
... | done valueL with canonical-forms ⊢L valueL
...   | canonical-true   =  steps βif-true
...   | canonical-false  =  steps βif-false
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
  progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Progress M
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

  - Variable `x` appears free, but `f` does not, in ``ƛ "f" ⇒ # "f" · # "x"``.
  - Both `f` and `x` appear free in ``(ƛ "f" ⇒ # "f" · # "x") · # "f"``.
    Indeed, `f` appears both bound and free in this term.
  - No variables appear free in ``ƛ "f" ⇒ ƛ "x" ⇒ # "f" · # "x"``.

Formally:

\begin{code}
data _∈_ : Id → Term → Set where
  free-#  : ∀ {x} → x ∈ # x
  free-ƛ  : ∀ {w x N} → w ≢ x → w ∈ N → w ∈ (ƛ x ⇒ N)
  free-·₁ : ∀ {w L M} → w ∈ L → w ∈ (L · M)
  free-·₂ : ∀ {w L M} → w ∈ M → w ∈ (L · M)
  free-if₁ : ∀ {w L M N} → w ∈ L → w ∈ (if L then M else N)
  free-if₂ : ∀ {w L M N} → w ∈ M → w ∈ (if L then M else N)
  free-if₃ : ∀ {w L M N} → w ∈ N → w ∈ (if L then M else N)
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
x≢f : "x" ≢ "f"
x≢f ()

ex₃ : "x" ∈ (ƛ "f" ⇒ # "f" · # "x")
ex₃ = free-ƛ x≢f (free-·₂ free-#)

ex₄ : "f" ∉ (ƛ "f" ⇒ # "f" · # "x")
ex₄ (free-ƛ f≢f _) = f≢f refl
\end{code}


#### Exercise: 1 star (free-in)
Prove formally the remaining examples given above.

\begin{code}
postulate
  ex₅ : "x" ∈ ((ƛ "f" ⇒ # "f" · # "x") · # "f")
  ex₆ : "f" ∈ ((ƛ "f" ⇒ # "f" · # "x") · # "f")
  ex₇ : "x" ∉ (ƛ "f" ⇒ ƛ "x" ⇒ # "f" · # "x")
  ex₈ : "f" ∉ (ƛ "f" ⇒ ƛ "x" ⇒ # "f" · # "x")
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
free-lemma : ∀ {w M A Γ} → w ∈ M → Γ ⊢ M ⦂ A → ∃[ B ](Γ ∋ w ⦂ B)
free-lemma free-# (Ax {Γ} {w} {B} ∋w) = ⟨ B , ∋w ⟩
free-lemma (free-ƛ {w} {x} w≢ ∈N) (⇒-I ⊢N) with w ≟ x
... | yes refl                           =  ⊥-elim (w≢ refl)
... | no  _    with free-lemma ∈N ⊢N
...              | ⟨ B , Z ⟩             =  ⊥-elim (w≢ refl)
...              | ⟨ B , S _ ∋w ⟩        =  ⟨ B , ∋w ⟩
free-lemma (free-·₁ ∈L) (⇒-E ⊢L ⊢M) = free-lemma ∈L ⊢L
free-lemma (free-·₂ ∈M) (⇒-E ⊢L ⊢M) = free-lemma ∈M ⊢M
free-lemma (free-if₁ ∈L) (𝔹-E ⊢L ⊢M ⊢N) = free-lemma ∈L ⊢L
free-lemma (free-if₂ ∈M) (𝔹-E ⊢L ⊢M ⊢N) = free-lemma ∈M ⊢M
free-lemma (free-if₃ ∈N) (𝔹-E ⊢L ⊢M ⊢N) = free-lemma ∈N ⊢N
\end{code}

<!--
A subtle point: if the first argument of `free-λ` was of type
`x ≢ w` rather than of type `w ≢ x`, then the type of the
term `Γx≡C` would not simplify properly; instead, one would need
to rewrite with the symmetric equivalence.
-->

As a second technical lemma, we need that any term `M` which is well
typed in the empty context is closed (has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

\begin{code}
postulate
  ∅⊢-closed : ∀ {M A} → ∅ ⊢ M ⦂ A → closed M
\end{code}

<div class="hidden">
\begin{code}
∅-empty : ∀ {x A} → ¬ (∅ ∋ x ⦂ A)
∅-empty ()

∅⊢-closed′ : ∀ {M A} → ∅ ⊢ M ⦂ A → closed M
∅⊢-closed′ ⊢M ∈M with free-lemma ∈M ⊢M
... | ⟨ B , ∋w ⟩ = ∅-empty ∋w
\end{code}
</div>

Sometimes, when we have a proof `Γ ⊢ M ⦂ A`, we will need to
replace `Γ` by a different context `Γ′`.  When is it safe
to do this?  Intuitively, the only variables we care about
in the context are those that appear free in `M`. So long
as the two contexts agree on those variables, one can be
exchanged for the other.

\begin{code}
ext : ∀ {Γ Δ}
  → (∀ {w B}     →        Γ ∋ w ⦂ B →         Δ ∋ w ⦂ B)
    -----------------------------------------------------
  → (∀ {w x A B} → Γ , x ⦂ A ∋ w ⦂ B → Δ , x ⦂ A ∋ w ⦂ B)
ext σ Z          =  Z
ext σ (S w≢ ∋w)  =  S w≢ (σ ∋w)

rename : ∀ {Γ Δ}
        → (∀ {w B} → Γ ∋ w ⦂ B → Δ ∋ w ⦂ B)
          ----------------------------------
        → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename σ (Ax ∋w)        = Ax (σ ∋w)
rename σ (⇒-I ⊢N)       = ⇒-I (rename (ext σ) ⊢N)
rename σ (⇒-E ⊢L ⊢M)    = ⇒-E (rename σ ⊢L) (rename σ ⊢M)
rename σ 𝔹-I₁           = 𝔹-I₁
rename σ 𝔹-I₂           = 𝔹-I₂
rename σ (𝔹-E ⊢L ⊢M ⊢N) = 𝔹-E (rename σ ⊢L) (rename σ ⊢M) (rename σ ⊢N)
\end{code}

We have three important corrolaries.  First,
any closed term can be weakened to any context.
\begin{code}
rename-∅ : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
rename-∅ {Γ} ⊢M = rename σ ⊢M
  where
  σ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  σ ()
\end{code}

Second, if the last two variable in a context are
equal, the term can be renamed to drop the redundant one.
\begin{code}
rename-≡ : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
rename-≡ {Γ} {x} {M} {A} {B} {C} ⊢M = rename σ ⊢M
  where
  σ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  σ Z                   =  Z
  σ (S z≢x Z)           =  ⊥-elim (z≢x refl)
  σ (S z≢x (S z≢y ∋z))  =  S z≢x ∋z
\end{code}

Third, if the last two variable in a context differ,
the term can be renamed to flip their order.
\begin{code}
rename-≢ : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B , y ⦂ A ⊢ M ⦂ C
rename-≢ {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename σ ⊢M
  where
  σ : ∀ {z C}
    → Γ , y ⦂ A , x ⦂ B ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ B , y ⦂ A ∋ z ⦂ C
  σ Z                    =  S (λ{refl → x≢y refl}) Z
  σ (S z≢x Z)            =  Z
  σ (S z≢x (S z≢y ∋z))   =  S z≢y (S z≢x ∋z)
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

_Lemma_: If `Γ , x ⦂ A ⊢ N ⦂ B` and `∅ ⊢ V ⦂ A`, then
`Γ ⊢ (N [ x := V ]) ⦂ B`.

One technical subtlety in the statement of the lemma is that we assume
`V` is closed; it has type `A` in the _empty_ context.  This
assumption simplifies the `λ` case of the proof because the context
invariance lemma then tells us that `V` has type `A` in any context at
all---we don't have to worry about free variables in `V` clashing with
the variable being introduced into the context by `λ`. It is possible
to prove the theorem under the more general assumption `Γ ⊢ V ⦂ A`,
but the proof is more difficult.

<!--
Intuitively, the substitution lemma says that substitution and typing can
be done in either order: we can either assign types to the terms
`N` and `V` separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to `N [ x := V ]`---the result is the same either
way.
-->

\begin{code}
subst : ∀ {Γ x N V A B}
  → Γ , x ⦂ A ⊢ N ⦂ B
  → ∅ ⊢ V ⦂ A
    -----------------------
  → Γ ⊢ N [ x := V ] ⦂ B

subst {Γ} {y} {# x} (Ax Z) ⊢V with x ≟ y
... | yes refl  =  rename-∅ ⊢V
... | no  x≢y   =  ⊥-elim (x≢y refl)
subst {Γ} {y} {# x} (Ax (S x≢y ∋x)) ⊢V with x ≟ y
... | yes refl  =  ⊥-elim (x≢y refl)
... | no  _     =  Ax ∋x
subst {Γ} {y} {ƛ x ⇒ N} (⇒-I ⊢N) ⊢V with x ≟ y
... | yes refl  =  ⇒-I (rename-≡ ⊢N)
... | no  x≢y   =  ⇒-I (subst (rename-≢ x≢y ⊢N) ⊢V)
subst (⇒-E ⊢L ⊢M) ⊢V     =  ⇒-E (subst ⊢L ⊢V) (subst ⊢M ⊢V)
subst 𝔹-I₁ ⊢V            =  𝔹-I₁
subst 𝔹-I₂ ⊢V            =  𝔹-I₂
subst (𝔹-E ⊢L ⊢M ⊢N) ⊢V  =  𝔹-E (subst ⊢L ⊢V) (subst ⊢M ⊢V) (subst ⊢N ⊢V)
\end{code}


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

\begin{code}
preservation : ∀ {M N A} → ∅ ⊢ M ⦂ A → M ⟹ N → ∅ ⊢ N ⦂ A
preservation (Ax ())
preservation (⇒-I ⊢N) ()
preservation (⇒-E ⊢L ⊢M) (ξ·₁ L⟹L′) with preservation ⊢L L⟹L′
... | ⊢L′  =  ⇒-E ⊢L′ ⊢M
preservation (⇒-E ⊢L ⊢M) (ξ·₂ valueL M⟹M′) with preservation ⊢M M⟹M′
... | ⊢M′  =  ⇒-E ⊢L ⊢M′
preservation (⇒-E (⇒-I ⊢N) ⊢V) (βλ· valueV)  =  subst ⊢N ⊢V
preservation 𝔹-I₁ ()
preservation 𝔹-I₂ ()
preservation (𝔹-E ⊢L ⊢M ⊢N) (ξif L⟹L′) with preservation ⊢L L⟹L′
... | ⊢L′  =  𝔹-E ⊢L′ ⊢M ⊢N
preservation (𝔹-E 𝔹-I₁ ⊢M ⊢N) βif-true   =  ⊢M
preservation (𝔹-E 𝔹-I₂ ⊢M ⊢N) βif-false  =  ⊢N
\end{code}


#### Exercise: 2 stars, recommended (subject_expansion_stlc)

<!--
An exercise in the [Types]({{ "Types" | relative_url }}) chapter asked about the
subject expansion property for the simple language of arithmetic and boolean
expressions.  Does this property hold for STLC?  That is, is it always the case
that, if `M ==> N` and `∅ ⊢ N ⦂ A`, then `∅ ⊢ M ⦂ A`?  It is easy to find a
counter-example with conditionals, find one not involving conditionals.
-->

We say that `M` _reduces_ to `N` if `M ⟹ N`,
and that `M` _expands_ to `N` if `N ⟹ M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M ==> N` and `∅ ⊢ N ⦂ A`, then `∅ ⊢ M ⦂ A`.
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
  Soundness : ∀ {M N A} → ∅ ⊢ M ⦂ A → M ⟹* N → ¬ (Stuck N)
\end{code}

<div class="hidden">
\begin{code}
Soundness′ : ∀ {M N A} → ∅ ⊢ M ⦂ A → M ⟹* N → ¬ (Stuck N)
Soundness′ ⊢M (M ∎) ⟨ ¬M⟹N , ¬ValueM ⟩ with progress ⊢M
... | steps M⟹N   =  ¬M⟹N M⟹N
... | done  ValueM  =  ¬ValueM ValueM
Soundness′ ⊢L (L ⟹⟨ L⟹M ⟩ M⟹*N) = Soundness′ ⊢M M⟹*N
  where
  ⊢M = preservation ⊢L L⟹M
\end{code}
</div>


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

                 -------------------              (ST_Foo1)
                 (λ x ⇒ # x) ⟹ foo

                    ------------                  (ST_Foo2)
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

             Γ ⊢ L ⦂ 𝔹 ⇒ 𝔹 ⇒ 𝔹
             Γ ⊢ M ⦂ 𝔹
             ------------------------------          (T_FunnyApp)
             Γ ⊢ L · M ⦂ 𝔹

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

                Γ ⊢ L ⦂ 𝔹
                Γ ⊢ M ⦂ 𝔹
                ---------------------               (T_FunnyApp')
                Γ ⊢ L · M ⦂ 𝔹

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
                ∅ ⊢ λ[ x ⦂ 𝔹 ] N ⦂ 𝔹

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation
