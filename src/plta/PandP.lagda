---
title     : "PandP: Progress and Preservation"
layout    : page
permalink : /PandP/
---

\begin{code}
module plta.PandP where
\end{code}

[Parts of this chapter take their text from chapter _StlcProp_
of _Software Foundations_ (_Programming Language Foundations_).
Those parts will be revised.]

The last chapter formalised simply-typed lambda calculus and
introduced several important relations over it.
We write `Value M` if term `M` is a value.
We write `M ⟶ N` if term `M` reduces to term `N`.
And we write `Γ ⊢ M ⦂ A` if in context `Γ` the term `M` has type `A`.
We are particularly concerned with terms typed in the empty context
`∅`, which must be _closed_ (that is, have no _free variables_).

Ultimately, we would like to show that we can keep reducing a term
until we reach a value.  For instance, if `M` is a term of type natural,
we would like to show that ultimately it reduces to a term representing
some specific natural number.  We have seen two examples in the previous
chapter, where the terms

    plus · two · two

and

    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

both reduce to `` `suc `suc `suc `suc `zero ``,
which represents the natural number four.

What we might expect is that every term is either a value or can take
a reduction step.  As we will see, this property does _not_ hold for
every term, but it does hold for every closed, well-typed term.

_Progress_: If `∅ ⊢ M ⦂ A` then either `M` is a value or there is an `N` such
that `M ⟶ N`.

So, either we have a value, and we are done, or we can take a reduction step.
In the latter case, we would like to apply progress again. But first we need
to know that the term yielded by the reduction is itself closed and well-typed.
It turns out that this property holds whenever we start with a closed,
well-typed term.

_Preservation_: If `∅ ⊢ M ⦂ A` and `M ⟶ N` then `∅ ⊢ N ⦂ A`.

This gives us a recipe for evaluation. Start with a closed and well-typed term.
By progress, it is either a value, in which case we are done, or it reduces
to some other term.  By preservation, that other term will itself be closed
and well-typed.  Repeat.  We will either loop forever, in which case evaluation
does not terminate, or we will eventually reach a value, which is guaranteed
to be closed and of the same type as the original term.  We will turn this
recipe into Agda code that can compute for us the reduction sequence of
`plus · two · two`, and its Church numeral variant.

In this chapter we will prove _Preservation_ and _Progress_, and show
how to apply them to get Agda to evaluate terms.

The development in this chapter was inspired by the corresponding
development in in _Software Foundations, volume _Programming Language
Foundations_, chapter _StlcProp_.  It will turn out that one of our technical choices
(to introduce an explicit judgment `Γ ∋ x ⦂ A` in place of
treating a context as a function from identifiers to types)
permits a simpler development. In particular, we can prove substitution preserves
types without needing to develop a separate inductive definition of the
`appears_free_in` relation.


## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plta.Isomorphism
open import plta.Lambda
open Chain (Term) (_⟶_)
\end{code}


## Canonical Forms

Well-typed values must take one of a small number of _canonical forms_.
We provide an analogue of the `Value` relation that relates values
to their types.  A lambda expression must have a function type,
and a zero or successor expression must be a natural.
Further, the body of a function must be well-typed in a context
containing only its bound variable, and the argument of successor
must itself be canonical.
\begin{code}
infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ
\end{code}    

Every closed, well-typed value is canonical.
\begin{code}
canonical : ∀ {V A}
  → ∅ ⊢ V ⦂ A
  → Value V
    -----------
  → Canonical V ⦂ A
canonical (Ax ())          ()
canonical (⊢ƛ ⊢N)          V-ƛ         =  C-ƛ ⊢N
canonical (⊢L · ⊢M)        ()
canonical ⊢zero            V-zero      =  C-zero
canonical (⊢suc ⊢V)        (V-suc VV)  =  C-suc (canonical ⊢V VV)
canonical (⊢case ⊢L ⊢M ⊢N) ()
canonical (⊢μ ⊢M)          ()
\end{code}
There are only three interesting cases to consider. 

* If the term is a lambda abstraction, then well-typing of the term
  guarantees well-typing of the body.

* If the term is zero than it is canonical trivially.

* If the term is a successor then since it is well-typed its argument
  is well-typed, and since it is a value its argument is a value.
  Hence, by induction its argument is also canonical.

The variable case is thrown out because a closed term has no free
variables and because a variable is not a value.  The cases for
application, zero, successor, and fixpoint are thrown out because they
are not values.

Conversely, if a term is canonical then it is a value
and it is well-typed in the empty context.
\begin{code}
value : ∀ {M A}
  → Canonical M ⦂ A
    ----------------
  → Value M
value (C-ƛ ⊢N)    =  V-ƛ
value C-zero      =  V-zero
value (C-suc CM)  =  V-suc (value CM)

typed : ∀ {M A}
  → Canonical M ⦂ A
    ---------------
  → ∅ ⊢ M ⦂ A
typed (C-ƛ ⊢N)    =  ⊢ƛ ⊢N
typed C-zero      =  ⊢zero
typed (C-suc CM)  =  ⊢suc (typed CM)
\end{code}
The proofs are straightforward, and again use induction in the
case of successor.


## Progress

We would like to show that every term is either a value or takes a
reduction step.  However, this is not true in general.  The term

    `zero · `suc `zero

is neither a value nor can take a reduction step. And if `` s ⦂ `ℕ ⇒ `ℕ ``
then the term

     s · `zero

cannot reduce because we do not know which function is bound to the
free variable `s`.  The first of those terms is ill-typed, and the
second has a free variable.  Every term that is well-typed and closed
has the desired property.

_Progress_: If `∅ ⊢ M ⦂ A` then either `M` is a value or there is an `N` such
that `M ⟶ N`.

To formulate this property, we first introduce a relation that
captures what it means for a term `M` to make progess.
\begin{code}
data Progress (M : Term) : Set where

  step : ∀ {N}
    → M ⟶ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
\end{code}
A term `M` makes progress if either it can take a step, meaning there
exists a term `N` such that `M ⟶ N`, or if it is done, meaning that
`M` is a value.

If a term is well-typed in the empty context then it is a value.
\begin{code}
progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (Ax ())
progress (⊢ƛ ⊢N)                             =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L⟶L′                            =  step (ξ-·₁ L⟶L′)
... | done VL with progress ⊢M
...   | step M⟶M′                          =  step (ξ-·₂ VL M⟶M′)
...   | done VM with canonical ⊢L VL
...     | C-ƛ _                              =  step (β-ƛ· VM)
progress ⊢zero                               =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M⟶M′                           =  step (ξ-suc M⟶M′)
...  | done VM                               =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L⟶L′                            =  step (ξ-case L⟶L′)
... | done VL with canonical ⊢L VL
...   | C-zero                               =  step β-case-zero
...   | C-suc CL                             =  step (β-case-suc (value CL))
progress (⊢μ ⊢M)                             =  step β-μ
\end{code}
We induct on the evidence that `M` is well-typed.
Let's unpack the first three cases.  

* The term cannot be a variable, since no variable is well typed
  in the empty context.

* If the term is a lambda abstraction then it is a value.

* If the term is an application `L · M`, recursively apply
  progress to the derivation that `L` is well-typed.

  + If the term steps, we have evidence that `L ⟶ L′`,
    which by `ξ-·₁` means that our original term steps
    to `L′ · M`

  + If the term is done, we have evidence that `L` is
    a value. Recursively apply progress to the derivation
    that `M` is well-typed.

    - If the term steps, we have evidence that `M ⟶ M′`,
      which by `ξ-·₂` means that our original term steps
      to `L · M′`.  Step `ξ-·₂` applies only if we have
      evidence that `L` is a value, but progress on that
      subterm has already supplied the required evidence.

    - If the term is done, we have evidence that `M` is
      a value.  We apply the canonical forms lemma to the
      evidence that `L` is well typed and a value, which
      since we are in an application leads to the
      conclusion that `L` must be a lambda
      abstraction.  We also have evidence that `M` is
      a value, so our original term steps by `β-ƛ·`.

The remaining cases, for zero, successor, case, and fixpoint,
are similar.

Our code reads neatly in part because we consider the
`step` option before the `done` option. We could, of course,
do it the other way around, but then the `...` abbreviation
no longer works, and we will need to write out all the arguments
in full. In general, the rule of thumb is to consider the easy case
(here `step`) before the hard case (here `done`).
If you have two hard cases, you will have to expand out `...`
or introduce subsidiary functions.

Instead of defining a data type for `Progress M`, we could
have formulated progress using disjunction and existentials:
\begin{code}
postulate
  progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M ⟶ N)
\end{code}
This leads to a less perspicous proof.  Instead of the mnemonic `done`
and `step` we use `inj₁` and `inj₂`, and the term `N` is no longer
implicit and so must be written out in full.  In the case for `β-ƛ·`
this requires that we match against the lambda expression `L` to
determine its bound variable and body, `ƛ x ⇒ N`, so we can show that
`L · M` reduces to `N [ x := M ]`.

#### Exercise (`progress′`)

Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.

#### Exercise (`Progress-iso`)

Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M ⟶ N)`.


## Prelude to preservation

The other property we wish to prove, preservation of typing under
reduction, turns out to require considerably more work.  Our proof
draws on a line of work by Thorsten Altenkirch, Conor McBride,
James McKinna, and others.  The proof has three key steps.

The first step is to show that types are preserved by _renaming_.

_Renaming_:
Let `Γ` and `Δ` be two context such that every variable that
appears in `Γ` also appears with the same type in `Δ`.  Then
if a term is typable under `Γ`, it has the same type under `Δ`.

In symbols,

    Γ ∋ x ⦂ A  →  Δ ∋ x ⦂ A
    -----------------------
    Γ ⊢ M ⦂ A  →  Δ ∋ M ⦂ A

Special cases of renaming include _weakening_ (where `Δ` is an
extension of `Γ`) and _swapping_ (reordering the occurrence of
variables in `Γ` and `Δ`).  Our renaming lemma is similar to the
_context invariance_ lemma in _Software Foundations_, but does not
require a separate definition of the `appears_free_in` relation
which is needed there.

The second step is to show that types are preserved by
_substitution_.

_Substitution_:
Say we have a closed term `V` of type `A`, and under the
assumption that `x` has type `A` the term `N` has type `B`.
Then substituting `V` for `x` in `N` yields a term that
also has type `B`.

In symbols,

    ∅ ⊢ V ⦂ A
    Γ , x ⦂ A ⊢ N ⦂ B
    ------------------
    Γ ⊢ N [x := V] ⦂ B

The result does not depend on `V` being a value, but it does
require that `V` be closed; recall that we restricted our attention
to substitution by closed terms in order to avoid the need to
rename bound variables.  The term into which we are substituting
is typed in an arbitrary context `Γ`, extended by the variable
`x` for which we are substituting; and the result term is typed
in `Γ`. 

The lemma establishes that substitution composes well with typing:
if we first type the components separately and then combine them we get
the same result as if we first substitute and then type the result.

The third step is to show preservation.

_Preservation_:
If `∅ ⊢ M ⦂ A` and `M ⟶ N` then `∅ ⊢ N ⦂ A`.

The proof is by induction over the possible reductions, and
the substitution lemma is crucial in showing that each of the
`β` rules which uses substitution preserves types.

We now proceed with our three-step programme.


## Renaming

We often need to "rebase" a type derivation, replacing a
derivation `Γ ⊢ M ⦂ A` by a related derivation `Δ ⊢ M ⦂ A`.
We may do so as long as every variable that appears in
`Γ` also appears in `Δ`, and with the same type.

Three of the rules for typing (lambda abstraction, case on naturals,
and fixpoint) have hypotheses that extend the context to include a
bound variable. In each of these rules, `Γ` appears in the conclusion
and `Γ , x ⦂ A` appears in a hypothesis.  Thus:

    Γ , x ⦂ A ⊢ N ⦂ B
    ------------------- ⊢ƛ
    Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

for lambda expressions, and similarly for case and fixpoint.  To deal
with this situation, we first prove a lemma showing that if one context
extends another, this is still true after adding the same variable to
both contexts.
\begin{code}
ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)

ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)
\end{code}
Let `ρ` be the name of the map that takes evidence that
`x` appears in `Γ` to evidence that `x` appears in `Δ`.
The proof is by induction on the evidence that `x` appears
in the extended map `Γ , y ⦂ B`. If `x` is the same as `y`,
we used `Z` to access the last variable in the extended `Γ`;
and can similarly use `Z` to access the last variable in the
extended `Δ`.  If `x` differs from `y`, then we used `S`
to skip over the last variable in the extended `Γ`, where
`x≢y` is evidence that `x` and `y` differ, and `∋x` is the
evidence that `x` appears in `Γ`; and we can similarly use
`S` to skip over the last variable in the extended `Δ`,
applying `ρ` to find the evidence that `w` appears
in `Δ`.

With this lemma under our belts, it is straightforward to
prove renaming preserves types.
\begin{code}
rename : ∀ {Γ Δ}
        → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
          ----------------------------------
        → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (Ax ∋w)           =  Ax (ρ ∋w)
rename ρ (⊢ƛ ⊢N)           =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)         =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero             =  ⊢zero
rename ρ (⊢suc ⊢M)         =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)  =  ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)           =  ⊢μ (rename (ext ρ) ⊢M)
\end{code}
As before, let `ρ` be the name of the map that takes evidence that
`x` appears in `Γ` to evidence that `x` appears in `Δ`.  We induct
on the evidence that `M` is well-typed in `Γ`.  Let's unpack the
first three cases.

* If the term is a variable, then applying `ρ` to the evidence
that the variable appears in `Γ` yields the corresponding evidence that
the variable appears in `Δ`.

* If the term is a lambda abstraction, use the previous lemma to
extend the map `ρ` suitably and recursively rename the body of the
abstraction

* If the term is an application, recursively rename both the
function and the argument.

The remaining cases, for zero, successor, case, and fixpoint, are
similar.  In case and fixpoint, as with lambda abstraction, map `ρ`
needs to be extended to account for the bound variable.  The induction
is over the derivation that the term is well-typed, so the extension
doesn't invalidate the inductive hypothesis. Equivalently, the
recursion terminates because the second argument is always smaller,
even though the first argument sometimes grows larger.

We have three important corollaries, each proved by constructing
a suitable map between contexts.  First,
any closed term can be weakened to any context.
\begin{code}
rename-∅ : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
rename-∅ {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()
\end{code}
Here the map `ρ` is trivial, since there are no possible
arguments in the empty context `∅`.

Second, if the last two variables in a context are
equal, the term can be renamed to drop the redundant one.
\begin{code}
rename-≡ : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
rename-≡ {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                 =  Z
  ρ (S x≢x Z)         =  ⊥-elim (x≢x refl)
  ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z
\end{code}
Here map `ρ` can never be invoked on the inner occurence of `x` since
it is masked by the outer occurence.  Skipping over the `x` in the
first position can only happen if the variable looked for differs from
`x` (the evidence for which is `x≢x` or `z≢x`) but if the variable is
found in the second position, which also contains `x`, this leads to a
contradiction (evidenced by `x≢x refl`).

Third, if the last two variables in a context differ,
the term can be renamed to flip their order.
\begin{code}
rename-≢ : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
rename-≢ {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z                   =  S x≢y Z
  ρ (S y≢x Z)           =  Z
  ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)
\end{code}
Here the renaming map takes a variable at the end into a variable one
from the end, and vice versa.  The first line is responsible for
moving `x` from a position at the end to a position one from the end
with `y` at the end, and requires the provided evidence that `x ≢ y`.


## Substitution

The key to preservation – and the trickiest bit of the proof – is
the lemma establishing that substitution preserves types.

Recall that in order to avoid renaming bound variables,
substitution is restricted to be by closed terms only.
This restriction was not enforced by our definition of substitution,
but it is captured by our lemma to assert that substitution
preserves typing.

Our concern is with reducing closed terms, which means that when
we apply `β` reduction, the term substituted in contains a single
free variable (the bound variable of the lambda abstraction, or
similarly for case or fixpoint). However, substitution
is defined by recursion, and as we descend into terms with bound
variables the context grows.  So for the induction to go through,
we require an arbitrary context `Γ`, as in the statement of the lemma.

Here is the formal statement and proof that substitution preserves types.
\begin{code}
subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (Ax {x = x} Z) with x ≟ y
... | yes refl     =  rename-∅ ⊢V
... | no  x≢y      =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (Ax {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl     =  ⊥-elim (x≢y refl)
... | no  _        =  Ax ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl     =  ⊢ƛ (rename-≡ ⊢N)
... | no  x≢y      =  ⊢ƛ (subst ⊢V (rename-≢ x≢y ⊢N))
subst ⊢V (⊢L · ⊢M) = subst ⊢V ⊢L · subst ⊢V ⊢M
subst ⊢V ⊢zero     =  ⊢zero
subst ⊢V (⊢suc ⊢M) =  ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl     =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (rename-≡ ⊢N)
... | no  x≢y      =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (rename-≢ x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl     =  ⊢μ (rename-≡ ⊢M)
... | no  x≢y      =  ⊢μ (subst ⊢V (rename-≢ x≢y ⊢M))
\end{code}
We induct on the evidence that `N` is well-typed in the
context `Γ` extended by `x`.

Immediately, we note a wee issue with naming.  In the lemma
statement, the variable `x` is an implicit parameter for the variable
substituted, while in the type rules for variables, abstractions,
cases, and fixpoints, the variable `x` is an implicit parameter for
the relevant variable.  We are going to need to get hold of both
variables, so we use the syntax `{x = y}` to bind `y` to the
substituted variable and the syntax `{x = x}` to bind `x` to the
relevant variable in the patterns for `Ax`, `⊢ƛ`, `⊢case`, and `⊢μ`.
Using the name `y` here is consistent with the naming in the original
definition of substitution in the previous chapter.  The proof never
mentions the types of `x`, `y`, `V`, or `N`, so in what follows we
choose type name as convenient.

Now let's unpack the first three cases.

* In the variable case, given `∅ ⊢ V ⦂ B` and `Γ , y ⦂ B ⊢ ⌊ x ⌋ ⦂ A`,
  we need to show `Γ ⊢ x [ y := V ] ⦂ A`.  There are two subcases,
  depending on the evidence demonstrating `Γ , y ⦂ B ∋ x ⦂ A`.

  + If `x` appears at the end of the context, as evidenced by `Z`,
    then `x` and `y` are necessarily identical, as are `A` and `B`.
    Nonetheless, we must evaluate `x ≟ y` in order to allow the
    definition of substitution to simplify.

    - If the variables are equal, then `x [ x := V ]` simplifies to
      `V`, and the weakening lemma `rename-∅` applied to evidence of 
      `∅ ⊢ V ⦂ A` yields evidence that `Γ ⊢ V ⦂ A`, as required.
 
    - If the variables are unequal, we have a contradiction and the
      result follows immediately by `⊥-elim`.

  + If `x` appears elsewhere in the context, as evidenced by `S x≢y
    ∋x`, then `x` and `y` are necessarily distinct.  Nonetheless, we
    must again evaluate `x ≟ y` in order to allow the definition of
    substitution to simplify.

    - If the variables are equal, we have a contradiction and the
      result follows immediately by `⊥-elim`.

    - If the variables are unequal, then `x [ y := V ]` simplifies to
      `x`, and `∋x` provides evidence that `Γ ∋ x ⦂ A`, as required.

* In the abstraction case, given `∅ ⊢ V ⦂ B` and `Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C`
  we need to show `Γ ⊢ (ƛ x ⇒ N) [ y := V ] ⦂ A ⇒ C`.  We evaluate `x ≟ y` in
  order to allow the definition of substitution to simplify.

  + If the variables are equal, then `(ƛ x ⇒ N) [ x := V ]` simplifies
    to `ƛ x ⇒ N`, and the drop lemma `rename-≡` applied to evidence of
    `Γ , x ⦂ B , x ⦂ A ⊢ N ⦂ C` yields evidence that `Γ , x ⦂ A ⊢ N ⦂ C`.
    The typing rule for abstractions then yields `Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ C`,
    as required.


  + If the variables are unequal, then `(ƛ x ⇒ N) [ y := V ]` simplifies
    to `ƛ x ⇒ (N [ y := V ])`.  The swap lemma `rename-≢` applied to
    evidence of `Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C` yields evidence that
    `Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C`, which allows us to apply the inductive
    hypothesis to conclude `Γ , x ⦂ A ⊢ N [ y := V ] ⦂ C`. By the typing
    rule for abstactions we then have `Γ ⊢ ƛ x ⇒ (N [ y := V ]) ⦂ A ⇒ C`,
    as required.

* In the application case, given `∅ ⊢ V ⦂ C` and `Γ , y ⦂ C ⊢ L ⦂ A ⇒ B` and
  `Γ , y ⦂ C ⊢ M ⦂ A`.  Applying the induction hypothesis to `L` and `M`
  `Γ ⊢ L [ y := V ] ⦂ A ⇒ B` and `Γ ⊢ M [ y := V ] ⦂ A`.  By the typing rule
  for applications we then have `Γ ⊢ (L · M) [ y := V ] ⦂ B` as required.

The remaining cases, for zero, successor, case, and fixpoint,
are similar.


---

revised attempt

---

* In the variable case, we must show

    ∅ ⊢ V ⦂ B
    Γ , y ⦂ B ⊢ ⌊ x ⌋ ⦂ A
    ------------------------
    Γ ⊢ ⌊ x ⌋ [ y := V ] ⦂ A

  There are two subcases, depending on the evidence demonstrating
  `Γ , y ⦂ B ∋ x ⦂ A`.

  + If `x` appears at the end of the context, as evidenced by `Z`,
    then `x` and `y` are necessarily identical, as are `A` and `B`.
    Nonetheless, we must evaluate `x ≟ y` in order to allow the
    definition of substitution to simplify.

    - If the variables are equal, then after simplification we
      must show

        ∅ ⊢ V ⦂ A
        Γ , x ⦂ A ⊢ ⌊ x ⌋ ⦂ A
        ------------------------
        Γ ⊢ V ⦂ A

      The first hypothesis implies the conclusion by the weakening
      lemma `rename-∅`.

    - If the variables are unequal we have a contradiction.

  + If `x` appears elsewhere in the context, as evidenced by `S x≢y ∋x`,
    then `x` and `y` are necessarily distinct.  Nonetheless, we
    must again evaluate `x ≟ y` in order to allow the definition of
    substitution to simplify.

    - If the variables are equal we have a contradiction.

    - If the variables are unequal, then after simplification we
      must show

        ∅ ⊢ V ⦂ B
        Γ , y ⦂ B ⊢ ⌊ x ⌋ ⦂ A
        ------------------------
        Γ ⊢ ⌊ x ⌋ ⦂ A

      This follows immediately, since `∋x` provides evidence that `Γ ∋ x ⦂ A`.

* In the abstraction case, we must show

    ∅ ⊢ V ⦂ B
    Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C
    --------------------------------
    Γ ⊢ (ƛ x ⇒ N) [ y := V ] ⦂ A ⇒ C

  We evaluate `x ≟ y` in order to allow the definition of substitution to simplify.

  + If the variables are equal then after simplification we must show

      ∅ ⊢ V ⦂ B
      Γ , x ⦂ B , x ⦂ A ⊢ N ⦂ C
      -------------------------
      Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ C

    From the drop lemma, `rename-≡`, we may conclude

      Γ , x ⦂ B , x ⦂ A ⊢ N ⦂ C
      -------------------------
      Γ , x ⦂ A ⊢ N ⦂ C

    The typing rule for abstractions then yields the required conclusion.    

  + If the variables are unequal then after simplification we must show

      ∅ ⊢ V ⦂ B
      Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C
      --------------------------------
      Γ ⊢ ƛ x ⇒ (N [ y := V ]) ⦂ A ⇒ C

    From the swap lemma, `rename-≢`, we may conclude

      Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C
      -------------------------
      Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C

    The inductive hypothesis gives us

      ∅ ⊢ V ⦂ B
      Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C        
      ------------------------------------
      Γ , x ⦂ A , y ⦂ B ⊢ N [ y := V ] ⦂ C

    The typing rule for abstractions then yields the required conclusion.

* In the application case, we must show

    ∅ ⊢ V ⦂ C
    Γ , y ⦂ C ⊢ L ⦂ A ⇒ B
    Γ , y ⦂ C ⊢ M ⦂ A
    ------------------------------
    Γ ⊢ (L · M) [ y := V ] ⦂ B

  By the definition of substitution, we must show

    Γ ⊢ (L [ y := V ]) · (M [ y := V ])

  Applying the induction hypothesis for `L` and `M` and the typing
  rule for applications yields the required conclusion.

The remaining cases, for zero, successor, case, and fixpoint,
are similar.




### Main Theorem

Once we have shown that substitution preserves types, showing
that reduction preserves types is straightforward.

\begin{code}
preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M ⟶ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (Ax ())
preserve (⊢ƛ ⊢N)                 ()
preserve (⊢L · ⊢M)               (ξ-·₁ L⟶L′)     =  (preserve ⊢L L⟶L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M⟶M′)  =  ⊢L · (preserve ⊢M M⟶M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ· VV)        =  subst ⊢V ⊢N
preserve ⊢zero                   ()
preserve (⊢suc ⊢M)               (ξ-suc M⟶M′)    =  ⊢suc (preserve ⊢M M⟶M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L⟶L′)   =  ⊢case (preserve ⊢L L⟶L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     β-case-zero      =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-case-suc VV)  =  subst ⊢V ⊢N 
preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M
\end{code}


## Normalisation

\begin{code}
Gas : Set
Gas = ℕ

data Normalise (M : Term) : Set where

  out-of-gas : ∀ {N A}
    → M ⟶* N
    → ∅ ⊢ N ⦂ A
      -------------
    → Normalise M

  normal : ∀ {V}
    → Gas
    → M ⟶* V
    → Value V
     --------------
    → Normalise M

normalise : ∀ {M A}
  → Gas
  → ∅ ⊢ M ⦂ A
    -----------
  → Normalise M
normalise {L} zero    ⊢L                   =  out-of-gas (L ∎) ⊢L
normalise {L} (suc m) ⊢L with progress ⊢L
...  | done VL                             =  normal (suc m) (L ∎) VL
...  | step L⟶M with normalise m (preserve ⊢L L⟶M)
...          | out-of-gas M⟶*N ⊢N        =  out-of-gas (L ⟶⟨ L⟶M ⟩ M⟶*N) ⊢N
...          | normal n M⟶*V VV          =  normal n (L ⟶⟨ L⟶M ⟩ M⟶*V) VV
\end{code}

### Examples

\begin{code}
_ : normalise 100 ⊢four ≡
  normal 88
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
      ])))
   · `suc (`suc `zero)
   · `suc (`suc `zero)
   ⟶⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
         ])))
      · ⌊ "m" ⌋
      · ⌊ "n" ⌋)
     ]))
   · `suc (`suc `zero)
   · `suc (`suc `zero)
   ⟶⟨ ξ-·₁ (β-ƛ· (V-suc (V-suc V-zero))) ⟩
   (ƛ "n" ⇒
    `case `suc (`suc `zero) [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
        ])))
     · ⌊ "m" ⌋
     · ⌊ "n" ⌋)
    ])
   · `suc (`suc `zero)
   ⟶⟨ β-ƛ· (V-suc (V-suc V-zero)) ⟩
   `case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
       ])))
    · ⌊ "m" ⌋
    · `suc (`suc `zero))
   ]
   ⟶⟨ β-case-suc (V-suc V-zero) ⟩
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
       ])))
    · `suc `zero
    · `suc (`suc `zero))
   ⟶⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
   `suc
   ((ƛ "m" ⇒
     (ƛ "n" ⇒
      `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
          ])))
       · ⌊ "m" ⌋
       · ⌊ "n" ⌋)
      ]))
    · `suc `zero
    · `suc (`suc `zero))
   ⟶⟨ ξ-suc (ξ-·₁ (β-ƛ· (V-suc V-zero))) ⟩
   `suc
   ((ƛ "n" ⇒
     `case `suc `zero [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
         ])))
      · ⌊ "m" ⌋
      · ⌊ "n" ⌋)
     ])
    · `suc (`suc `zero))
   ⟶⟨ ξ-suc (β-ƛ· (V-suc (V-suc V-zero))) ⟩
   `suc
   `case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
       ])))
    · ⌊ "m" ⌋
    · `suc (`suc `zero))
   ]
   ⟶⟨ ξ-suc (β-case-suc V-zero) ⟩
   `suc
   (`suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
        ])))
     · `zero
     · `suc (`suc `zero)))
   ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
   `suc
   (`suc
    ((ƛ "m" ⇒
      (ƛ "n" ⇒
       `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
           ])))
        · ⌊ "m" ⌋
        · ⌊ "n" ⌋)
       ]))
     · `zero
     · `suc (`suc `zero)))
   ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ· V-zero))) ⟩
   `suc
   (`suc
    ((ƛ "n" ⇒
      `case `zero [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
          ])))
       · ⌊ "m" ⌋
       · ⌊ "n" ⌋)
      ])
     · `suc (`suc `zero)))
   ⟶⟨ ξ-suc (ξ-suc (β-ƛ· (V-suc (V-suc V-zero)))) ⟩
   `suc
   (`suc
    `case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
        ])))
     · ⌊ "m" ⌋
     · `suc (`suc `zero))
    ])
   ⟶⟨ ξ-suc (ξ-suc β-case-zero) ⟩ `suc (`suc (`suc (`suc `zero))) ∎)
  (V-suc (V-suc (V-suc (V-suc V-zero))))
_ = refl
\end{code}

\begin{code}
_ : normalise 100 ⊢fourᶜ ≡
  normal 88
  ((ƛ "m" ⇒
    (ƛ "n" ⇒
     (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "m" ⌋ · ⌊ "s" ⌋ · (⌊ "n" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋)))))
   · (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)))
   · (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)))
   · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
   · `zero
   ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ· V-ƛ))) ⟩
   (ƛ "n" ⇒
    (ƛ "s" ⇒
     (ƛ "z" ⇒
      (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · ⌊ "s" ⌋ ·
      (⌊ "n" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋))))
   · (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)))
   · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
   · `zero
   ⟶⟨ ξ-·₁ (ξ-·₁ (β-ƛ· V-ƛ)) ⟩
   (ƛ "s" ⇒
    (ƛ "z" ⇒
     (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · ⌊ "s" ⌋ ·
     ((ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · ⌊ "s" ⌋ · ⌊ "z" ⌋)))
   · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
   · `zero
   ⟶⟨ ξ-·₁ (β-ƛ· V-ƛ) ⟩
   (ƛ "z" ⇒
    (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
    ·
    ((ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
     · ⌊ "z" ⌋))
   · `zero
   ⟶⟨ β-ƛ· V-zero ⟩
   (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
   ·
   ((ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
    · `zero)
   ⟶⟨ ξ-·₁ (β-ƛ· V-ƛ) ⟩
   (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
   ((ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
    · `zero)
   ⟶⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ· V-ƛ)) ⟩
   (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
   ((ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
    `zero)
   ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· V-zero) ⟩
   (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
   ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · `zero))
   ⟶⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ· V-zero)) ⟩
   (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
   ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · `suc `zero)
   ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· (V-suc V-zero)) ⟩
   (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
   `suc (`suc `zero)
   ⟶⟨ β-ƛ· (V-suc (V-suc V-zero)) ⟩
   (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · `suc (`suc `zero))
   ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· (V-suc (V-suc V-zero))) ⟩
   (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · `suc (`suc (`suc `zero)) ⟶⟨
   β-ƛ· (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero))) ∎)
  (V-suc (V-suc (V-suc (V-suc V-zero))))
_ = refl
\end{code}




#### Exercise: 2 stars, recommended (subject_expansion_stlc)

<!--
An exercise in the [Types]({{ "Types" | relative_url }}) chapter asked about the
subject expansion property for the simple language of arithmetic and boolean
expressions.  Does this property hold for STLC?  That is, is it always the case
that, if `M ==> N` and `∅ ⊢ N ⦂ A`, then `∅ ⊢ M ⦂ A`?  It is easy to find a
counter-example with conditionals, find one not involving conditionals.
-->

We say that `M` _reduces_ to `N` if `M ⟶ N`,
and that `M` _expands_ to `N` if `N ⟶ M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M ==> N` and `∅ ⊢ N ⦂ A`, then `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.

## Type Soundness

#### Exercise: 2 stars, optional (type_soundness)

Put progress and preservation together and show that a well-typed
term can _never_ reach a stuck state.

\begin{code}
Normal : Term → Set
Normal M = ∀ {N} → ¬ (M ⟶ N)

Stuck : Term → Set
Stuck M = Normal M × ¬ Value M

postulate
  Soundness : ∀ {M N A}
    → ∅ ⊢ M ⦂ A
    → M ⟶* N
      -----------
    → ¬ (Stuck N)
\end{code}

<div class="hidden">
\begin{code}
Soundness′ : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M ⟶* N
    -----------
  → ¬ (Stuck N)
Soundness′ ⊢M (M ∎) ⟨ ¬M⟶N , ¬VM ⟩ with progress ⊢M
... | step M⟶N                      =  ¬M⟶N M⟶N
... | done VM                         =  ¬VM VM
Soundness′ ⊢L (L ⟶⟨ L⟶M ⟩ M⟶*N)  =  Soundness′ (preserve ⊢L L⟶M) M⟶*N
\end{code}
</div>


## Additional Exercises

#### Exercise: 1 star (progress_preservation_statement)

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.

#### Exercise: 2 stars (stlc_variation1)

Suppose we add a new term `zap` with the following reduction rule

                     ---------                  (ST_Zap)
                     M ⟶ zap

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

                 -------------------              (Foo₁)
                 (λ x ⇒ ⌊ x ⌋) ⟶ foo

                    ------------                  (Foo₂)
                    foo ⟶ true

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation

#### Exercise: 2 stars (stlc_variation3)

Suppose instead that we remove the rule `ξ·₁` from the `⟶`
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

     ----------------------------------------      (FunnyCaseZero)
     case zero [zero⇒ M |suc x ⇒ N ] ⟶ true

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

             Γ ⊢ L ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
             Γ ⊢ M ⦂ `ℕ
             ------------------------------          (FunnyApp)
             Γ ⊢ L · M ⦂ `ℕ

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

                Γ ⊢ L ⦂ `ℕ
                Γ ⊢ M ⦂ `ℕ
                ---------------------               (FunnyApp')
                Γ ⊢ L · M ⦂ `ℕ

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation



#### Exercise : 2 stars, optional (stlc_variation7)

Suppose we add the following new rule to the typing relation
of the STLC:

                --------------------              (T_FunnyAbs)
                ∅ ⊢ ƛ x ⇒ N ⦂ `ℕ

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation




