---
title     : "Properties: Progress and Preservation"
layout    : page
prev      : /Lambda/
permalink : /Properties/
next      : /DeBruijn/
---

```
module plfa.part2.Properties where
```

This chapter covers properties of the simply-typed lambda calculus, as
introduced in the previous chapter.  The most important of these
properties are progress and preservation.  We introduce these below,
and show how to combine them to get Agda to compute reduction
sequences for us.


## Imports

```
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plfa.part1.Isomorphism
open import plfa.part2.Lambda
```


## Introduction

The last chapter introduced simply-typed lambda calculus,
including the notions of closed terms, terms that are values,
reducing one term to another, and well-typed terms.

Ultimately, we would like to show that we can keep reducing a term
until we reach a value.  For instance, in the last chapter we showed
that two plus two is four,

    plus · two · two  —↠  `suc `suc `suc `suc `zero

which was proved by a long chain of reductions, ending in the value
on the right.  Every term in the chain had the same type, `` `ℕ ``.
We also saw a second, similar example involving Church numerals.

What we might expect is that every term is either a value or can take
a reduction step.  As we will see, this property does _not_ hold for
every term, but it does hold for every closed, well-typed term.

_Progress_: If `∅ ⊢ M ⦂ A` then either `M` is a value or there is an `N` such
that `M —→ N`.

So, either we have a value, and we are done, or we can take a reduction step.
In the latter case, we would like to apply progress again. But to do so we need
to know that the term yielded by the reduction is itself closed and well typed.
It turns out that this property holds whenever we start with a closed,
well-typed term.

_Preservation_: If `∅ ⊢ M ⦂ A` and `M —→ N` then `∅ ⊢ N ⦂ A`.

This gives us a recipe for automating evaluation. Start with a closed
and well-typed term.  By progress, it is either a value, in which case
we are done, or it reduces to some other term.  By preservation, that
other term will itself be closed and well typed.  Repeat.  We will
either loop forever, in which case evaluation does not terminate, or
we will eventually reach a value, which is guaranteed to be closed and
of the same type as the original term.  We will turn this recipe into
Agda code that can compute for us the reduction sequence of `plus · two · two`,
and its Church numeral variant.

(The development in this chapter was inspired by the corresponding
development in _Software Foundations_, Volume _Programming Language
Foundations_, Chapter _StlcProp_.  It will turn out that one of our technical choices
— to introduce an explicit judgment `Γ ∋ x ⦂ A` in place of
treating a context as a function from identifiers to types —
permits a simpler development. In particular, we can prove substitution preserves
types without needing to develop a separate inductive definition of the
`appears_free_in` relation.)


## Values do not reduce

We start with an easy observation. Values do not reduce:
```
V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ        ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N
```
We consider the three possibilities for values:

* If it is an abstraction then no reduction applies

* If it is zero then no reduction applies

* If it is a successor then rule `ξ-suc` may apply,
  but in that case the successor is itself of a value
  that reduces, which by induction cannot occur.

As a corollary, terms that reduce are not values:
```
—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N
```
If we expand out the negations, we have

    V¬—→ : ∀ {M N} → Value M → M —→ N → ⊥
    —→¬V : ∀ {M N} → M —→ N → Value M → ⊥

which are the same function with the arguments swapped.


## Canonical Forms

Well-typed values must take one of a small number of _canonical forms_,
which provide an analogue of the `Value` relation that relates values
to their types.  A lambda expression must have a function type,
and a zero or successor expression must be a natural.
Further, the body of a function must be well typed in a context
containing only its bound variable, and the argument of successor
must itself be canonical:
```
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
```

Every closed, well-typed value is canonical:
```
canonical : ∀ {V A}
  → ∅ ⊢ V ⦂ A
  → Value V
    -----------
  → Canonical V ⦂ A
canonical (⊢` ())          ()
canonical (⊢ƛ ⊢N)          V-ƛ         =  C-ƛ ⊢N
canonical (⊢L · ⊢M)        ()
canonical ⊢zero            V-zero      =  C-zero
canonical (⊢suc ⊢V)        (V-suc VV)  =  C-suc (canonical ⊢V VV)
canonical (⊢case ⊢L ⊢M ⊢N) ()
canonical (⊢μ ⊢M)          ()
```
There are only three interesting cases to consider:

* If the term is a lambda abstraction, then well-typing of the term
  guarantees well-typing of the body.

* If the term is zero then it is canonical trivially.

* If the term is a successor then since it is well typed its argument
  is well typed, and since it is a value its argument is a value.
  Hence, by induction its argument is also canonical.

The variable case is thrown out because a closed term has no free
variables and because a variable is not a value.  The cases for
application, case expression, and fixpoint are thrown out because they
are not values.

Conversely, if a term is canonical then it is a value
and it is well typed in the empty context:
```
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
```
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
free variable `s`.  The first of those terms is ill typed, and the
second has a free variable.  Every term that is well typed and closed
has the desired property.

_Progress_: If `∅ ⊢ M ⦂ A` then either `M` is a value or there is an `N` such
that `M —→ N`.

To formulate this property, we first introduce a relation that
captures what it means for a term `M` to make progress:
```
data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
```
A term `M` makes progress if either it can take a step, meaning there
exists a term `N` such that `M —→ N`, or if it is done, meaning that
`M` is a value.

If a term is well typed in the empty context then it satisfies progress:
```
progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done VL with progress ⊢M
...   | step M—→M′                          =  step (ξ-·₂ VL M—→M′)
...   | done VM with canonical ⊢L VL
...     | C-ƛ _                             =  step (β-ƛ VM)
progress ⊢zero                              =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M—→M′                           =  step (ξ-suc M—→M′)
...  | done VM                              =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            =  step (ξ-case L—→L′)
... | done VL with canonical ⊢L VL
...   | C-zero                              =  step β-zero
...   | C-suc CL                            =  step (β-suc (value CL))
progress (⊢μ ⊢M)                            =  step β-μ
```
We induct on the evidence that the term is well typed.
Let's unpack the first three cases:

* The term cannot be a variable, since no variable is well typed
  in the empty context.

* If the term is a lambda abstraction then it is a value.

* If the term is an application `L · M`, recursively apply
  progress to the derivation that `L` is well typed:

  + If the term steps, we have evidence that `L —→ L′`,
    which by `ξ-·₁` means that our original term steps
    to `L′ · M`

  + If the term is done, we have evidence that `L` is
    a value. Recursively apply progress to the derivation
    that `M` is well typed:

    - If the term steps, we have evidence that `M —→ M′`,
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
      a value, so our original term steps by `β-ƛ`.

The remaining cases are similar.  If by induction we have a
`step` case we apply a `ξ` rule, and if we have a `done` case
then either we have a value or apply a `β` rule.  For fixpoint,
no induction is required as the `β` rule applies immediately.

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
```
postulate
  progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
```
This leads to a less perspicuous proof.  Instead of the mnemonic `done`
and `step` we use `inj₁` and `inj₂`, and the term `N` is no longer
implicit and so must be written out in full.  In the case for `β-ƛ`
this requires that we match against the lambda expression `L` to
determine its bound variable and body, `ƛ x ⇒ N`, so we can show that
`L · M` reduces to `N [ x := M ]`.

#### Exercise `Progress-≃` (practice)

Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M —→ N)`.

```
-- Your code goes here
```

#### Exercise `progress′` (practice)

Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.

```
-- Your code goes here
```

#### Exercise `value?` (practice)

Combine `progress` and `—→¬V` to write a program that decides
whether a well-typed term is a value:
```
postulate
  value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
```

## Prelude to preservation

The other property we wish to prove, preservation of typing under
reduction, turns out to require considerably more work.  The proof has
three key steps.

The first step is to show that types are preserved by _renaming_.

_Renaming_:
Let `Γ` and `Δ` be two contexts such that every variable that
appears in `Γ` also appears with the same type in `Δ`.  Then
if any term is typeable under `Γ`, it has the same type under `Δ`.

In symbols:

    ∀ {x A} → Γ ∋ x ⦂ A  →  Δ ∋ x ⦂ A
    ---------------------------------
    ∀ {M A} → Γ ⊢ M ⦂ A  →  Δ ⊢ M ⦂ A

Three important corollaries follow.  The _weaken_ lemma asserts that a term
which is well typed in the empty context is also well typed in an arbitrary
context.  The _drop_ lemma asserts that a term which is well typed in a context
where the same variable appears twice remains well typed if we drop the shadowed
occurrence. The _swap_ lemma asserts that a term which is well typed in a
context remains well typed if we swap two variables. 

(Renaming is similar to the _context invariance_ lemma in _Software
Foundations_, but it does not require the definition of
`appears_free_in` nor the `free_in_context` lemma.)

The second step is to show that types are preserved by
_substitution_.

_Substitution_:
Say we have a closed term `V` of type `A`, and under the
assumption that `x` has type `A` the term `N` has type `B`.
Then substituting `V` for `x` in `N` yields a term that
also has type `B`.

In symbols:

    ∅ ⊢ V ⦂ A
    Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
    Γ ⊢ N [ x := V ] ⦂ B

The result does not depend on `V` being a value, but it does
require that `V` be closed; recall that we restricted our attention
to substitution by closed terms in order to avoid the need to
rename bound variables.  The term into which we are substituting
is typed in an arbitrary context `Γ`, extended by the variable
`x` for which we are substituting; and the result term is typed
in `Γ`.

The lemma establishes that substitution composes well with typing:
typing the components separately guarantees that the result of
combining them is also well typed.

The third step is to show preservation.

_Preservation_:
If `∅ ⊢ M ⦂ A` and `M —→ N` then `∅ ⊢ N ⦂ A`.

The proof is by induction over the possible reductions, and
the substitution lemma is crucial in showing that each of the
`β` rules that uses substitution preserves types.

We now proceed with our three-step programme.


## Renaming

We often need to "rebase" a type derivation, replacing a derivation
`Γ ⊢ M ⦂ A` by a related derivation `Δ ⊢ M ⦂ A`.  We may do so as long
as every variable that appears in `Γ` also appears in `Δ`, and with
the same type.

Three of the rules for typing (lambda abstraction, case on naturals,
and fixpoint) have hypotheses that extend the context to include a
bound variable. In each of these rules, `Γ` appears in the conclusion
and `Γ , x ⦂ A` appears in a hypothesis.  Thus:

    Γ , x ⦂ A ⊢ N ⦂ B
    ------------------- ⊢ƛ
    Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

for lambda expressions, and similarly for case and fixpoint.  To deal
with this situation, we first prove a lemma showing that if one context maps to another,
this is still true after adding the same variable to
both contexts:
```
ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)
```
Let `ρ` be the name of the map that takes evidence that
`x` appears in `Γ` to evidence that `x` appears in `Δ`.
The proof is by case analysis of the evidence that `x` appears
in the extended map `Γ , y ⦂ B`:

* If `x` is the same as `y`, we used `Z` to access the last variable
in the extended `Γ`; and can similarly use `Z` to access the last
variable in the extended `Δ`.

* If `x` differs from `y`, then we used `S` to skip over the last
variable in the extended `Γ`, where `x≢y` is evidence that `x` and `y`
differ, and `∋x` is the evidence that `x` appears in `Γ`; and we can
similarly use `S` to skip over the last variable in the extended `Δ`,
applying `ρ` to find the evidence that `x` appears in `Δ`.

With the extension lemma under our belts, it is straightforward to
prove renaming preserves types:
```
rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w)           =  ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N)           =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)         =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero             =  ⊢zero
rename ρ (⊢suc ⊢M)         =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)  =  ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)           =  ⊢μ (rename (ext ρ) ⊢M)
```
As before, let `ρ` be the name of the map that takes evidence that
`x` appears in `Γ` to evidence that `x` appears in `Δ`.  We induct
on the evidence that `M` is well typed in `Γ`.  Let's unpack the
first three cases:

* If the term is a variable, then applying `ρ` to the evidence
that the variable appears in `Γ` yields the corresponding evidence that
the variable appears in `Δ`.

* If the term is a lambda abstraction, use the previous lemma to
extend the map `ρ` suitably and use induction to rename the body of the
abstraction.

* If the term is an application, use induction to rename both the
function and the argument.

The remaining cases are similar, using induction for each subterm, and
extending the map whenever the construct introduces a bound variable.

The induction is over the derivation that the term is well typed,
so extending the context doesn't invalidate the inductive hypothesis.
Equivalently, the recursion terminates because the second argument
always grows smaller, even though the first argument sometimes grows larger.

We have three important corollaries, each proved by constructing
a suitable map between contexts.

First, a closed term can be weakened to any context:
```
weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()
```
Here the map `ρ` is trivial, since there are no possible
arguments in the empty context `∅`.

Second, if the last two variables in a context are equal then we can
drop the shadowed one:
```
drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                 =  Z
  ρ (S x≢x Z)         =  ⊥-elim (x≢x refl)
  ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z
```
Here map `ρ` can never be invoked on the inner occurrence of `x` since
it is masked by the outer occurrence.  Skipping over the `x` in the
first position can only happen if the variable looked for differs from
`x` (the evidence for which is `x≢x` or `z≢x`) but if the variable is
found in the second position, which also contains `x`, this leads to a
contradiction (evidenced by `x≢x refl`).

Third, if the last two variables in a context differ then we can swap them:
```
swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z                   =  S x≢y Z
  ρ (S z≢x Z)           =  Z
  ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)
```
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

Here is the formal statement and proof that substitution preserves types:
```
subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _           =  weaken ⊢V
... | no  x≢y         =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl        =  ⊥-elim (x≢y refl)
... | no  _           =  ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl        =  ⊢ƛ (drop ⊢N)
... | no  x≢y         =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M)    =  (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero        =  ⊢zero
subst ⊢V (⊢suc ⊢M)    =  ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl        =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no  x≢y         =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl        =  ⊢μ (drop ⊢M)
... | no  x≢y         =  ⊢μ (subst ⊢V (swap x≢y ⊢M))
```
We induct on the evidence that `N` is well typed in the
context `Γ` extended by `x`.

First, we note a wee issue with naming.  In the lemma
statement, the variable `x` is an implicit parameter for the variable
substituted, while in the type rules for variables, abstractions,
cases, and fixpoints, the variable `x` is an implicit parameter for
the relevant variable.  We are going to need to get hold of both
variables, so we use the syntax `{x = y}` to bind `y` to the
substituted variable and the syntax `{x = x}` to bind `x` to the
relevant variable in the patterns for `` ⊢` ``, `⊢ƛ`, `⊢case`, and `⊢μ`.
Using the name `y` here is consistent with the naming in the original
definition of substitution in the previous chapter.  The proof never
mentions the types of `x`, `y`, `V`, or `N`, so in what follows we
choose type names as convenient.

Now that naming is resolved, let's unpack the first three cases:

* In the variable case, we must show

      ∅ ⊢ V ⦂ B
      Γ , y ⦂ B ⊢ ` x ⦂ A
      ------------------------
      Γ ⊢ ` x [ y := V ] ⦂ A

  where the second hypothesis follows from:

      Γ , y ⦂ B ∋ x ⦂ A

  There are two subcases, depending on the evidence for this judgment:

  + The lookup judgment is evidenced by rule `Z`:

        ----------------
        Γ , x ⦂ A ∋ x ⦂ A

    In this case, `x` and `y` are necessarily identical, as are `A`
    and `B`.  Nonetheless, we must evaluate `x ≟ y` in order to allow
    the definition of substitution to simplify:

    - If the variables are equal, then after simplification we
      must show

          ∅ ⊢ V ⦂ A
          ---------
          Γ ⊢ V ⦂ A

      which follows by weakening.

    - If the variables are unequal we have a contradiction.

  + The lookup judgment is evidenced by rule `S`:

        x ≢ y
        Γ ∋ x ⦂ A
        -----------------
        Γ , y ⦂ B ∋ x ⦂ A

    In this case, `x` and `y` are necessarily distinct.
    Nonetheless, we must again evaluate `x ≟ y` in order to allow
    the definition of substitution to simplify:

    - If the variables are equal we have a contradiction.

    - If the variables are unequal, then after simplification we
      must show

          ∅ ⊢ V ⦂ B
          x ≢ y
          Γ ∋ x ⦂ A
          -------------
          Γ ⊢ ` x ⦂ A

      which follows by the typing rule for variables.

* In the abstraction case, we must show

      ∅ ⊢ V ⦂ B
      Γ , y ⦂ B ⊢ (ƛ x ⇒ N) ⦂ A ⇒ C
      --------------------------------
      Γ ⊢ (ƛ x ⇒ N) [ y := V ] ⦂ A ⇒ C

  where the second hypothesis follows from

      Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C

  We evaluate `x ≟ y` in order to allow the definition of substitution to simplify:

  + If the variables are equal then after simplification we must show:

        ∅ ⊢ V ⦂ B
        Γ , x ⦂ B , x ⦂ A ⊢ N ⦂ C
        -------------------------
        Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ C

    From the drop lemma, `drop`, we may conclude:

        Γ , x ⦂ B , x ⦂ A ⊢ N ⦂ C
        -------------------------
        Γ , x ⦂ A ⊢ N ⦂ C

    The typing rule for abstractions then yields the required conclusion.

  + If the variables are distinct then after simplification we must show:

        ∅ ⊢ V ⦂ B
        Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C
        --------------------------------
        Γ ⊢ ƛ x ⇒ (N [ y := V ]) ⦂ A ⇒ C

    From the swap lemma we may conclude:

        Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C
        -------------------------
        Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C

    The inductive hypothesis gives us:

        ∅ ⊢ V ⦂ B
        Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C
        ----------------------------
        Γ , x ⦂ A ⊢ N [ y := V ] ⦂ C

    The typing rule for abstractions then yields the required conclusion.

* In the application case, we must show

      ∅ ⊢ V ⦂ C
      Γ , y ⦂ C ⊢ L · M ⦂ B
      --------------------------
      Γ ⊢ (L · M) [ y := V ] ⦂ B

  where the second hypothesis follows from the two judgments

      Γ , y ⦂ C ⊢ L ⦂ A ⇒ B
      Γ , y ⦂ C ⊢ M ⦂ A

  By the definition of substitution, we must show:

      ∅ ⊢ V ⦂ C
      Γ , y ⦂ C ⊢ L ⦂ A ⇒ B
      Γ , y ⦂ C ⊢ M ⦂ A
      ---------------------------------------
      Γ ⊢ (L [ y := V ]) · (M [ y := V ]) ⦂ B

  Applying the induction hypothesis for `L` and `M` and the typing
  rule for applications yields the required conclusion.

The remaining cases are similar, using induction for each subterm.
Where the construct introduces a bound variable we need to compare it
with the substituted variable, applying the drop lemma if they are
equal and the swap lemma if they are distinct.

For Agda it makes a difference whether we write `x ≟ y` or 
`y ≟ x`. In an interactive proof, Agda will show which residual `with`
clauses in the definition of `_[_:=_]` need to be simplified, and the
`with` clauses in `subst` need to match these exactly. The guideline is
that Agda knows nothing about symmetry or commutativity, which require
invoking appropriate lemmas, so it is important to think about order of
arguments and to be consistent.

#### Exercise `subst′` (stretch)

Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.

```
-- Your code goes here
```


## Preservation

Once we have shown that substitution preserves types, showing
that reduction preserves types is straightforward:

```
preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢` ())
preserve (⊢ƛ ⊢N)                 ()
preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)     =  (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′)  =  ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)         =  subst ⊢V ⊢N
preserve ⊢zero                   ()
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     (β-zero)         =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)       =  subst ⊢V ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M
```
The proof never mentions the types of `M` or `N`,
so in what follows we choose type name as convenient.

Let's unpack the cases for two of the reduction rules:

* Rule `ξ-·₁`.  We have

      L —→ L′
      ----------------
      L · M —→ L′ · M

  where the left-hand side is typed by

      Γ ⊢ L ⦂ A ⇒ B
      Γ ⊢ M ⦂ A
      -------------
      Γ ⊢ L · M ⦂ B

  By induction, we have

      Γ ⊢ L ⦂ A ⇒ B
      L —→ L′
      --------------
      Γ ⊢ L′ ⦂ A ⇒ B

  from which the typing of the right-hand side follows immediately.

* Rule `β-ƛ`.  We have

      Value V
      -----------------------------
      (ƛ x ⇒ N) · V —→ N [ x := V ]

  where the left-hand side is typed by

      Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
      Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B    Γ ⊢ V ⦂ A
      --------------------------------
      Γ ⊢ (ƛ x ⇒ N) · V ⦂ B

  By the substitution lemma, we have

      Γ ⊢ V ⦂ A
      Γ , x ⦂ A ⊢ N ⦂ B
      --------------------
      Γ ⊢ N [ x := V ] ⦂ B

  from which the typing of the right-hand side follows immediately.

The remaining cases are similar.  Each `ξ` rule follows by induction,
and each `β` rule follows by the substitution lemma.


## Evaluation

By repeated application of progress and preservation, we can evaluate
any well-typed term.  In this section, we will present an Agda
function that computes the reduction sequence from any given closed,
well-typed term to its value, if it has one.

Some terms may reduce forever.  Here is a simple example:
```
sucμ  =  μ "x" ⇒ `suc (` "x")

_ =
  begin
    sucμ
  —→⟨ β-μ ⟩
    `suc sucμ
  —→⟨ ξ-suc β-μ ⟩
    `suc `suc sucμ
  —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc `suc `suc sucμ
  --  ...
  ∎
```
Since every Agda computation must terminate,
we cannot simply ask Agda to reduce a term to a value.
Instead, we will provide a natural number to Agda, and permit it
to stop short of a value if the term requires more than the given
number of reduction steps.

A similar issue arises with cryptocurrencies.  Systems which use
smart contracts require the miners that maintain the blockchain to
evaluate the program which embodies the contract.  For instance,
validating a transaction on Ethereum may require executing a program
for the Ethereum Virtual Machine (EVM).  A long-running or
non-terminating program might cause the miner to invest arbitrary
effort in validating a contract for little or no return.  To avoid
this situation, each transaction is accompanied by an amount of _gas_
available for computation.  Each step executed on the EVM is charged
an advertised amount of gas, and the transaction pays for the gas at a
published rate: a given number of Ethers (the currency of Ethereum)
per unit of gas.

By analogy, we will use the name _gas_ for the parameter which puts a
bound on the number of reduction steps.  `Gas` is specified by a natural number:
```
data Gas : Set where
  gas : ℕ → Gas
```
When our evaluator returns a term `N`, it will either give evidence that
`N` is a value or indicate that it ran out of gas:
```
data Finished (N : Term) : Set where

  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N
```
Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished:
```
data Steps (L : Term) : Set where

  steps : ∀ {N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
```
The evaluator takes gas and evidence that a term is well typed,
and returns the corresponding steps:
```
{-# TERMINATING #-}
eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ⦂ A
    ---------
  → Steps L
eval {L} (gas zero)    ⊢L                             =  steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL                                         =  steps (L ∎) (done VL)
... | step L—→M with eval (gas m) (preserve ⊢L L—→M)
...    | steps M—↠N fin                               =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```
Let `L` be the name of the term we are reducing, and `⊢L` be the
evidence that `L` is well typed.  We consider the amount of gas
remaining.  There are two possibilities:

* It is zero, so we stop early.  We return the trivial reduction
  sequence `L —↠ L`, evidence that `L` is well typed, and an
  indication that we are out of gas.

* It is non-zero and after the next step we have `m` gas remaining.
  Apply progress to the evidence that term `L` is well typed.  There
  are two possibilities:

  + Term `L` is a value, so we are done. We return the
    trivial reduction sequence `L —↠ L`, evidence that `L` is
    well typed, and the evidence that `L` is a value.

  + Term `L` steps to another term `M`.  Preservation provides
    evidence that `M` is also well typed, and we recursively invoke
    `eval` on the remaining gas.  The result is evidence that
    `M —↠ N`, together with evidence that `N` is well typed and an
    indication of whether reduction finished.  We combine the evidence
    that `L —→ M` and `M —↠ N` to return evidence that `L —↠ N`,
    together with the other relevant evidence.


### Examples

We can now use Agda to compute the non-terminating reduction
sequence given earlier.  First, we show that the term `sucμ`
is well typed:
```
⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where
  ∋x = Z
```
To show the first three steps of the infinite reduction
sequence, we evaluate with three steps worth of gas:
```
_ : eval (gas 3) ⊢sucμ ≡
  steps
   (μ "x" ⇒ `suc ` "x"
   —→⟨ β-μ ⟩
    `suc (μ "x" ⇒ `suc ` "x")
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ "x" ⇒ `suc ` "x"))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ "x" ⇒ `suc ` "x")))
   ∎)
   out-of-gas
_ = refl
```

Similarly, we can use Agda to compute the reduction sequences given
in the previous chapter.  We start with the Church numeral two
applied to successor and zero.  Supplying 100 steps of gas is more than enough:
```
_ : eval (gas 100) (⊢twoᶜ · ⊢sucᶜ · ⊢zero) ≡
  steps
   ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
   · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
     `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "n" ⇒ `suc ` "n") · `suc `zero
   —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
   ∎)
   (done (V-suc (V-suc V-zero)))
_ = refl
```
The example above was generated by using `C-c C-n` to normalise the
left-hand side of the equation and pasting in the result as the
right-hand side of the equation.  The example reduction of the
previous chapter was derived from this result, reformatting and
writing `twoᶜ` and `sucᶜ` in place of their expansions.

Next, we show two plus two is four:
```
_ : eval (gas 100) ⊢2+2 ≡
  steps
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · `suc (`suc `zero)
    · `suc (`suc `zero)
   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "m"
       · ` "n")
      ]))
    · `suc (`suc `zero)
    · `suc (`suc `zero)
   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · ` "n")
     ])
    · `suc (`suc `zero)
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "m"
     · `suc (`suc `zero))
    ]
   —→⟨ β-suc (V-suc V-zero) ⟩
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · `suc `zero
     · `suc (`suc `zero))
   —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc
    ((ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     · `suc `zero
     · `suc (`suc `zero))
   —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc
    ((ƛ "n" ⇒
      case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "m"
       · ` "n")
      ])
     · `suc (`suc `zero))
   —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc
    case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "m"
     · `suc (`suc `zero))
    ]
   —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc
    (`suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · `zero
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc
    (`suc
     ((ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
        `suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ]))
      · `zero
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc
    (`suc
     ((ƛ "n" ⇒
       case `zero [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ])
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc
    (`suc
     case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · `suc (`suc `zero))
     ])
   —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
   ∎)
   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
```
Again, the derivation in the previous chapter was derived by
editing the above.

Similarly, we can evaluate the corresponding term for Church numerals:
```
_ : eval (gas 100) ⊢2+2ᶜ ≡
  steps
   ((ƛ "m" ⇒
     (ƛ "n" ⇒
      (ƛ "s" ⇒ (ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z")))))
    · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
    · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
    · (ƛ "n" ⇒ `suc ` "n")
    · `zero
   —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒
     (ƛ "s" ⇒
      (ƛ "z" ⇒
       (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" ·
       (` "n" · ` "s" · ` "z"))))
    · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
    · (ƛ "n" ⇒ `suc ` "n")
    · `zero
   —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒
     (ƛ "z" ⇒
      (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" ·
      ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" · ` "z")))
    · (ƛ "n" ⇒ `suc ` "n")
    · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒
     (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
     ·
     ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
      · ` "z"))
    · `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
    ·
    ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
     · `zero)
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
     · `zero)
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
     `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `zero))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "n" ⇒ `suc ` "n") · `suc `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    `suc (`suc `zero)
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `suc (`suc `zero))
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒ `suc ` "n") · `suc (`suc (`suc `zero))
   —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc (`suc (`suc (`suc `zero)))
   ∎)
   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
```
And again, the example in the previous section was derived by editing the
above.

#### Exercise `mul-eval` (recommended)

Using the evaluator, confirm that two times two is four.

```
-- Your code goes here
```


#### Exercise: `progress-preservation` (practice)

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.

```
-- Your code goes here
```


#### Exercise `subject_expansion` (practice)

We say that `M` _reduces_ to `N` if `M —→ N`,
but we can also describe the same situation by saying
that `N` _expands_ to `M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M —→ N` and `∅ ⊢ N ⦂ A` imply `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.

```
-- Your code goes here
```


## Well-typed terms don't get stuck

A term is _normal_ if it cannot reduce:
```
Normal : Term → Set
Normal M  =  ∀ {N} → ¬ (M —→ N)
```

A term is _stuck_ if it is normal yet not a value:
```
Stuck : Term → Set
Stuck M  =  Normal M × ¬ Value M
```

Using progress, it is easy to show that no well-typed term is stuck:
```
postulate
  unstuck : ∀ {M A}
    → ∅ ⊢ M ⦂ A
      -----------
    → ¬ (Stuck M)
```

Using preservation, it is easy to show that after any number of steps,
a well-typed term remains well typed:
```
postulate
  preserves : ∀ {M N A}
    → ∅ ⊢ M ⦂ A
    → M —↠ N
      ---------
    → ∅ ⊢ N ⦂ A
```

An easy consequence is that starting from a well-typed term, taking
any number of reduction steps leads to a term that is not stuck:
```
postulate
  wttdgs : ∀ {M N A}
    → ∅ ⊢ M ⦂ A
    → M —↠ N
      -----------
    → ¬ (Stuck N)
```
Felleisen and Wright, who introduced proofs via progress and
preservation, summarised this result with the slogan _well-typed terms
don't get stuck_.  (They were referring to earlier work by Robin
Milner, who used denotational rather than operational semantics. He
introduced `wrong` as the denotation of a term with a type error, and
showed _well-typed terms don't go wrong_.)

#### Exercise `stuck` (practice)

Give an example of an ill-typed term that does get stuck.

```
-- Your code goes here
```

#### Exercise `unstuck` (recommended)

Provide proofs of the three postulates, `unstuck`, `preserves`, and `wttdgs` above.

```
-- Your code goes here
```

## Reduction is deterministic

When we introduced reduction, we claimed it was deterministic.
For completeness, we present a formal proof here.

Our proof will need a variant
of congruence to deal with functions of four arguments
(to deal with `case_[zero⇒_|suc_⇒_]`).  It
is exactly analogous to `cong` and `cong₂` as defined previously:
```
cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl
```

It is now straightforward to show that reduction is deterministic:
```
det : ∀ {M M′ M″}
  → (M —→ M′)
  → (M —→ M″)
    --------
  → M′ ≡ M″
det (ξ-·₁ L—→L′)   (ξ-·₁ L—→L″)     =  cong₂ _·_ (det L—→L′ L—→L″) refl
det (ξ-·₁ L—→L′)   (ξ-·₂ VL M—→M″)  =  ⊥-elim (V¬—→ VL L—→L′)
det (ξ-·₁ L—→L′)   (β-ƛ _)          =  ⊥-elim (V¬—→ V-ƛ L—→L′)
det (ξ-·₂ VL _)    (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ VL L—→L″)
det (ξ-·₂ _ M—→M′) (ξ-·₂ _ M—→M″)   =  cong₂ _·_ refl (det M—→M′ M—→M″)
det (ξ-·₂ _ M—→M′) (β-ƛ VM)         =  ⊥-elim (V¬—→ VM M—→M′)
det (β-ƛ _)        (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ V-ƛ L—→L″)
det (β-ƛ VM)       (ξ-·₂ _ M—→M″)   =  ⊥-elim (V¬—→ VM M—→M″)
det (β-ƛ _)        (β-ƛ _)          =  refl
det (ξ-suc M—→M′)  (ξ-suc M—→M″)    =  cong `suc_ (det M—→M′ M—→M″)
det (ξ-case L—→L′) (ξ-case L—→L″)   =  cong₄ case_[zero⇒_|suc_⇒_]
                                         (det L—→L′ L—→L″) refl refl refl
det (ξ-case L—→L′) β-zero           =  ⊥-elim (V¬—→ V-zero L—→L′)
det (ξ-case L—→L′) (β-suc VL)       =  ⊥-elim (V¬—→ (V-suc VL) L—→L′)
det β-zero         (ξ-case M—→M″)   =  ⊥-elim (V¬—→ V-zero M—→M″)
det β-zero         β-zero           =  refl
det (β-suc VL)     (ξ-case L—→L″)   =  ⊥-elim (V¬—→ (V-suc VL) L—→L″)
det (β-suc _)      (β-suc _)        =  refl
det β-μ            β-μ              =  refl
```
The proof is by induction over possible reductions.  We consider
three typical cases:

* Two instances of `ξ-·₁`:

      L —→ L′                 L —→ L″
      --------------- ξ-·₁    --------------- ξ-·₁
      L · M —→ L′ · M         L · M —→ L″ · M

  By induction we have `L′ ≡ L″`, and hence by congruence
  `L′ · M ≡ L″ · M`.

* An instance of `ξ-·₁` and an instance of `ξ-·₂`:

                              Value L
      L —→ L′                 M —→ M″
      --------------- ξ-·₁    --------------- ξ-·₂
      L · M —→ L′ · M         L · M —→ L · M″

  The rule on the left requires `L` to reduce, but the rule on the right
  requires `L` to be a value.  This is a contradiction since values do
  not reduce.  If the value constraint was removed from `ξ-·₂`, or from
  one of the other reduction rules, then determinism would no longer hold.

* Two instances of `β-ƛ`:

      Value V                              Value V
      ----------------------------- β-ƛ    ----------------------------- β-ƛ
      (ƛ x ⇒ N) · V —→ N [ x := V ]        (ƛ x ⇒ N) · V —→ N [ x := V ]

  Since the left-hand sides are identical, the right-hand sides are
  also identical. The formal proof simply invokes `refl`.

Five of the 18 lines in the above proof are redundant, e.g., the case
when one rule is `ξ-·₁` and the other is `ξ-·₂` is considered twice,
once with `ξ-·₁` first and `ξ-·₂` second, and the other time with the
two swapped.  What we might like to do is delete the redundant lines
and add

    det M—→M′ M—→M″ = sym (det M—→M″ M—→M′)

to the bottom of the proof. But this does not work: the termination
checker complains, because the arguments have merely switched order
and neither is smaller.


#### Quiz

Suppose we add a new term `zap` with the following reduction rule

    -------- β-zap
    M —→ zap

and the following typing rule:

    ----------- ⊢zap
    Γ ⊢ zap ⦂ A

Which of the following properties remain true in
the presence of these rules?  For each property, write either
"remains true" or "becomes false." If a property becomes
false, give a counterexample:

  - Determinism of `step`

  - Progress

  - Preservation


#### Quiz

Suppose instead that we add a new term `foo` with the following
reduction rules:

    ------------------ β-foo₁
    (λ x ⇒ ` x) —→ foo

    ----------- β-foo₂
    foo —→ zero

Which of the following properties remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample:

  - Determinism of `step`

  - Progress

  - Preservation


#### Quiz

Suppose instead that we remove the rule `ξ·₁` from the step
relation. Which of the following properties remain
true in the absence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample:

  - Determinism of `step`

  - Progress

  - Preservation


#### Quiz

We can enumerate all the computable function from naturals to
naturals, by writing out all programs of type `` `ℕ ⇒ `ℕ`` in
lexical order.  Write `fᵢ` for the `i`'th function in this list.

Say we add a typing rule that applies the above enumeration
to interpret a natural as a function from naturals to naturals:

    Γ ⊢ L ⦂ `ℕ
    Γ ⊢ M ⦂ `ℕ
    -------------- _·ℕ_
    Γ ⊢ L · M ⦂ `ℕ

And that we add the corresponding reduction rule:

    fᵢ(m) —→ n
    ---------- δ
    i · m —→ n

Which of the following properties remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample:

  - Determinism of `step`

  - Progress

  - Preservation

Are all properties preserved in this case? Are there any
other alterations we would wish to make to the system?

## Unicode

This chapter uses the following unicode:

    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    Δ  U+0394  GREEK CAPITAL LETTER DELTA (\GD or \Delta)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    δ  U+03B4  GREEK SMALL LETTER DELTA (\Gd or \delta)
    μ  U+03BC  GREEK SMALL LETTER MU (\Gm or \mu)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    ρ  U+03B4  GREEK SMALL LETTER RHO (\Gr or \rho)
    ᵢ  U+1D62  LATIN SUBSCRIPT SMALL LETTER I (\_i)
    ᶜ  U+1D9C  MODIFIER LETTER SMALL C (\^c)
    –  U+2013  EM DASH (\em)
    ₄  U+2084  SUBSCRIPT FOUR (\_4)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ∅  U+2205  EMPTY SET (\0)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ≟  U+225F  QUESTIONED EQUAL TO (\?=)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
