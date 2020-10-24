---
title     : "Untyped: Untyped lambda calculus with full normalisation"
layout    : page
prev      : /Inference/
permalink : /Untyped/
next      : /Confluence/
---

```
module plfa.part2.Untyped where
```

In this chapter we play with variations on a theme:

* Previous chapters consider intrinsically-typed calculi;
  here we consider one that is untyped but intrinsically scoped.

* Previous chapters consider call-by-value calculi;
  here we consider call-by-name.

* Previous chapters consider _weak head normal form_,
  where reduction stops at a lambda abstraction;
  here we consider _full normalisation_,
  where reduction continues underneath a lambda.

* Previous chapters consider _deterministic_ reduction,
  where there is at most one redex in a given term;
  here we consider _non-deterministic_ reduction
  where a term may contain many redexes and any one of them may reduce.

* Previous chapters consider reduction of _closed_ terms,
  those with no free variables;
  here we consider _open_ terms,
  those which may have free variables.

* Previous chapters consider lambda calculus extended
  with natural numbers and fixpoints;
  here we consider a tiny calculus with just variables,
  abstraction, and application, in which the other
  constructs may be encoded.

In general, one may mix and match these features,
save that full normalisation requires open terms and
encoding naturals and fixpoints requires being untyped.
The aim of this chapter is to give some appreciation for
the range of different lambda calculi one may encounter.


## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)
```


## Untyped is Uni-typed

Our development will be close to that in
Chapter [DeBruijn](/DeBruijn/),
save that every term will have exactly the same type, written `★`
and pronounced "any".
This matches a slogan introduced by Dana Scott
and echoed by Robert Harper: "Untyped is Uni-typed".
One consequence of this approach is that constructs which previously
had to be given separately (such as natural numbers and fixpoints)
can now be defined in the language itself.


## Syntax

First, we get all our infix declarations out of the way:

```
infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infix  6  ′_
infixl 7  _·_
```

## Types

We have just one type:
```
data Type : Set where
  ★ : Type
```

#### Exercise (`Type≃⊤`) (practice)

Show that `Type` is isomorphic to `⊤`, the unit type.

```
-- Your code goes here
```

## Contexts

As before, a context is a list of types, with the type of the
most recently bound variable on the right:
```
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```
We let `Γ` and `Δ` range over contexts.

#### Exercise (`Context≃ℕ`) (practice)

Show that `Context` is isomorphic to `ℕ`.

```
-- Your code goes here
```

## Variables and the lookup judgment

Intrinsically-scoped variables correspond to the lookup judgment.  The
rules are as before:
```
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
     ---------
   → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
```
We could write the rules with all instances of `A` and `B`
replaced by `★`, but arguably it is clearer not to do so.

Because `★` is the only type, the judgment doesn't guarantee anything
useful about types.  But it does ensure that all variables are in
scope.  For instance, we cannot use `S S Z` in a context that only
binds two variables.


## Terms and the scoping judgment

Intrinsically-scoped terms correspond to the typing judgment, but with
`★` as the only type.  The result is that we check that terms are
well scoped — that is, that all variables they mention are in scope —
but not that they are well typed:
```
data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  :  ∀ {Γ}
    → Γ , ★ ⊢ ★
      ---------
    → Γ ⊢ ★

  _·_ : ∀ {Γ}
    → Γ ⊢ ★
    → Γ ⊢ ★
      ------
    → Γ ⊢ ★
```
Now we have a tiny calculus, with only variables, abstraction, and
application.  Below we will see how to encode naturals and
fixpoints into this calculus.

## Writing variables as numerals

As before, we can convert a natural to the corresponding de Bruijn
index.  We no longer need to lookup the type in the context, since
every variable has the same type:
```
count : ∀ {Γ} → ℕ → Γ ∋ ★
count {Γ , ★} zero     =  Z
count {Γ , ★} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥
```

We can then introduce a convenient abbreviation for variables:
```
#_ : ∀ {Γ} → ℕ → Γ ⊢ ★
# n  =  ` count n
```

## Test examples

Our only example is computing two plus two on Church numerals:
```
twoᶜ : ∀ {Γ} → Γ ⊢ ★
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

fourᶜ : ∀ {Γ} → Γ ⊢ ★
fourᶜ = ƛ ƛ (# 1 · (# 1 · (# 1 · (# 1 · # 0))))

plusᶜ : ∀ {Γ} → Γ ⊢ ★
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

2+2ᶜ : ∅ ⊢ ★
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ
```
Before, reduction stopped when we reached a lambda term, so we had to
compute `` plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero `` to ensure we reduced
to a representation of the natural four.  Now, reduction continues
under lambda, so we don't need the extra arguments.  It is convenient
to define a term to represent four as a Church numeral, as well as
two.

## Renaming

Our definition of renaming is as before.  First, we need an extension lemma:
```
ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```
We could replace all instances of `A` and `B` by `★`, but arguably it is
clearer not to do so.

Now it is straightforward to define renaming:
```
rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
```
This is exactly as before, save that there are fewer term forms.

## Simultaneous substitution

Our definition of substitution is also exactly as before.
First we need an extension lemma:
```
exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)
```
Again, we could replace all instances of `A` and `B` by `★`.

Now it is straightforward to define substitution:
```
subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
```
Again, this is exactly as before, save that there are fewer term forms.

## Single substitution

It is easy to define the special case of substitution for one free variable:
```
subst-zero : ∀ {Γ B} → (Γ ⊢ B) → ∀ {A} → (Γ , B ∋ A) → (Γ ⊢ A)
subst-zero M Z      =  M
subst-zero M (S x)  =  ` x

_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} (subst-zero M) {A} N
```

## Neutral and normal terms

Reduction continues until a term is fully normalised.  Hence, instead
of values, we are now interested in _normal forms_.  Terms in normal
form are defined by mutual recursion with _neutral_ terms:
```
data Neutral : ∀ {Γ A} → Γ ⊢ A → Set
data Normal  : ∀ {Γ A} → Γ ⊢ A → Set
```
Neutral terms arise because we now consider reduction of open terms,
which may contain free variables.  A term is neutral if it is a
variable or a neutral term applied to a normal term:
```
data Neutral where

  `_  : ∀ {Γ A} (x : Γ ∋ A)
      -------------
    → Neutral (` x)

  _·_  : ∀ {Γ} {L M : Γ ⊢ ★}
    → Neutral L
    → Normal M
      ---------------
    → Neutral (L · M)
```
A term is a normal form if it is neutral or an abstraction where the
body is a normal form. We use `′_` to label neutral terms.
Like `` `_ ``, it is unobtrusive:
```
data Normal where

  ′_ : ∀ {Γ A} {M : Γ ⊢ A}
    → Neutral M
      ---------
    → Normal M

  ƛ_  : ∀ {Γ} {N : Γ , ★ ⊢ ★}
    → Normal N
      ------------
    → Normal (ƛ N)
```

We introduce a convenient abbreviation for evidence that a variable is neutral:
```
#′_ : ∀ {Γ} (n : ℕ) → Neutral {Γ} (# n)
#′ n  =  ` count n
```

For example, here is the evidence that the Church numeral two is in
normal form:
```
_ : Normal (twoᶜ {∅})
_ = ƛ ƛ (′ #′ 1 · (′ #′ 1 · (′ #′ 0)))
```
The evidence that a term is in normal form is almost identical to
the term itself, decorated with some additional primes to indicate
neutral terms, and using `#′` in place of `#`


## Reduction step

The reduction rules are altered to switch from call-by-value to
call-by-name and to enable full normalisation:

* The rule `ξ₁` remains the same as it was for the simply-typed
  lambda calculus.

* In rule `ξ₂`, the requirement that the term `L` is a value
  is dropped. So this rule can overlap with `ξ₁` and
  reduction is _non-deterministic_. One can choose to reduce
  a term inside either `L` or `M`.

* In rule `β`, the requirement that the argument is a value
  is dropped, corresponding to call-by-name evaluation.
  This introduces further non-determinism, as `β` overlaps
  with `ξ₂` when there are redexes in the argument.

* A new rule `ζ` is added, to enable reduction underneath a lambda.

Here are the formalised rules:
```
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ₁ : ∀ {Γ} {L L′ M : Γ ⊢ ★}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂ : ∀ {Γ} {L M M′ : Γ ⊢ ★}
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β : ∀ {Γ} {N : Γ , ★ ⊢ ★} {M : Γ ⊢ ★}
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  ζ : ∀ {Γ} {N N′ : Γ , ★ ⊢ ★}
    → N —→ N′
      -----------
    → ƛ N —→ ƛ N′
```

#### Exercise (`variant-1`) (practice)

How would the rules change if we want call-by-value where terms
normalise completely?  Assume that `β` should not permit reduction
unless both terms are in normal form.

```
-- Your code goes here
```

#### Exercise (`variant-2`) (practice)

How would the rules change if we want call-by-value where terms
do not reduce underneath lambda?  Assume that `β`
permits reduction when both terms are values (that is, lambda
abstractions).  What would `2+2ᶜ` reduce to in this case?

```
-- Your code goes here
```


## Reflexive and transitive closure

We cut-and-paste the previous definition:
```
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```


## Example reduction sequence

Here is the demonstration that two plus two is four:
```
_ : 2+2ᶜ —↠ fourᶜ
_ =
  begin
    plusᶜ · twoᶜ · twoᶜ
  —→⟨ ξ₁ β ⟩
    (ƛ ƛ ƛ twoᶜ · # 1 · (# 2 · # 1 · # 0)) · twoᶜ
  —→⟨ β ⟩
    ƛ ƛ twoᶜ · # 1 · (twoᶜ · # 1 · # 0)
  —→⟨ ζ (ζ (ξ₁ β)) ⟩
    ƛ ƛ ((ƛ # 2 · (# 2 · # 0)) · (twoᶜ · # 1 · # 0))
  —→⟨ ζ (ζ β) ⟩
    ƛ ƛ # 1 · (# 1 · (twoᶜ · # 1 · # 0))
  —→⟨ ζ (ζ (ξ₂ (ξ₂ (ξ₁ β)))) ⟩
    ƛ ƛ # 1 · (# 1 · ((ƛ # 2 · (# 2 · # 0)) · # 0))
  —→⟨ ζ (ζ (ξ₂ (ξ₂ β))) ⟩
   ƛ (ƛ # 1 · (# 1 · (# 1 · (# 1 · # 0))))
  ∎
```
After just two steps the top-level term is an abstraction,
and `ζ` rules drive the rest of the normalisation.


## Progress

Progress adapts.  Instead of claiming that every term either is a value
or takes a reduction step, we claim that every term is either in normal
form or takes a reduction step.

Previously, progress only applied to closed, well-typed terms.  We had
to rule out terms where we apply something other than a function (such
as `` `zero ``) or terms with a free variable.  Now we can demonstrate
it for open, well-scoped terms.  The definition of normal form permits
free variables, and we have no terms that are not functions.

A term makes progress if it can take a step or is in normal form:
```
data Progress {Γ A} (M : Γ ⊢ A) : Set where

  step : ∀ {N : Γ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Normal M
      ----------
    → Progress M
```

If a term is well scoped then it satisfies progress:
```
progress : ∀ {Γ A} → (M : Γ ⊢ A) → Progress M
progress (` x)                                 =  done (′ ` x)
progress (ƛ N)  with  progress N
... | step N—→N′                               =  step (ζ N—→N′)
... | done NrmN                                =  done (ƛ NrmN)
progress (` x · M) with progress M
... | step M—→M′                               =  step (ξ₂ M—→M′)
... | done NrmM                                =  done (′ (` x) · NrmM)
progress ((ƛ N) · M)                           =  step β
progress (L@(_ · _) · M) with progress L
... | step L—→L′                               =  step (ξ₁ L—→L′)
... | done (′ NeuL) with progress M
...    | step M—→M′                            =  step (ξ₂ M—→M′)
...    | done NrmM                             =  done (′ NeuL · NrmM)
```
We induct on the evidence that the term is well scoped:

* If the term is a variable, then it is in normal form.
  (This contrasts with previous proofs, where the variable case was
  ruled out by the restriction to closed terms.)
* If the term is an abstraction, recursively invoke progress on the body.
  (This contrast with previous proofs, where an abstraction is
  immediately a value.):
  + If it steps, then the whole term steps via `ζ`.
  + If it is in normal form, then so is the whole term.
* If the term is an application, consider the function subterm:
  + If it is a variable, recursively invoke progress on the argument:
    - If it steps, then the whole term steps via `ξ₂`;
    - If it is normal, then so is the whole term.
  + If it is an abstraction, then the whole term steps via `β`.
  + If it is an application, recursively apply progress to the function subterm:
    - If it steps, then the whole term steps via `ξ₁`.
    - If it is normal, recursively apply progress to the argument subterm:
      * If it steps, then the whole term steps via `ξ₂`.
      * If it is normal, then so is the whole term.

The final equation for progress uses an _at pattern_ of the form `P@Q`,
which matches only if both pattern `P` and pattern `Q` match.  Character
`@` is one of the few that Agda doesn't allow in names, so spaces are not
required around it.  In this case, the pattern ensures that `L` is an
application.

## Evaluation

As previously, progress immediately yields an evaluator.

Gas is specified by a natural number:
```
record Gas : Set where
  constructor gas
  field
    amount : ℕ
```
When our evaluator returns a term `N`, it will either give evidence that
`N` is normal or indicate that it ran out of gas:
```
data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Normal N
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
data Steps : ∀ {Γ A} → Γ ⊢ A → Set where

  steps : ∀ {Γ A} {L N : Γ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
```
The evaluator takes gas and a term and returns the corresponding steps:
```
eval : ∀ {Γ A}
  → Gas
  → (L : Γ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done NrmL                          =  steps (L ∎) (done NrmL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```
The definition is as before, save that the empty context `∅`
generalises to an arbitrary context `Γ`.

## Example

We reiterate our previous example. Two plus two is four, with Church numerals:
```
_ : eval (gas 100) 2+2ᶜ ≡
  steps
   ((ƛ
     (ƛ
      (ƛ
       (ƛ
        (` (S (S (S Z)))) · (` (S Z)) ·
        ((` (S (S Z))) · (` (S Z)) · (` Z))))))
    · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
    · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
   —→⟨ ξ₁ β ⟩
    (ƛ
     (ƛ
      (ƛ
       (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) ·
       ((` (S (S Z))) · (` (S Z)) · (` Z)))))
    · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
   —→⟨ β ⟩
    ƛ
    (ƛ
     (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) ·
     ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z)))
   —→⟨ ζ (ζ (ξ₁ β)) ⟩
    ƛ
    (ƛ
     (ƛ (` (S (S Z))) · ((` (S (S Z))) · (` Z))) ·
     ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z)))
   —→⟨ ζ (ζ β) ⟩
    ƛ
    (ƛ
     (` (S Z)) ·
     ((` (S Z)) ·
      ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z))))
   —→⟨ ζ (ζ (ξ₂ (ξ₂ (ξ₁ β)))) ⟩
    ƛ
    (ƛ
     (` (S Z)) ·
     ((` (S Z)) ·
      ((ƛ (` (S (S Z))) · ((` (S (S Z))) · (` Z))) · (` Z))))
   —→⟨ ζ (ζ (ξ₂ (ξ₂ β))) ⟩
    ƛ (ƛ (` (S Z)) · ((` (S Z)) · ((` (S Z)) · ((` (S Z)) · (` Z)))))
   ∎)
   (done
    (ƛ
     (ƛ
      (′
       (` (S Z)) ·
       (′ (` (S Z)) · (′ (` (S Z)) · (′ (` (S Z)) · (′ (` Z)))))))))
_ = refl
```

## Naturals and fixpoint

We could simulate naturals using Church numerals, but computing
predecessor is tricky and expensive.  Instead, we use a different
representation, called Scott numerals, where a number is essentially
defined by the expression that corresponds to its own case statement.

Recall that Church numerals apply a given function for the
corresponding number of times.  Using named terms, we represent the
first three Church numerals as follows:

    zero  =  ƛ s ⇒ ƛ z ⇒ z
    one   =  ƛ s ⇒ ƛ z ⇒ s · z
    two   =  ƛ s ⇒ ƛ z ⇒ s · (s · z)

In contrast, for Scott numerals, we represent the first three naturals
as follows:

    zero = ƛ s ⇒ ƛ z ⇒ z
    one  = ƛ s ⇒ ƛ z ⇒ s · zero
    two  = ƛ s ⇒ ƛ z ⇒ s · one

Each representation expects two arguments, one corresponding to
the successor branch of the case (it expects an additional argument,
the predecessor of the current argument) and one corresponding to the
zero branch of the case.  (The cases could be in either order.
We put the successor case first to ease comparison with Church numerals.)

Here is the Scott representation of naturals encoded with de Bruijn indexes:
```
`zero : ∀ {Γ} → (Γ ⊢ ★)
`zero = ƛ ƛ (# 0)

`suc_ : ∀ {Γ} → (Γ ⊢ ★) → (Γ ⊢ ★)
`suc_ M  = (ƛ ƛ ƛ (# 1 · # 2)) · M

case : ∀ {Γ} → (Γ ⊢ ★) → (Γ ⊢ ★) → (Γ , ★ ⊢ ★)  → (Γ ⊢ ★)
case L M N = L · (ƛ N) · M
```
Here we have been careful to retain the exact form of our previous
definitions.  The successor branch expects an additional variable to
be in scope (as indicated by its type), so it is converted to an
ordinary term using lambda abstraction.

Applying successor to the zero indeed reduces to the Scott numeral
for one.

```
_ : eval (gas 100) (`suc_ {∅} `zero) ≡
    steps
        ((ƛ (ƛ (ƛ # 1 · # 2))) · (ƛ (ƛ # 0))
    —→⟨ β ⟩
         ƛ (ƛ # 1 · (ƛ (ƛ # 0)))
    ∎)
    (done (ƛ (ƛ (′ (` (S Z)) · (ƛ (ƛ (′ (` Z))))))))
_ = refl
```

We can also define fixpoint.  Using named terms, we define:

    μ f = (ƛ x ⇒ f · (x · x)) · (ƛ x ⇒ f · (x · x))

This works because:

      μ f
    ≡
      (ƛ x ⇒ f · (x · x)) · (ƛ x ⇒ f · (x · x))
    —→
      f · ((ƛ x ⇒ f · (x · x)) · (ƛ x ⇒ f · (x · x)))
    ≡
      f · (μ f)

With de Bruijn indices, we have the following:
```
μ_ : ∀ {Γ} → (Γ , ★ ⊢ ★) → (Γ ⊢ ★)
μ N  =  (ƛ ((ƛ (# 1 · (# 0 · # 0))) · (ƛ (# 1 · (# 0 · # 0))))) · (ƛ N)
```
The argument to fixpoint is treated similarly to the successor branch of case.

We can now define two plus two exactly as before:
```
infix 5 μ_

two : ∀ {Γ} → Γ ⊢ ★
two = `suc `suc `zero

four : ∀ {Γ} → Γ ⊢ ★
four = `suc `suc `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ ★
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))
```
Because `` `suc `` is now a defined term rather than primitive,
it is no longer the case that `plus · two · two` reduces to `four`,
but they do both reduce to the same normal term.


#### Exercise `plus-eval` (practice)

Use the evaluator to confirm that `plus · two · two` and `four`
normalise to the same term.

```
-- Your code goes here
```

#### Exercise `multiplication-untyped` (recommended)

Use the encodings above to translate your definition of
multiplication from previous chapters with the Scott
representation and the encoding of the fixpoint operator.
Confirm that two times two is four.

```
-- Your code goes here
```

#### Exercise `encode-more` (stretch)

Along the lines above, encode all of the constructs of
Chapter [More](/More/),
save for primitive numbers, in the untyped lambda calculus.

```
-- Your code goes here
```


## Multi-step reduction is transitive

In our formulation of the reflexive transitive closure of reduction,
i.e., the `—↠` relation, there is not an explicit rule for
transitivity. Instead the relation mimics the structure of lists by
providing a case for an empty reduction sequence and a case for adding
one reduction to the front of a reduction sequence.  The following is
the proof of transitivity, which has the same structure as the append
function `_++_` on lists.

```
—↠-trans : ∀{Γ}{A}{L M N : Γ ⊢ A}
         → L —↠ M
         → M —↠ N
         → L —↠ N
—↠-trans (M ∎) mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)
```

The following notation makes it convenient to employ
transitivity of `—↠`.

```
infixr 2 _—↠⟨_⟩_

_—↠⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —↠ M
    → M —↠ N
      ---------
    → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = —↠-trans L—↠M M—↠N
```

## Multi-step reduction is a congruence

Recall from Chapter [Induction](/Induction/) that a
relation `R` is a _congruence_ for a given function `f` if it is
preserved by that function, i.e., if `R x y` then `R (f x) (f y)`.
The term constructors `ƛ_` and `_·_` are functions, and so
the notion of congruence applies to them as well. Furthermore, when a
relation is a congruence for all of the term constructors, we
say that the relation is a congruence for the language in question, in
this case the untyped lambda calculus.

The rules `ξ₁`, `ξ₂`, and `ζ` ensure that the reduction relation is a
congruence for the untyped lambda calculus. The multi-step reduction
relation `—↠` is also a congruence, which we prove in the following
three lemmas.

```
appL-cong : ∀ {Γ} {L L' M : Γ ⊢ ★}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong {Γ}{L}{L'}{M} (L ∎) = L · M ∎
appL-cong {Γ}{L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁ r ⟩ appL-cong rs
```

The proof of `appL-cong` is by induction on the reduction sequence `L —↠ L'`.
* Suppose `L —↠ L` by `L ∎`. Then we have
  `L · M —↠ L · M` by `L · M ∎`.
* Suppose `L —↠ L''` by `L —→⟨ r ⟩ rs`, so
  `L —→ L'` by `r` and `L' —↠ L''` by `rs`.
  We have `L · M —→ L' · M` by `ξ₁ r` and
  `L' · M —↠ L'' · M` by the induction hypothesis applied to `rs`.
  We conclude that ``L · M —↠ L'' · M`` by putting these two
  facts together using `_—→⟨_⟩_`.

The proofs of `appR-cong` and `abs-cong` follow the same pattern as
the proof for `appL-cong`.

```
appR-cong : ∀ {Γ} {L M M' : Γ ⊢ ★}
         → M —↠ M'
           ---------------
         → L · M —↠ L · M'
appR-cong {Γ}{L}{M}{M'} (M ∎) = L · M ∎
appR-cong {Γ}{L}{M}{M'} (M —→⟨ r ⟩ rs) = L · M —→⟨ ξ₂ r ⟩ appR-cong rs
```

```
abs-cong : ∀ {Γ} {N N' : Γ , ★ ⊢ ★}
         → N —↠ N'
           ----------
         → ƛ N —↠ ƛ N'
abs-cong (M ∎) = ƛ M ∎
abs-cong (L —→⟨ r ⟩ rs) = ƛ L —→⟨ ζ r ⟩ abs-cong rs
```

## Unicode

This chapter uses the following unicode:

    ★  U+2605  BLACK STAR (\st)

The `\st` command permits navigation among many different stars;
the one we use is number 7.
