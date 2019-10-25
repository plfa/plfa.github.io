---
title     : "DeBruijn: Intrinsically-typed de Bruijn representation"
layout    : page
prev      : /Properties/
permalink : /DeBruijn/
next      : /More/
---

```
module plfa.part2.DeBruijn where
```

The previous two chapters introduced lambda calculus, with a
formalisation based on named variables, and terms defined
separately from types.  We began with that approach because it
is traditional, but it is not the one we recommend.  This
chapter presents an alternative approach, where named
variables are replaced by de Bruijn indices and terms are
indexed by their types.  Our new presentation is more compact, using
substantially fewer lines of code to cover the same ground.

There are two fundamental approaches to typed lambda calculi.
One approach, followed in the last two chapters,
is to first define terms and then define types.
Terms exist independent of types, and may have types assigned to them
by separate typing rules.
Another approach, followed in this chapter,
is to first define types and then define terms.
Terms and type rules are intertwined, and it makes no sense to talk
of a term without a type.
The two approaches are sometimes called _Curry style_ and _Church style_.
Following Reynolds, we will refer to them as _extrinsic_ and _intrinsic_.

The particular representation described here
was first proposed by
Thorsten Altenkirch and Bernhard Reus.
The formalisation of renaming and substitution
we use is due to Conor McBride.
Related work has been carried out by
James Chapman, James McKinna, and many others.


## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
```

## Introduction

There is a close correspondence between the structure of a
term and the structure of the derivation showing that it is
well typed.  For example, here is the term for the Church
numeral two:

    twoᶜ : Term
    twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

And here is its corresponding type derivation:

    ⊢twoᶜ : ∀ {A} → ∅ ⊢ twoᶜ ⦂ Ch A
    ⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
      where
      ∋s = S ("s" ≠ "z") Z
      ∋z = Z

(These are both taken from Chapter
[Lambda]({{ site.baseurl }}/Lambda/)
and you can see the corresponding derivation tree written out
in full
[here]({{ site.baseurl }}/Lambda/#derivation).)
The two definitions are in close correspondence, where:

  * `` `_ `` corresponds to `` ⊢` ``
  * `ƛ_⇒_`   corresponds to `⊢ƛ`
  * `_·_`    corresponds to `_·_`

Further, if we think of `Z` as zero and `S` as successor, then
the lookup derivation for each variable corresponds to a
number which tells us how many enclosing binding terms to
count to find the binding of that variable.  Here `"z"`
corresponds to `Z` or zero and `"s"` corresponds to `S Z` or
one.  And, indeed, `"z"` is bound by the inner abstraction
(count outward past zero abstractions) and `"s"` is bound by the
outer abstraction (count outward past one abstraction).

In this chapter, we are going to exploit this correspondence,
and introduce a new notation for terms that simultaneously
represents the term and its type derivation.  Now we will
write the following:

    twoᶜ  :  ∅ ⊢ Ch `ℕ
    twoᶜ  =  ƛ ƛ (# 1 · (# 1 · # 0))

A variable is represented by a natural number (written with
`Z` and `S`, and abbreviated in the usual way), and tells us
how many enclosing binding terms to count to find the binding
of that variable. Thus, `# 0` is bound at the inner `ƛ`, and
`# 1` at the outer `ƛ`.

Replacing variables by numbers in this way is called _de
Bruijn representation_, and the numbers themselves are called
_de Bruijn indices_, after the Dutch mathematician Nicolaas
Govert (Dick) de Bruijn (1918—2012), a pioneer in the creation
of proof assistants.  One advantage of replacing named
variables with de Bruijn indices is that each term now has a
unique representation, rather than being represented by the
equivalence class of terms under alpha renaming.

The other important feature of our chosen representation is
that it is _intrinsically typed_.  In the previous two chapters,
the definition of terms and the definition of types are
completely separate.  All terms have type `Term`, and nothing
in Agda prevents one from writing a nonsense term such as
`` `zero · `suc `zero `` which has no type.  Such terms that
exist independent of types are sometimes called _preterms_ or
_raw terms_.  Here we are going to replace the type `Term` of
raw terms by the type `Γ ⊢ A` of intrinsically-typed terms
which in context `Γ` have type `A`.

While these two choices fit well, they are independent.  One
can use de Bruijn indices in raw terms, or
have intrinsically-typed terms with names.  In
Chapter [Untyped]({{ site.baseurl }}/Untyped/),
we will introduce terms with de Bruijn indices that
are intrinsically scoped but not typed.


## A second example

De Bruijn indices can be tricky to get the hang of, so before
proceeding further let's consider a second example.  Here is
the term that adds two naturals:

    plus : Term
    plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
             case ` "m"
               [zero⇒ ` "n"
               |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

Note variable `"m"` is bound twice, once in a lambda abstraction
and once in the successor branch of the case.  Any appearance
of `"m"` in the successor branch must refer to the latter
binding, due to shadowing.

Here is its corresponding type derivation:

    ⊢plus : ∅ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
    ⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
             (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′)))))
      where
      ∋+  = (S ("+" ≠ "m") (S ("+" ≠ "n") (S ("+" ≠ "m") Z)))
      ∋m  = (S ("m" ≠ "n") Z)
      ∋n  = Z
      ∋m′ = Z
      ∋n′ = (S ("n" ≠ "m") Z)

The two definitions are in close correspondence, where in
addition to the previous correspondences we have:

  * `` `zero `` corresponds to `⊢zero`
  * `` `suc_ `` corresponds to `⊢suc`
  * `` case_[zero⇒_|suc_⇒_] `` corresponds to `⊢case`
  * `μ_⇒_` corresponds to `⊢μ`

Note the two lookup judgments `∋m` and `∋m′` refer to two
different bindings of variables named `"m"`.  In contrast, the
two judgments `∋n` and `∋n′` both refer to the same binding
of `"n"` but accessed in different contexts, the first where
`"n"` is the last binding in the context, and the second after
`"m"` is bound in the successor branch of the case.

Here is the term and its type derivation in the notation of this chapter:

    plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
    plus = μ ƛ ƛ case (# 1) (# 0) (`suc (# 3 · # 0 · # 1))

Reading from left to right, each de Bruijn index corresponds
to a lookup derivation:

  * `# 1` corresponds to `∋m`
  * `# 0` corresponds to `∋n`
  * `# 3` corresponds to `∋+`
  * `# 0` corresponds to `∋m′`
  * `# 1` corresponds to `∋n′`

The de Bruijn index counts the number of `S` constructs in the
corresponding lookup derivation.  Variable `"n"` bound in the
inner abstraction is referred to as `# 0` in the zero branch
of the case but as `# 1` in the successor branch of the case,
because of the intervening binding.  Variable `"m"` bound in the
lambda abstraction is referred to by the first `# 1` in the
code, while variable `"m"` bound in the successor branch of the
case is referred to by the second `# 0`.  There is no
shadowing: with variable names, there is no way to refer to
the former binding in the scope of the latter, but with de
Bruijn indices it could be referred to as `# 2`.

## Order of presentation

In the current chapter, the use of intrinsically-typed terms
necessitates that we cannot introduce operations such as
substitution or reduction without also showing that they
preserve types.  Hence, the order of presentation must change.

The syntax of terms now incorporates their typing rules, and the
definition of values now incorporates the Canonical Forms lemma.  The
definition of substitution is somewhat more involved, but incorporates
the trickiest part of the previous proof, the lemma establishing that
substitution preserves types.  The definition of reduction
incorporates preservation, which no longer requires a separate proof.

## Syntax

We now begin our formal development.

First, we get all our infix declarations out of the way.
We list separately operators for judgments, types, and terms:
```
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_
```

Since terms are intrinsically typed, we must define types and
contexts before terms.

### Types

As before, we have just two types, functions and naturals.
The formal definition is unchanged:
```
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type
```

### Contexts

Contexts are as before, but we drop the names.
Contexts are formalised as follows:
```
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```
A context is just a list of types, with the type of the most
recently bound variable on the right.  As before, we let `Γ`
and `Δ` range over contexts.  We write `∅` for the empty
context, and `Γ , A` for the context `Γ` extended by type `A`.
For example
```
_ : Context
_ = ∅ , `ℕ ⇒ `ℕ , `ℕ
```
is a context with two variables in scope, where the outer
bound one has type `` `ℕ ⇒ `ℕ ``, and the inner bound one has
type `` `ℕ ``.

### Variables and the lookup judgment

Intrinsically-typed variables correspond to the lookup judgment.
They are represented by de Bruijn indices, and hence also
correspond to natural numbers.  We write

    Γ ∋ A

for variables which in context `Γ` have type `A`.
The lookup judgement is formalised by a datatype indexed
by a context and a type.
It looks exactly like the old lookup judgment, but
with all variable names dropped:
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
Constructor `S` no longer requires an additional parameter,
since without names shadowing is no longer an issue.  Now
constructors `Z` and `S` correspond even more closely to the
constructors `here` and `there` for the element-of relation
`_∈_` on lists, as well as to constructors `zero` and `suc`
for natural numbers.

For example, consider the following old-style lookup
judgments:

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

They correspond to the following intrinsically-typed variables:
```
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ
_ = Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ ⇒ `ℕ
_ = S Z
```
In the given context, `"z"` is represented by `Z`
(as the most recently bound variable),
and `"s"` by `S Z`
(as the next most recently bound variable).

### Terms and the typing judgment

Intrinsically-typed terms correspond to the typing judgment.
We write

    Γ ⊢ A

for terms which in context `Γ` has type `A`.
The judgement is formalised by a datatype indexed
by a context and a type.
It looks exactly like the old typing judgment, but
with all terms and variable names dropped:
```
data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  `zero : ∀ {Γ}
      ---------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      ----------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ---------
    → Γ ⊢ A
```
The definition exploits the close correspondence between the
structure of terms and the structure of a derivation showing
that it is well typed: now we use the derivation _as_ the
term.

For example, consider the following old-style typing judgments:

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

They correspond to the following intrinsically-typed terms:
```
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ` S Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · ` Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · (` S Z · ` Z)

_ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ƛ (` S Z · (` S Z · ` Z))

_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (` S Z · (` S Z · ` Z))
```
The final term represents the Church numeral two.

### Abbreviating de Bruijn indices

We can use a natural number to select a type from a context:
```
lookup : Context → ℕ → Type
lookup (Γ , A) zero     =  A
lookup (Γ , _) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥
```
We intend to apply the function only when the natural is
shorter than the length of the context, which we indicate by
postulating an `impossible` term, just as we did
[here]({{ site.baseurl }}/Lambda/#primed).

Given the above, we can convert a natural to a corresponding
de Bruijn index, looking up its type in the context:
```
count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero     =  Z
count {Γ , _} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥
```
This requires the same trick as before.

We can then introduce a convenient abbreviation for variables:
```
#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n
```

With this abbreviation, we can rewrite the Church numeral two more compactly:
```
_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (# 1 · (# 1 · # 0))
```


### Test examples

We repeat the test examples from
Chapter [Lambda]({{ site.baseurl }}/Lambda/).
You can find them
[here]({{ site.baseurl }}/Lambda/#derivation)
for comparison.

First, computing two plus two on naturals:
```
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two
```
We generalise to arbitrary contexts because later we will give examples
where `two` appears nested inside binders.

Next, computing two plus two on Church numerals:
```
Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```
As before we generalise everything to arbitrary
contexts.  While we are at it, we also generalise `twoᶜ` and
`plusᶜ` to Church numerals over arbitrary types.



#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers, now adapted to the intrinsically-typed
DeBruijn representation.

```
-- Your code goes here
```


## Renaming

Renaming is a necessary prelude to substitution, enabling us
to "rebase" a term from one context to another.  It
corresponds directly to the renaming result from the previous
chapter, but here the theorem that ensures renaming preserves
typing also acts as code that performs renaming.

As before, we first need an extension lemma that allows us to
extend the context when we encounter a binder. Given a map
from variables in one context to variables in another,
extension yields a map from the first context extended to the
second context similarly extended.  It looks exactly like the
old extension lemma, but with all names and terms dropped:
```
ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```
Let `ρ` be the name of the map that takes variables in `Γ`
to variables in `Δ`.  Consider the de Bruijn index of the
variable in `Γ , B`:

* If it is `Z`, which has type `B` in `Γ , B`,
  then we return `Z`, which also has type `B` in `Δ , B`.

* If it is `S x`, for some variable `x` in `Γ`, then `ρ x`
  is a variable in `Δ`, and hence `S (ρ x)` is a variable in
  `Δ , B`.

With extension under our belts, it is straightforward
to define renaming.  If variables in one context map to
variables in another, then terms in the first context map to
terms in the second:
```
rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N)          =  μ (rename (ext ρ) N)
```
Let `ρ` be the name of the map that takes variables in `Γ`
to variables in `Δ`.  Let's unpack the first three cases:

* If the term is a variable, simply apply `ρ`.

* If the term is an abstraction, use the previous result
  to extend the map `ρ` suitably and recursively rename
  the body of the abstraction.

* If the term is an application, recursively rename both
  the function and the argument.

The remaining cases are similar, recursing on each subterm,
and extending the map whenever the construct introduces a
bound variable.

Whereas before renaming was a result that carried evidence
that a term is well typed in one context to evidence that it
is well typed in another context, now it actually transforms
the term, suitably altering the bound variables. Typechecking
the code in Agda ensures that it is only passed and returns
terms that are well typed by the rules of simply-typed lambda
calculus.

Here is an example of renaming a term with one free
and one bound variable:
```
M₀ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₀ = ƛ (# 1 · (# 1 · # 0))

M₁ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
M₁ = ƛ (# 2 · (# 2 · # 0))

_ : rename S_ M₀ ≡ M₁
_ = refl
```
In general, `rename S_` will increment the de Bruijn index for
each free variable by one, while leaving the index for each
bound variable unchanged.  The code achieves this naturally:
the map originally increments each variable by one, and is
extended for each bound variable by a map that leaves it
unchanged.

We will see below that renaming by `S_` plays a key role in
substitution.  For traditional uses of de Bruijn indices
without intrinsic typing, this is a little tricky. The code
keeps count of a number where all greater indexes are free and
all smaller indexes bound, and increment only indexes greater
than the number. It's easy to have off-by-one errors.  But
it's hard to imagine an off-by-one error that preserves
typing, and hence the Agda code for intrinsically-typed de Bruijn
terms is intrinsically reliable.


## Simultaneous Substitution

Because de Bruijn indices free us of concerns with renaming,
it becomes easy to provide a definition of substitution that
is more general than the one considered previously.  Instead
of substituting a closed term for a single variable, it
provides a map that takes each free variable of the original
term to another term. Further, the substituted terms are over
an arbitrary context, and need not be closed.

The structure of the definition and the proof is remarkably
close to that for renaming.  Again, we first need an extension
lemma that allows us to extend the context when we encounter a
binder.  Whereas renaming concerned a map from variables
in one context to variables in another, substitution takes a
map from variables in one context to _terms_ in another.
Given a map from variables in one context to terms over
another, extension yields a map from the first context
extended to the second context similarly extended:
```
exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)
```
Let `σ` be the name of the map that takes variables in `Γ`
to terms over `Δ`.  Consider the de Bruijn index of the
variable in `Γ , B`:

* If it is `Z`, which has type `B` in `Γ , B`,
  then we return the term `` ` Z``, which also has
  type `B` in `Δ , B`.

* If it is `S x`, for some variable `x` in `Γ`, then
  `σ x` is a term in `Δ`, and hence `rename S_ (σ x)`
  is a term in `Δ , B`.

This is why we had to define renaming first, since
we require it to convert a term over context `Δ`
to a term over the extended context `Δ , B`.

With extension under our belts, it is straightforward
to define substitution.  If variables in one context map
to terms over another, then terms in the first context
map to terms in the second:
```
subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)          =  μ (subst (exts σ) N)
```
Let `σ` be the name of the map that takes variables in `Γ`
to terms over `Δ`.  Let's unpack the first three cases:

* If the term is a variable, simply apply `σ`.

* If the term is an abstraction, use the previous result
  to extend the map `σ` suitably and recursively substitute
  over the body of the abstraction.

* If the term is an application, recursively substitute over
  both the function and the argument.

The remaining cases are similar, recursing on each subterm,
and extending the map whenever the construct introduces a
bound variable.

## Single substitution

From the general case of substitution for multiple free
variables it is easy to define the special case of
substitution for one free variable:
```
_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x
```
In a term of type `A` over context `Γ , B`, we replace the
variable of type `B` by a term of type `B` over context `Γ`.
To do so, we use a map from the context `Γ , B` to the context
`Γ`, that maps the last variable in the context to the term of
type `B` and every other free variable to itself.

Consider the previous example:

* `` (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] `` yields
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") ``

Here is the example formalised:
```
M₂ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₂ = ƛ # 1 · (# 1 · # 0)

M₃ : ∅ ⊢ `ℕ ⇒ `ℕ
M₃ = ƛ `suc # 0

M₄ : ∅ ⊢ `ℕ ⇒ `ℕ
M₄ = ƛ (ƛ `suc # 0) · ((ƛ `suc # 0) · # 0)

_ : M₂ [ M₃ ] ≡ M₄
_ = refl
```

Previously, we presented an example of substitution that we
did not implement, since it needed to rename the bound
variable to avoid capture:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` should yield
  `` ƛ "z" ⇒ ` "z" · (` "x" · `zero) ``

Say the bound `"x"` has type `` `ℕ ⇒ `ℕ ``, the substituted
`"y"` has type `` `ℕ ``, and the free `"x"` also has type ``
`ℕ ⇒ `ℕ ``.  Here is the example formalised:
```
M₅ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₅ = ƛ # 0 · # 1

M₆ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ
M₆ = # 0 · `zero

M₇ : ∅ , `ℕ ⇒ `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₇ = ƛ (# 0 · (# 1 · `zero))

_ : M₅ [ M₆ ] ≡ M₇
_ = refl
```

The logician Haskell Curry observed that getting the
definition of substitution right can be a tricky business.  It
can be even trickier when using de Bruijn indices, which can
often be hard to decipher.  Under the current approach, any
definition of substitution must, of necessity, preserves
types.  While this makes the definition more involved, it
means that once it is done the hardest work is out of the way.
And combining definition with proof makes it harder for errors
to sneak in.


## Values

The definition of value is much as before, save that the
added types incorporate the same information found in the
Canonical Forms lemma:
```
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)
```

Here `zero` requires an implicit parameter to aid inference,
much in the same way that `[]` did in
[Lists]({{ site.baseurl }}/Lists/).


## Reduction

The reduction rules are the same as those given earlier, save
that for each term we must specify its types.  As before, we
have compatibility rules that reduce a part of a term,
labelled with `ξ`, and rules that simplify a constructor
combined with a destructor, labelled with `β`:

```
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]
```
The definition states that `M —→ N` can only hold of terms `M`
and `N` which _both_ have type `Γ ⊢ A` for some context `Γ`
and type `A`.  In other words, it is _built-in_ to our
definition that reduction preserves types.  There is no
separate Preservation theorem to prove.  The Agda type-checker
validates that each term preserves types.  In the case of `β`
rules, preservation depends on the fact that substitution
preserves types, which is built-in to our
definition of substitution.


## Reflexive and transitive closure

The reflexive and transitive closure is exactly as before.
We simply cut-and-paste the previous definition:
```
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```


## Examples

We reiterate each of our previous examples.  First, the Church
numeral two applied to the successor function and zero yields
the natural number two:
```
_ : twoᶜ · sucᶜ · `zero {∅} —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ (sucᶜ · (sucᶜ · # 0))) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
   `suc (`suc `zero)
  ∎
```
As before, we need to supply an explicit context to `` `zero ``.

Next, a sample reduction demonstrating that two plus two is four:
```
_ : plus {∅} · two · two —↠ `suc `suc `suc `suc `zero
_ =
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z))) · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ case two (` Z) (`suc (plus · ` Z · ` S Z))) · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two two (`suc (plus · ` Z · two))
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
      · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ case (`suc `zero) (` Z) (`suc (plus · ` Z · ` S Z))) · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case (`suc `zero) (two) (`suc (plus · ` Z · two)))
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc (`suc (plus · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc (`suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
      · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc (`suc ((ƛ case `zero (` Z) (`suc (plus · ` Z · ` S Z))) · two))
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc (`suc (case `zero (two) (`suc (plus · ` Z · two))))
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎
```

And finally, a similar sample reduction for Church numerals:
```
_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero {∅}
_ =
  begin
    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ ƛ ƛ twoᶜ · ` S Z · (` S S Z · ` S Z · ` Z)) · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ ƛ twoᶜ · ` S Z · (twoᶜ · ` S Z · ` Z)) · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` Z)) · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · ((ƛ sucᶜ · (sucᶜ · ` Z)) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (sucᶜ · `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · `suc (`suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · `suc (`suc (`suc `zero))
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎
```

## Values do not reduce

We have now completed all the definitions, which of
necessity subsumed some of the propositions from the
earlier development: Canonical Forms,
Substitution preserves types, and Preservation.
We now turn to proving the remaining results from the
previous development.

#### Exercise `V¬—→` (practice)

Following the previous development, show values do
not reduce, and its corollary, terms that reduce are not
values.

```
-- Your code goes here
```

## Progress

As before, every term that is well typed and closed is either
a value or takes a reduction step.  The formulation of progress
is just as before, but annotated with types:
```
data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
```

The statement and proof of progress is much as before,
appropriately annotated.  We no longer need
to explicitly refer to the Canonical Forms lemma, since it
is built-in to the definition of value:
```
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ N)                          =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                     =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                 =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                    =  step (β-ƛ VM)
progress (`zero)                        =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                     =  step (ξ-suc M—→M′)
...    | done VM                        =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                     =  step (ξ-case L—→L′)
...    | done V-zero                    =  step (β-zero)
...    | done (V-suc VL)                =  step (β-suc VL)
progress (μ N)                          =  step (β-μ)
```


## Evaluation

Before, we combined progress and preservation to evaluate a term.
We can do much the same here, but we no longer need to explicitly
refer to preservation, since it is built-in to the definition of reduction.

As previously, gas is specified by a natural number:
```
data Gas : Set where
  gas : ℕ → Gas
```
When our evaluator returns a term `N`, it will either give evidence that
`N` is a value or indicate that it ran out of gas:
```
data Finished {Γ A} (N : Γ ⊢ A) : Set where

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
data Steps : ∀ {A} → ∅ ⊢ A → Set where

  steps : ∀ {A} {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
```
The evaluator takes gas and a term and returns the corresponding steps:
```
eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```
The definition is a little simpler than previously, as we no longer need
to invoke preservation.

## Examples

We reiterate each of our previous examples.  We re-define the term
`sucμ` that loops forever:
```
sucμ : ∅ ⊢ `ℕ
sucμ = μ (`suc (# 0))
```
To compute the first three steps of the infinite reduction sequence,
we evaluate with three steps worth of gas:
```
_ : eval (gas 3) sucμ ≡
  steps
   (μ `suc ` Z
   —→⟨ β-μ ⟩
    `suc (μ `suc ` Z)
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ `suc ` Z))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ `suc ` Z)))
   ∎)
   out-of-gas
_ = refl
```

The Church numeral two applied to successor and zero:
```
_ : eval (gas 100) (twoᶜ · sucᶜ · `zero) ≡
  steps
   ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) · `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ `suc ` Z) · ((ƛ `suc ` Z) · `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ `suc ` Z) · `suc `zero
   —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
   ∎)
   (done (V-suc (V-suc V-zero)))
_ = refl
```

Two plus two is four:
```
_ : eval (gas 100) (plus · two · two) ≡
  steps
   ((μ
     (ƛ
      (ƛ
       case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · `suc (`suc `zero)
    · `suc (`suc `zero)
   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ
     (ƛ
      case (` (S Z)) (` Z)
      (`suc
       ((μ
         (ƛ
          (ƛ
           case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
        · ` Z
        · ` (S Z)))))
    · `suc (`suc `zero)
    · `suc (`suc `zero)
   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ
     case (`suc (`suc `zero)) (` Z)
     (`suc
      ((μ
        (ƛ
         (ƛ
          case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` Z
       · ` (S Z))))
    · `suc (`suc `zero)
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case (`suc (`suc `zero)) (`suc (`suc `zero))
    (`suc
     ((μ
       (ƛ
        (ƛ
         case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · `suc (`suc `zero)))
   —→⟨ β-suc (V-suc V-zero) ⟩
    `suc
    ((μ
      (ƛ
       (ƛ
        case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · `suc `zero
     · `suc (`suc `zero))
   —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc
    ((ƛ
      (ƛ
       case (` (S Z)) (` Z)
       (`suc
        ((μ
          (ƛ
           (ƛ
            case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
         · ` Z
         · ` (S Z)))))
     · `suc `zero
     · `suc (`suc `zero))
   —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc
    ((ƛ
      case (`suc `zero) (` Z)
      (`suc
       ((μ
         (ƛ
          (ƛ
           case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
        · ` Z
        · ` (S Z))))
     · `suc (`suc `zero))
   —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc
    case (`suc `zero) (`suc (`suc `zero))
    (`suc
     ((μ
       (ƛ
        (ƛ
         case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc
    (`suc
     ((μ
       (ƛ
        (ƛ
         case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · `zero
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc
    (`suc
     ((ƛ
       (ƛ
        case (` (S Z)) (` Z)
        (`suc
         ((μ
           (ƛ
            (ƛ
             case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
          · ` Z
          · ` (S Z)))))
      · `zero
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc
    (`suc
     ((ƛ
       case `zero (` Z)
       (`suc
        ((μ
          (ƛ
           (ƛ
            case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
         · ` Z
         · ` (S Z))))
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc
    (`suc
     case `zero (`suc (`suc `zero))
     (`suc
      ((μ
        (ƛ
         (ƛ
          case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` Z
       · `suc (`suc `zero))))
   —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
   ∎)
   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
```

And the corresponding term for Church numerals:
```
_ : eval (gas 100) (plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero) ≡
  steps
   ((ƛ
     (ƛ
      (ƛ (ƛ ` (S (S (S Z))) · ` (S Z) · (` (S (S Z)) · ` (S Z) · ` Z)))))
    · (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z)))
    · (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z)))
    · (ƛ `suc ` Z)
    · `zero
   —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ
     (ƛ
      (ƛ
       (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · ` (S Z) ·
       (` (S (S Z)) · ` (S Z) · ` Z))))
    · (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z)))
    · (ƛ `suc ` Z)
    · `zero
   —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ
     (ƛ
      (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · ` (S Z) ·
      ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · ` (S Z) · ` Z)))
    · (ƛ `suc ` Z)
    · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ
     (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) ·
     ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) · ` Z))
    · `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) ·
    ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) · `zero)
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) ·
    ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) · `zero)
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) ·
    ((ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) · `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) ·
    ((ƛ `suc ` Z) · ((ƛ `suc ` Z) · `zero))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) ·
    ((ƛ `suc ` Z) · `suc `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) · `suc (`suc `zero)
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    (ƛ `suc ` Z) · ((ƛ `suc ` Z) · `suc (`suc `zero))
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ `suc ` Z) · `suc (`suc (`suc `zero))
   —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc (`suc (`suc (`suc `zero)))
   ∎)
   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
```

We omit the proof that reduction is deterministic, since it is
tedious and almost identical to the previous proof.


#### Exercise `mul-example` (recommended)

Using the evaluator, confirm that two times two is four.

```
-- Your code goes here
```


## Intrinsic typing is golden

Counting the lines of code is instructive.  While this chapter
covers the same formal development as the previous two
chapters, it has much less code.  Omitting all the examples,
and all proofs that appear in Properties but not DeBruijn
(such as the proof that reduction is deterministic), the
number of lines of code is as follows:

    Lambda                      216
    Properties                  235
    DeBruijn                    275

The relation between the two approaches approximates the
golden ratio: extrinsically-typed terms
require about 1.6 times as much code as intrinsicaly-typed.

## Unicode

This chapter uses the following unicode:

    σ  U+03C3  GREEK SMALL LETTER SIGMA (\Gs or \sigma)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₃  U+20B3  SUBSCRIPT THREE (\_3)
    ₄  U+2084  SUBSCRIPT FOUR (\_4)
    ₅  U+2085  SUBSCRIPT FIVE (\_5)
    ₆  U+2086  SUBSCRIPT SIX (\_6)
    ₇  U+2087  SUBSCRIPT SEVEN (\_7)
    ≠  U+2260  NOT EQUAL TO (\=n)

