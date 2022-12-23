---
title     : "StlcNew: The Simply Typed Lambda-Calculus"
permalink : /StlcNew
---

The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It embodies the concept of
_functional abstraction_, which shows up in almost every programming
language in some form (as functions, procedures, or methods).
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has just the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations;
we will be slightly more pragmatic and choose booleans as our base type.

This chapter formalises the simply-typed lambda calculus, giving its
syntax, small-step semantics, and typing rules.
The [next chapter](StlcNewProp) reviews its main properties,
including progress and preservation.
The most challenging new concepts will be
_variable binding_ and _substitution_.

We choose booleans as our base type for simplicity.  In later
chapters we'll enrich lambda calculus with types including naturals,
products, sums, and lists.

## Imports

\begin{code}
module StlcNew where

open import Data.String using (String; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
\end{code}

## Syntax

We have just two types.

  * Functions, `A ⇒ B`
  * Booleans, `𝔹`

We require some form of base type, because otherwise the set of types
would be empty. Church used a trivial base type `o` with no operations.
For us, it is more convenient to use booleans. Later we will consider
numbers as a base type.

Here is the syntax of types in BNF.

    A, B, C  ::=  A ⇒ B | 𝔹

And here it is formalised in Agda.

\begin{code}
infixr 20 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  𝔹 : Type
\end{code}

Terms have six constructs. Three are for the core lambda calculus:

  * Variables, `# x`
  * Abstractions, `ƛ x ⇒ N`
  * Applications, `L · M`

and three are for the base type, booleans:

  * True, `true`
  * False, `false`
  * Conditions, `if L then M else N`

Abstraction is also called lambda abstraction, and is the construct
from which the calculus takes its name.

With the exception of variables, each term form either constructs
a value of a given type (abstractions yield functions, true and
false yield booleans) or deconstructs it (applications use functions,
conditionals use booleans). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in BNF.

    L, M, N  ::=  # x | λ x ⇒ N | L · M | true | false | if L then M else N

And here it is formalised in Agda.

\begin{code}
infix  30 #_
infixl 20 _·_
infix  15 ƛ_⇒_
infix  15 if_then_else_

Id : Set
Id = String

data Term : Set where
  #_ : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _·_ : Term → Term → Term
  true : Term
  false : Term
  if_then_else_ : Term → Term → Term → Term
\end{code}


### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `# x`
for a term that is a variable. Agda requires we distinguish.
Often researchers use `var x` rather than `# x`, but we chose
the latter since it is less noisy.

Similarly, informal presentation often use the same notation for
function types, lambda abstraction, and function application in
both the object language (the language one is describing) and the
meta-language (the language in which the description is written),
trusting readers can use context to distinguish the two.  Agda is
is not quite so forgiving, so here we use `A ⇒ B`, `ƛ x ⇒ N`,
and `L · M` for the object language, as compared to `A → B`, `λ x → N`,
and `L M` in our meta-language, Agda.


### Examples

Here are a couple of example terms, `not` of type
`𝔹 ⇒ 𝔹`, which complements its argument, and `two` of type
`(𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹` which takes a function and a boolean
and applies the function to the boolean twice.

\begin{code}
not two : Term
not =  ƛ "x" ⇒ if # "x" then false else true
two =  ƛ "f" ⇒ ƛ "x" ⇒ # "f" · (# "f" · # "x")
\end{code}


### Bound and free variables

In an abstraction `ƛ x ⇒ N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  One of the most important
aspects of lambda calculus is that names of bound variables are
irrelevant.  Thus the five terms

* `` ƛ "f" ⇒ ƛ "x" ⇒ # "f" · (# "f" · # "x") ``
* `` ƛ "g" ⇒ ƛ "y" ⇒ # "g" · (# "g" · # "y") ``
* `` ƛ "fred" ⇒ ƛ "xander" ⇒ # "fred" · (# "fred" · # "xander") ``
* `` λ[ 😇 ∶ 𝔹 ⇒ 𝔹 ] λ[ 😈  ∶ 𝔹 ] ` 😇 · (` 😇 · ` 😈 ) ``
* `` ƛ "x" ⇒ ƛ "f" ⇒ # "x" · (# "x" · # "f") ``

are all considered equivalent.  This equivalence relation
is often called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms.

* `` ƛ "f" ⇒ ƛ "x" ⇒ # "f" · (# "f" · # "x") ``
  Both variable `f` and `x` are bound.

* `` ƛ "x" ⇒ # "f" · (# "f" · # "x") ``
  has `x` as a bound variable but `f` as a free variable.

* `` # "f" · (# "f" · # "x") ``
  has both `f` and `x` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.  A formal definition of bound and free variables will be
given in the next chapter.

Different occurrences of a variable may be bound and free.
In the term

    (ƛ "x" ⇒ # "x") · # "x"

the inner occurrence of `x` is bound while the outer occurrence is free.
Note that by alpha renaming, the term above is equivalent to

    (ƛ "y" ⇒ # "y") · # "x"

in which `y` is bound and `x` is free.  A common convention, called the
Barendregt convention, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.


### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus,

* `(𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹` abbreviates `(𝔹 ⇒ 𝔹) ⇒ (𝔹 ⇒ 𝔹)`
* `two · not · true` abbreviates `(two · not) · true`.

We choose the binding strength for abstractions and conditionals
to be weaker than application. For instance,

* `` ƛ "f" ⇒ ƛ "x" ⇒ # "f" · (# "f" · # "x") ``
  - denotes `` (ƛ "f" ⇒ (ƛ "x" ⇒ (# "f" · (# "f" · # "x")))) ``
  - and not `` (ƛ "f" ⇒ (ƛ "x" ⇒ # "f")) · (# "f" · # "x") ``

\begin{code}
_ : (𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹 ≡ (𝔹 ⇒ 𝔹) ⇒ (𝔹 ⇒ 𝔹)
_ = refl

_ : two · not · true ≡ (two · not) · true
_ = refl

_ : ƛ "f" ⇒ ƛ "x" ⇒ # "f" · (# "f" · # "x")
      ≡ (ƛ "f" ⇒ (ƛ "x" ⇒ (# "f" · (# "f" · # "x"))))
_ = refl
\end{code}

### Quiz

* What is the type of the following term?

    ƛ "f" ⇒ # "f" · (# "f"  · true)

  1. `𝔹 ⇒ (𝔹 ⇒ 𝔹)`
  2. `(𝔹 ⇒ 𝔹) ⇒ 𝔹`
  3. `𝔹 ⇒ 𝔹 ⇒ 𝔹`
  4. `𝔹 ⇒ 𝔹`
  5. `𝔹`

  Give more than one answer if appropriate.

* What is the type of the following term?

    (ƛ "f" ⇒ # "f" · (# "f"  · true)) · not

  1. `𝔹 ⇒ (𝔹 ⇒ 𝔹)`
  2. `(𝔹 ⇒ 𝔹) ⇒ 𝔹`
  3. `𝔹 ⇒ 𝔹 ⇒ 𝔹`
  4. `𝔹 ⇒ 𝔹`
  5. `𝔹`

  Give more than one answer if appropriate.

## Values

We only consider reduction of _closed_ terms,
those that contain no free variables.  We consider
a precise definition of free variables in
[StlcPropNew](StlcPropNew).

A term is a value if it is fully reduced.
For booleans, the situation is clear: `true` and
`false` are values, while conditionals are not.
For functions, applications are not values, because
we expect them to further reduce, and variables are
not values, because we focus on closed terms.
Following convention, we treat all abstractions
as values.

The predicate `Value M` holds if term `M` is a value.

\begin{code}
data Value : Term → Set where
  value-λ     : ∀ {x N} → Value (ƛ x ⇒ N)
  value-true  : Value true
  value-false : Value false
\end{code}

We let `V` and `W` range over values.


### Formal vs informal

In informal presentations of formal semantics, using
`V` as the name of a metavariable is sufficient to
indicate that it is a value. In Agda, we must explicitly
invoke the `Value` predicate.

### Other approaches

An alternative is not to focus on closed terms,
to treat variables as values, and to treat
`ƛ x ⇒ N` as a value only if `N` is a value.
Indeed, this is how Agda normalises terms.
We consider this approach in a [later chapter](Untyped).

## Substitution

The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have

      (ƛ "f" ⇒ # "f" · (# "f" · true)) · not
    ⟹
      not · (not · true)

where we substitute `not` for `` `f `` in the body
of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
"substitute term `V` for free occurrences of variable `x` in term `N`",
or, more compactly, "substitute `V` for `x` in `N`".
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since we
always substitute values.

Here are some examples.

* `` # "f" [ "f" := not ] `` yields `` not ``
* `` true [ "f" := not ] `` yields `` true ``
* `` (# "f" · true) [ "f" := not ] `` yields `` not · true ``
* `` (# "f" · (# "f" · true)) [ "f" := not ] `` yields `` not · (not · true) ``
* `` (ƛ "x" ⇒ # "f" · (# "f" · # "x")) [ "f" := not ] `` yields `` ƛ "x" ⇒ not · (not · # "x") ``
* `` (ƛ "y" ⇒ # "y") [ "x" := true ] `` yields `` ƛ "y" ⇒ # "y" ``
* `` (ƛ "x" ⇒ # "x") [ "x" := true ] `` yields `` ƛ "x" ⇒ # "x" ``

The last example is important: substituting `true` for `x` in
`` ƛ "x" ⇒ # "x" `` does _not_ yield `` ƛ "x" ⇒ true ``.
The reason for this is that `x` in the body of `` ƛ "x" ⇒ # "x" ``
is _bound_ by the abstraction.  An important feature of abstraction
is that the choice of bound names is irrelevant: both
`` ƛ "x" ⇒ # "x" `` and `` ƛ "y" ⇒ # "y" `` stand for the
identity function.  The way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they both just happen to have the same
name.

Here is the formal definition in Agda.

\begin{code}
infix 25 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(# x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = # x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no  _ = ƛ x ⇒ (N [ y := V ])
(L · M) [ y := V ] =  (L [ y := V ]) · (M [ y := V ])
(true) [ y := V ] = true
(false) [ y := V ] = false
(if L then M else N) [ y := V ] =
  if L [ y := V ] then M [ y := V ] else N [ y := V ]
\end{code}

The two key cases are variables and abstraction.

* For variables, we compare `w`, the variable we are substituting for,
with `x`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x` unchanged.

* For abstractions, we compare `w`, the variable we are substituting for,
with `x`, the variable bound in the abstraction. If they are the same,
we yield the abstraction unchanged, otherwise we substitute inside the body.

In all other cases, we push substitution recursively into
the subterms.



#### Examples

Here is confirmation that the examples above are correct.

\begin{code}
_ : # "f" [ "f" := not ] ≡  not
_ = refl

_ : true [ "f" := not ] ≡ true
_ = refl

_ : (# "f" · true) [ "f" := not ] ≡ not · true
_ = refl

_ : (# "f" · (# "f" · true)) [ "f" := not ] ≡ not · (not · true)
_ = refl

_ : (ƛ "x" ⇒ # "f" · (# "f" · # "x")) [ "f" := not ] ≡ ƛ "x" ⇒ not · (not · # "x")
_ = refl

_ : (ƛ "y" ⇒ # "y") [ "x" := true ] ≡ ƛ "y" ⇒ # "y"
_ = refl

_ : (ƛ "x" ⇒ # "x") [ "x" := true ] ≡ ƛ "x" ⇒ # "x"
_ = refl
\end{code}

#### Quiz

What is the result of the following substitution?

    (ƛ "y" ⇒ # "x" · (ƛ "x" ⇒ # "x")) [ "x" := true ]

1. `` (ƛ "y" ⇒ # "x" · (ƛ "x" ⇒ # "x")) ``
2. `` (ƛ "y" ⇒ # "x" · (ƛ "x" ⇒ true)) ``
3. `` (ƛ "y" ⇒ true · (ƛ "x" ⇒ # "x")) ``
4. `` (ƛ "y" ⇒ true · (ƛ "x" ⇒ true)) ``


## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.  To reduce a
conditional, we first reduce the condition until it becomes a value;
if the condition is true the conditional reduces to the first
branch and if false it reduces to the second branch.

In an informal presentation of the formal semantics,
the rules for reduction are written as follows.

    L ⟹ L′
    --------------- ξ·₁
    L · M ⟹ L′ · M

    M ⟹ M′
    --------------- ξ·₂
    V · M ⟹ V · M′

    --------------------------------- βλ·
    (ƛ x ⇒ N) · V ⟹ N [ x := V ]

    L ⟹ L′
    ----------------------------------------- ξif
    if L then M else N ⟹ if L′ then M else N

    -------------------------- βif-true
    if true then M else N ⟹ M

    --------------------------- βif-false
    if false then M else N ⟹ N

As we will show later, the rules are deterministic, in that
at most one rule applies to every term.  As we will also show
later, for every well-typed term either a reduction applies
or it is a value.

The rules break into two sorts. Compatibility rules
direct us to reduce some part of a term.
We give them names starting with the Greek letter xi, `ξ`.
Once a term is sufficiently
reduced, it will consist of a constructor and
a deconstructor, in our case `λ` and `·`, or
`if` and `true`, or `if` and `false`.
We give them names starting with the Greek letter beta, `β`,
and indeed such rules are traditionally called beta rules.

Here are the above rules formalised in Agda.

\begin{code}
infix 10 _⟹_

data _⟹_ : Term → Term → Set where

  ξ·₁ : ∀ {L L′ M}
    → L ⟹ L′
      -----------------
    → L · M ⟹ L′ · M

  ξ·₂ : ∀ {V M M′}
    → Value V
    → M ⟹ M′
      -----------------
    → V · M ⟹ V · M′

  βλ· : ∀ {x N V}
    → Value V
      ------------------------------------
    → (ƛ x ⇒ N) · V ⟹ N [ x := V ]

  ξif : ∀ {L L′ M N}
    → L ⟹ L′
      -------------------------------------------
    → if L then M else N ⟹ if L′ then M else N

  βif-true : ∀ {M N}
      ----------------------------
    → if true then M else N ⟹ M

  βif-false : ∀ {M N}
      -----------------------------
    → if false then M else N ⟹ N
\end{code}


#### Quiz

What does the following term step to?

    (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x")  ⟹  ???

1.  `` (ƛ "x" ⇒ # "x") ``
2.  `` (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") ``
3.  `` (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") ``

What does the following term step to?

    (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x")  ⟹  ???

1.  `` (ƛ "x" ⇒ # "x") ``
2.  `` (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") ``
3.  `` (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") ``

What does the following term step to?  (Where `not` is as defined above.)

    not · true  ⟹  ???

1.  `` if # "x" then false else true ``
2.  `` if true then false else true ``
3.  `` true ``
4.  `` false ``

What does the following term step to?  (Where `two` and `not` are as defined above.)

    two · not · true  ⟹  ???

1.  `` not · (not · true) ``
2.  `` (ƛ "x" ⇒ not · (not · # "x")) · true ``
3.  `` true ``
4.  `` false ``

## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `⟹*` of the step function `⟹`.
In an informal presentation of the formal semantics, the rules
are written as follows.

    ------- done
    M ⟹* M

    L ⟹ M
    M ⟹* N
    ------- step
    L ⟹* N

Here it is formalised in Agda, along similar lines to what
we used for reasoning about [Equality](Equality).

\begin{code}
infix  2 _⟹*_
infix  1 begin_
infixr 2 _⟹⟨_⟩_
infix  3 _∎

data _⟹*_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M ⟹* M

  _⟹⟨_⟩_ : ∀ L {M N}
    → L ⟹ M
    → M ⟹* N
      ---------
    → L ⟹* N

begin_ : ∀ {M N} → (M ⟹* N) → (M ⟹* N)
begin M⟹*N = M⟹*N
\end{code}

We can read this as follows.

* From term `M`, we can take no steps, giving `M ∎` of type `M ⟹* M`.

* From term `L` we can take a single step `L⟹M` of type `L ⟹ M`
  followed by zero or more steps `M⟹*N` of type `M ⟹* N`,
  giving `L ⟨ L⟹M ⟩ M⟹*N` of type `L ⟹* N`.

The names have been chosen to allow us to lay
out example reductions in an appealing way.

\begin{code}
_ : not · true ⟹* false
_ =
  begin
    not · true
  ⟹⟨ βλ· value-true ⟩
    if true then false else true
  ⟹⟨ βif-true ⟩
    false
  ∎

_ : two · not · true ⟹* true
_ =
  begin
    two · not · true
  ⟹⟨ ξ·₁ (βλ· value-λ) ⟩
    (ƛ "x" ⇒ not · (not · # "x")) · true
  ⟹⟨ βλ· value-true ⟩
    not · (not · true)
  ⟹⟨ ξ·₂ value-λ (βλ· value-true) ⟩
    not · (if true then false else true)
  ⟹⟨ ξ·₂ value-λ βif-true  ⟩
    not · false
  ⟹⟨ βλ· value-false ⟩
    if false then false else true
  ⟹⟨ βif-false ⟩
    true
  ∎
\end{code}

Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.


## Typing

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

In general, we use typing _judgments_ of the form

    Γ ⊢ M ⦂ A

to assert in type environment `Γ` that term `M` has type `A`.
Environment `Γ` provides types for all the free variables in `M`.

Here are three examples.

* `` ∅ , "f" ⦂ 𝔹 ⇒ 𝔹 , "x" ⦂ 𝔹 ⊢ # "f" · (# "f" · # "x") ⦂  𝔹 ``
* `` ∅ , "f" ⦂ 𝔹 ⇒ 𝔹 ⊢ (ƛ "x" ⇒ # "f" · (# "f" · # "x")) ⦂  𝔹 ⇒ 𝔹 ``
* `` ∅ ⊢ ƛ "f" ⇒ ƛ "x" ⇒ # "f" · (# "f" · # "x")) ⦂  (𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹 ``

Environments are partial maps from identifiers to types, built using `∅`
for the empty map, and `Γ , x ⦂ A` for the map that extends
environment `Γ` by mapping variable `x` to type `A`.

*It's redundant to have two versions of the rules*

*Need text to explain `Γ ∋ x ⦂ A`*

In an informal presentation of the formal semantics,
the rules for typing are written as follows.

    Γ x ≡ A
    ----------- Ax
    Γ ⊢ ` x ⦂ A

    Γ , x ⦂ A ⊢ N ⦂ B
    ------------------------ ⇒-I
    Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

    Γ ⊢ L ⦂ A ⇒ B
    Γ ⊢ M ⦂ A
    -------------- ⇒-E
    Γ ⊢ L · M ⦂ B

    ------------- 𝔹-I₁
    Γ ⊢ true ⦂ 𝔹

    -------------- 𝔹-I₂
    Γ ⊢ false ⦂ 𝔹

    Γ ⊢ L : 𝔹
    Γ ⊢ M ⦂ A
    Γ ⊢ N ⦂ A
    -------------------------- 𝔹-E
    Γ ⊢ if L then M else N ⦂ A

As we will show later, the rules are deterministic, in that
at most one rule applies to every term.

The proof rules come in pairs, with rules to introduce and to
eliminate each connective, labeled `-I` and `-E`, respectively. As we
read the rules from top to bottom, introduction and elimination rules
do what they say on the tin: the first _introduces_ a formula for the
connective, which appears in the conclusion but not in the premises;
while the second _eliminates_ a formula for the connective, which appears in
a premise but not in the conclusion. An introduction rule describes
how to construct a value of the type (abstractions yield functions,
true and false yield booleans), while an elimination rule describes
how to deconstruct a value of the given type (applications use
functions, conditionals use booleans).

Here are the above rules formalised in Agda.

\begin{code}
infix  4  _∋_⦂_
infix  4  _⊢_⦂_
infixl 5  _,_⦂_

data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

data _⊢_⦂_ : Context → Term → Type → Set where

  Ax : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -------------
    → Γ ⊢ # x ⦂ A

  ⇒-I : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      --------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  ⇒-E : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      --------------
    → Γ ⊢ L · M ⦂ B

  𝔹-I₁ : ∀ {Γ}
      -------------
    → Γ ⊢ true ⦂ 𝔹

  𝔹-I₂ : ∀ {Γ}
      --------------
    → Γ ⊢ false ⦂ 𝔹

  𝔹-E : ∀ {Γ L M N A}
    → Γ ⊢ L ⦂ 𝔹
    → Γ ⊢ M ⦂ A
    → Γ ⊢ N ⦂ A
      ---------------------------
    → Γ ⊢ if L then M else N ⦂ A
\end{code}

### Example type derivations

Here are a couple of typing examples.  First, here is how
they would be written in an informal description of the
formal semantics.

Derivation of `not`:

    ------------ Z
    Γ₀ ∋ "x" ⦂ B
    -------------- Ax    -------------- 𝔹-I₂    ------------- 𝔹-I₁
    Γ₀ ⊢ # "x" ⦂ 𝔹       Γ₀ ⊢ false ⦂ 𝔹         Γ₀ ⊢ true ⦂ 𝔹
    ------------------------------------------------------ 𝔹-E
    Γ₀ ⊢ if # "x" then false else true ⦂ 𝔹
    --------------------------------------------------- ⇒-I
    ∅ ⊢ ƛ "x" ⇒ if # "x" then false else true ⦂ 𝔹 ⇒ 𝔹

where `Γ₀ = ∅ , x ⦂ 𝔹`.

Derivation of `two`:

    ∋f                        ∋f                          ∋x
    ------------------- Ax    ------------------- Ax     --------------- Ax
    Γ₂ ⊢ # "f" ⦂ 𝔹 ⇒ 𝔹        Γ₂ ⊢ # "f" ⦂ 𝔹 ⇒ 𝔹         Γ₂ ⊢ # "x" ⦂ 𝔹
    ------------------- Ax    ------------------------------------------ ⇒-E
    Γ₂ ⊢ # "f" ⦂ 𝔹 ⇒ 𝔹        Γ₂ ⊢ # "f" · # "x" ⦂ 𝔹
    --------------------------------------------------  ⇒-E
    Γ₂ ⊢ # "f" · (# "f" · # "x") ⦂ 𝔹
    ---------------------------------------------- ⇒-I
    Γ₁ ⊢ ƛ "x" ⇒ # "f" · (# "f" · # "x") ⦂ 𝔹 ⇒ 𝔹
    ---------------------------------------------------------- ⇒-I
    ∅ ⊢ ƛ "f" ⇒ ƛ "x" ⇒ # "f" · (# "f" · # "x") ⦂ 𝔹 ⇒ 𝔹

Where `∋f` and `∋x` abbreviate the two derivations:


                 ---------------- Z
    "x" ≢ "f"    Γ₁ ∋ "f" ⦂ B ⇒ B
    ----------------------------- S        ------------- Z
    Γ₂ ∋ "f" ⦂ B ⇒ B                       Γ₂ ∋ "x" ⦂ 𝔹

where `Γ₁ = ∅ , f ⦂ 𝔹 ⇒ 𝔹` and `Γ₂ = ∅ , f ⦂ 𝔹 ⇒ 𝔹 , x ⦂ 𝔹`.

Here are the above derivations formalised in Agda.

\begin{code}
⊢not : ∅ ⊢ not ⦂ 𝔹 ⇒ 𝔹
⊢not = ⇒-I (𝔹-E (Ax Z) 𝔹-I₂ 𝔹-I₁)

⊢two : ∅ ⊢ two ⦂ (𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹
⊢two = ⇒-I (⇒-I (⇒-E (Ax ⊢f) (⇒-E (Ax ⊢f) (Ax ⊢x))))
  where

  f≢x : "f" ≢ "x"
  f≢x ()

  ⊢f = S f≢x Z
  ⊢x = Z
\end{code}

#### Interaction with Agda

Construction of a type derivation is best done interactively.
Start with the declaration:

    ⊢not : ∅ ⊢ not ⦂ 𝔹 ⇒ 𝔹
    ⊢not = ?

Typing C-l causes Agda to create a hole and tell us its expected type.

    ⊢not = { }0
    ?0 : ∅ ⊢ not ⦂ 𝔹 ⇒ 𝔹

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `not` in a `λ`, which is typed using `⇒-I`. The
`⇒-I` rule in turn takes one argument, which Agda leaves as a hole.

    ⊢not = ⇒-I { }0
    ?0 : ∅ , x ⦂ 𝔹 ⊢ if ` x then false else true ⦂ 𝔹

Again we fill in the hole by typing C-c C-r. Agda observes that the
outermost term is now `if_then_else_`, which is typed using `𝔹-E`. The
`𝔹-E` rule in turn takes three arguments, which Agda leaves as holes.

    ⊢not = ⇒-I (𝔹-E { }0 { }1 { }2)
    ?0 : ∅ , x ⦂ 𝔹 ⊢ ` x ⦂
    ?1 : ∅ , x ⦂ 𝔹 ⊢ false ⦂ 𝔹
    ?2 : ∅ , x ⦂ 𝔹 ⊢ true ⦂ 𝔹

Again we fill in the three holes by typing C-c C-r in each. Agda observes
that `` ` x ``, `false`, and `true` are typed using `Ax`, `𝔹-I₂`, and
`𝔹-I₁` respectively. The `Ax` rule in turn takes an argument, to show
that `(∅ , x ⦂ 𝔹) x = just 𝔹`, which can in turn be specified with a
hole. After filling in all holes, the term is as above.

The entire process can be automated using Agsy, invoked with C-c C-a.

### Injective

Note that `Γ ∋ x ⦂ A` is functional.
\begin{code}
∋-functional : ∀ {Γ w A B} → Γ ∋ w ⦂ A → Γ ∋ w ⦂ B → A ≡ B
∋-functional Z        Z          =  refl
∋-functional Z        (S w≢ _)   =  ⊥-elim (w≢ refl)
∋-functional (S w≢ _) Z          =  ⊥-elim (w≢ refl)
∋-functional (S _ ∋w) (S _ ∋w′)  =  ∋-functional ∋w ∋w′
\end{code}

The relation `Γ ⊢ M ⦂ A` is not functional. For example, in any `Γ`
the term `ƛ "x" ⇒ "x"` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term `` true ·
false ``.  In other words, no type `A` is the type of this term.  It
cannot be typed, because doing so requires that the first term in the
application is both a boolean and a function.

\begin{code}
ex₁ : ∀ {A} → ¬ (∅ ⊢ true · false ⦂ A)
ex₁ (⇒-E () _)
\end{code}

As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ # "x" · # "x" `` It cannot be typed, because
doing so requires some types `A` and `B` such that `A ⇒ B ≡ A`.

\begin{code}
contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
contradiction ()

ex₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ # "x" · # "x" ⦂ A)
ex₂ (⇒-I (⇒-E (Ax ∋x) (Ax ∋x′)))  =  contradiction (∋-functional ∋x ∋x′)
\end{code}


#### Quiz

For each of the following, given a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , y ⦂ A ⊢ λ[ x ⦂ 𝔹 ] ` x ⦂ 𝔹 ⇒ 𝔹 ``
2. `` ∅ ⊢ λ[ y ⦂ 𝔹 ⇒ 𝔹 ] λ[ x ⦂ 𝔹 ] ` y · ` x ⦂ A ``
3. `` ∅ ⊢ λ[ y ⦂ 𝔹 ⇒ 𝔹 ] λ[ x ⦂ 𝔹 ] ` x · ` y ⦂ A ``
4. `` ∅ , x ⦂ A ⊢ λ[ y : 𝔹 ⇒ 𝔹 ] `y · `x : A ``

For each of the following, give type `A`, `B`, `C`, and `D` for which it is derivable,
or explain why there are no such types.

1. `` ∅ ⊢ λ[ y ⦂ 𝔹 ⇒ 𝔹 ⇒ 𝔹 ] λ[ x ⦂ 𝔹 ] ` y · ` x ⦂ A ``
2. `` ∅ , x ⦂ A ⊢ x · x ⦂ B ``
3. `` ∅ , x ⦂ A , y ⦂ B ⊢ λ[ z ⦂ C ] ` x · (` y · ` z) ⦂ D ``



## Unicode

This chapter uses the following unicode

    ⇒    U+21D2: RIGHTWARDS DOUBLE ARROW (\=>)
    ƛ    U+019B: LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    ⦂    U+2982: Z NOTATION TYPE COLON (\:)
    ·    U+00B7: MIDDLE DOT (\cdot)
    😇   U+1F607: SMILING FACE WITH HALO
    😈   U+1F608: SMILING FACE WITH HORNS
    ′    U+2032: PRIME (\')
    ⟹  U+27F9: LONG RIGHTWARDS DOUBLE ARROW (\r6)
    ξ    U+03BE: GREEK SMALL LETTER XI (\Gx or \xi)
    β    U+03B2: GREEK SMALL LETTER BETA (\Gb or \beta)

Note that ′ (U+2032: PRIME) is not the same as ' (U+0027: APOSTROPHE).
