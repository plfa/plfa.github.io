---
title     : "Lambda: Introduction to Lambda Calculus"
layout    : page
permalink : /Lambda/
---

\begin{code}
module plta.Lambda where
\end{code}

[This chapter was originally based on Chapter _Stlc_
of _Software Foundations_ (_Programming Language Foundations_).
It has now been updated, but if you spot any plagiarism
please let me know. -- P]

The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It captures the key concept of
_functional abstraction_, which appears in pretty much every programming
language, in the form of either functions, procedures, or methods.
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations.
We will instead echo Plotkin's _Programmable Computable
Functions_ (PCF), and add operations on natural numbers and
recursive function definitions.

This chapter formalises the simply-typed lambda calculus, giving its
syntax, small-step semantics, and typing rules.  The next chapter
[PandP]({{ site.baseurl }}{% link out/plta/PandP.md %})
proves its main properties, including
progress and preservation.  Following chapters will look at a number
of variants of lambda calculus.

Be aware that the approach we take here is _not_ our recommended
approach to formalisation.  Using De Bruijn indices and
inherently-typed terms, as we will do in
Chapter [DeBruijn]({{ site.baseurl }}{% link out/plta/DeBruijn.md %}),
leads to a more compact formulation.  Nonetheless, we begin with named
variables, partly because such terms are easier to read and partly
because the development is more traditional.

The development in this chapter was inspired by the corresponding
development in Chapter _Stlc_ of _Software Foundations_ 
(_Programming Language Foundations_).  We differ by
representing contexts explicitly (as lists pairing identifiers with
types) rather than as partial maps (which take identifiers to types),
which will corresponds better to our subsequent development of DeBruin
notation. We also differ by taking natural numbers as the base type
rather than booleans, allowing more sophisticated examples. In
particular, we will be able to show (twice!) that two plus two is
four.

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)
\end{code}

## Syntax of terms

Terms have seven constructs. Three are for the core lambda calculus:

  * Variables `⌊ x ⌋`
  * Abstractions `ƛ x ⇒ N`
  * Applications `L · M`

Three are for the naturals:

  * Zero `` `zero ``
  * Successor `` `suc ``
  * Case `` `case L [zero⇒ M |suc x ⇒ N ] ``

And one is for recursion:

  * Fixpoint `μ x ⇒ M`

Abstraction is also called _lambda abstraction_, and is the construct
from which the calculus takes its name.

With the exception of variables and fixpoints, each term
form either constructs a value of a given type (abstractions yield functions,
zero and successor yield booleans) or deconstructs it (applications use functions,
case terms use naturals). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in BNF.

    L, M, N  ::=
      ⌊ x ⌋  |  ƛ x ⇒ N  |  L · M  |
      `zero  |  `suc M  |  `case L [zero⇒ M |suc x ⇒ N]  |
      μ x ⇒ M

And here it is formalised in Agda.
\begin{code}
Id : Set
Id = String

infix  6  ƛ_⇒_
infix  6  μ_⇒_
infixl 7  _·_
infix  8  `suc_

data Term : Set where
  ⌊_⌋                      :  Id → Term
  ƛ_⇒_                     :  Id → Term → Term
  _·_                      :  Term → Term → Term
  `zero                    :  Term
  `suc_                    :  Term → Term
  `case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                     :  Id → Term → Term
\end{code}
We represent identifiers by strings.  We choose precedence so that
lambda abstraction and fixpoint bind least tightly, then application,
then successor, and tightest of all is the constructor for variables.
Case expressions are self-bracketing.


### Example terms

Here are some example terms: the natural number two,
a function that adds naturals,
and a term that computes two plus two.
\begin{code}
two : Term
two = `suc `suc `zero

plus : Term
plus =  μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         `case ⌊ "m" ⌋
           [zero⇒ ⌊ "n" ⌋
           |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋) ]

four : Term
four = plus · two · two
\end{code}
The recursive definition of addition is similar to our original
definition of `_+_` for naturals, as given in
Chapter [Naturals]({{ site.baseurl }}{% link out/plta/Naturals.md %}#plus).
Later we will confirm that two plus two is four, in other words that
the term

    plus · two · two

reduces to `` `suc `suc `suc `suc `zero ``.

As a second example, we use higher-order functions to represent
natural numbers.  In particular, the number _n_ is represented by a
function that accepts two arguments and applies the first _n_ times to the
second.  This is called the _Church representation_ of the
naturals.  Here are some example terms: the Church numeral two, a
function that adds Church numerals, a function to compute successor,
and a term that computes two plus two.
\begin{code}
twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ⌊ "m" ⌋ · ⌊ "s" ⌋ · (⌊ "n" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋)

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (⌊ "n" ⌋)

fourᶜ : Term
fourᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
\end{code}
The Church numeral for two takes two arguments `s` and `z`
and applies `s` twice to `z`.
Addition takes two numerals `m` and `n`, a
function `s` and an argument `z`, and it uses `m` to apply `s` to the
result of using `n` to apply `s` to `z`; hence `s` is applied `m` plus
`n` times to `z`, yielding the Church numeral for the sum of `m` and
`n`.  For convenience, we define a function that computes successor;
to convert a Church numeral to the corresponding natural, we apply
it to this function and the natural number zero.
Again, later we will confirm that two plus two is four,
in other words that the term

    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

reduces to `` `suc `suc `suc `suc `zero ``.


#### Exercise (`mul`)

Write out the defintion of a lambda term that multiplies
two natural numbers.


### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `⌊ x ⌋`
for a term that is a variable. Agda requires we distinguish.

Similarly, informal presentation often use the same notation for
function types, lambda abstraction, and function application in both
the object language (the language one is describing) and the
meta-language (the language in which the description is written),
trusting readers can use context to distinguish the two.  Agda is is
not quite so forgiving, so here we use `ƛ x ⇒ N` and `L · M` for the
object language, as compared to `λ x → N` and `L M` in our
meta-language, Agda.


### Bound and free variables

In an abstraction `ƛ x ⇒ N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  A central feature
of lambda calculus is that consistent renaming of bound variables
leaves the meaning of a term unchanged.  Thus the five terms

* `` ƛ "s" ⇒ ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋) ``
* `` ƛ "f" ⇒ ƛ "x" ⇒ ⌊ "f" ⌋ · (⌊ "f" ⌋ · ⌊ "x" ⌋) ``
* `` ƛ "sam" ⇒ ƛ "zelda" ⇒ ⌊ "sam" ⌋ · (⌊ "sam" ⌋ · ⌊ "zelda" ⌋) ``
* `` ƛ "z" ⇒ ƛ "s" ⇒ ⌊ "z" ⌋ · (⌊ "z" ⌋ · ⌊ "s" ⌋) ``
* `` ƛ "😇" ⇒ ƛ "😈" ⇒ # "😇" · (# "😇" · # "😈" ) ``

are all considered equivalent.  Following the convention introduced
by Haskell Curry, who used the Greek letter `α` (_alpha_) to label such rules,
this equivalence relation is called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms.

* `` ƛ "s" ⇒ ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋) ``
  has both `s` and `z` as bound variables.

* `` ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋) ``
  has `s` bound and `z` free.

* `` ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋) ``
  has both `s` and `z` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.

Different occurrences of a variable may be bound and free.
In the term

    (ƛ "x" ⇒ ⌊ "x" ⌋) · ⌊ "x" ⌋

the inner occurrence of `x` is bound while the outer occurrence is free.
By alpha renaming, the term above is equivalent to

    (ƛ "y" ⇒ ⌊ "y" ⌋) · ⌊ "x" ⌋

in which `y` is bound and `x` is free.  A common convention, called the
_Barendregt convention_, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.

Case and recursion also introduce bound variables, which are also subject
to alpha renaming. In the term

    μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
      `case ⌊ "m" ⌋
        [zero⇒ ⌊ "n" ⌋
        |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋) ]

notice that there are two binding occurrences of `m`, one in the first
line and one in the last line.  It is equivalent to the following term,

    μ "plus" ⇒ ƛ "x" ⇒ ƛ "y" ⇒
      `case ⌊ "x" ⌋
        [zero⇒ ⌊ "y" ⌋
        |suc "x′" ⇒ `suc (⌊ "plus" ⌋ · ⌊ "x′" ⌋ · ⌊ "y" ⌋) ]

where the two binding occurrences corresponding to `m` now have distinct
names, `x` and `x′`.


## Values

<!--
We only consider reduction of _closed_ terms,
those that contain no free variables.  We consider
a precise definition of free variables in Chapter
[PandP]({{ site.baseurl }}{% link out/plta/PandP.md %}).
-->

A _value_ is a term that corresponds to an answer.
Thus, `` `suc `suc `suc `suc `zero` `` is a value,
while `` plus · two · two `` is not.
Following convention, we treat all function abstractions
as values; thus, `` plus `` by itself is considered a value.

The predicate `Value M` holds if term `M` is a value.

\begin{code}
data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)
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
We consider this approach in
Chapter [Untyped]({{ site.baseurl }}{% link out/plta/Untyped.md %}).


## Substitution

The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have

      (ƛ "s" ⇒ ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)) · sucᶜ · `zero
    ⟶
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · "z")) · `zero
    ⟶
      sucᶜ · (sucᶜ · `zero)

where we substitute `sucᶜ` for `` ⌊ "s" ⌋ `` and `` `zero `` for `` ⌊ "z" ⌋ ``
in the body of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
"substitute term `V` for free occurrences of variable `x` in term `N`",
or, more compactly, "substitute `V` for `x` in `N`".
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since in fact we
usually substitute values.

Here are some examples:

* `` (sucᶜ · (sucᶜ · ⌊ "z" ⌋)) [ "z" := `zero ] `` yields
  `` sucᶜ · (sucᶜ · `zero) ``
* `` (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)) [ "s" := sucᶜ ] `` yields
     ƛ "z" ⇒ sucᶜ · (sucᶜ · ⌊ "z" ⌋) ``
* `` (ƛ "x" ⇒ ⌊ "y" ⌋) [ "y" := `zero ] `` yields `` ƛ "x" ⇒ `zero ``
* `` (ƛ "x" ⇒ ⌊ "x" ⌋) [ "x" := `zero ] `` yields `` ƛ "x" ⇒ ⌊ "x" ⌋ ``
* `` (ƛ "y" ⇒ ⌊ "y" ⌋) [ "x" := `zero ] `` yields `` ƛ "x" ⇒ ⌊ "x" ⌋ ``

In the last but one example, substituting `` `zero `` for `x` in
`` ƛ "x" ⇒ ⌊ "x" ⌋ `` does _not_ yield `` ƛ "x" ⇒ `zero ``,
since `x` is bound in the lambda abstraction.
The choice of bound names is irrelevant: both
`` ƛ "x" ⇒ ⌊ "x" ⌋ `` and `` ƛ "y" ⇒ ⌊ "y" ⌋ `` stand for the
identity function.  One way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they just happen to have the same name.

We will give a definition of substitution that is only valid
when term substituted for the variable is closed. This is because
substitution by terms that are _not_ closed may require renaming
of bound variables. For example:

* `` (ƛ "x" ⇒ ⌊ "x" ⌋ · ⌊ "y" ⌋) [ "y" := ⌊ "x" ⌋ · ⌊ "y" ⌋ ] `` should not yield
  `` ƛ "x" ⇒ ⌊ "x" ⌋ · (⌊ "x" ⌋ · ⌊ "y" ⌋) ``

Instead, we should rename the variables to avoid capture.

* `` (ƛ "x" ⇒ ⌊ "x" ⌋ · ⌊ "y" ⌋) [ "y" := ⌊ "x" ⌋ · ⌊ "y" ⌋ ] `` should yield
  `` ƛ "z" ⇒ ⌊ "z" ⌋ · (⌊ "x" ⌋ · ⌊ "y" ⌋) ``

Formal definition of substitution with suitable renaming is considerably
more complex, so we avoid it by restricting to substitution by closed terms,
which will be adequate for our purposes.

Here is the formal definition of substitution by closed terms in Agda.

\begin{code}
infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
⌊ x ⌋ [ y := V ] with x ≟ y
... | yes _  =  V
... | no  _  =  ⌊ x ⌋
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _  =  ƛ x ⇒ N
... | no  _  =  ƛ x ⇒ (N [ y := V ])
(L · M) [ y := V ]   =  (L [ y := V ]) · (M [ y := V ])
(`zero) [ y := V ]   =  `zero
(`suc M) [ y := V ]  =  `suc (M [ y := V ])
(`case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _  =  `case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _  =  `case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _  =  μ x ⇒ N
... | no  _  =  μ x ⇒ (N [ y := V ])
\end{code}

Let's unpack the first three cases.

* For variables, we compare `y`, the substituted variable,
with `x`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x` unchanged.

* For abstractions, we compare `w`, the variable we are substituting for,
with `x`, the variable bound in the abstraction. If they are the same,
we yield the abstraction unchanged, otherwise we subsititute inside the body.

* For application, we recursively substitute in the function
and the argument.

Case expressions and recursion also have bound variables that are
treated similarly to those in lambda abstractions.  Otherwise we
simply push substitution recursively into the subterms.


### Examples

Here is confirmation that the examples above are correct.

\begin{code}
_ : (sucᶜ · sucᶜ · ⌊ "z" ⌋) [ "z" := `zero ] ≡  sucᶜ · sucᶜ · `zero
_ = refl

_ : (ƛ "z" ⇒ ⌊ "s" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋) [ "s" := sucᶜ ] ≡  ƛ "z" ⇒ sucᶜ · sucᶜ · ⌊ "z" ⌋
_ = refl

_ : (ƛ "x" ⇒ ⌊ "y" ⌋) [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ⌊ "x" ⌋) [ "x" := `zero ] ≡ ƛ "x" ⇒ ⌊ "x" ⌋
_ = refl

_ : (ƛ "y" ⇒ ⌊ "y" ⌋) [ "x" := `zero ] ≡ ƛ "y" ⇒ ⌊ "y" ⌋
_ = refl
\end{code}

#### Quiz

What is the result of the following substitution?

    (ƛ "y" ⇒ ⌊ "x" ⌋ · (ƛ "x" ⇒ ⌊ "x" ⌋)) [ "x" := `zero ]

1. `` (ƛ "y" ⇒ ⌊ "x" ⌋ · (ƛ "x" ⇒ ⌊ "x" ⌋)) ``
2. `` (ƛ "y" ⇒ ⌊ "x" ⌋ · (ƛ "x" ⇒ `zero)) ``
3. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ⌊ "x" ⌋)) ``
4. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ `zero)) ``


## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.

In an informal presentation of the operational semantics,
the rules for reduction of applications are written as follows.

    L ⟶ L′
    --------------- ξ·₁
    L · M ⟶ L′ · M

    M ⟶ M′
    --------------- ξ·₂
    V · M ⟶ V · M′

    --------------------------------- βλ·
    (ƛ x ⇒ N) · V ⟶ N [ x := V ] 

The Agda version of the rules below will be similar, except that universal
quantifications are made explicit, and so are the predicates that indicate
which terms are values.

The rules break into two sorts. Compatibility rules direct us to
reduce some part of a term.  We give them names starting with the
Greek letter `ξ` (_xi_).  Once a term is sufficiently reduced, it will
consist of a constructor and a deconstructor, in our case `λ` and `·`,
which reduces directly.  We give them names starting with the Greek
letter `β` (_beta_) and such rules are traditionally called _beta rules_.

The rules are deterministic, in that at most one rule applies to every
term.  We will show in the next chapter that for every well-typed term
either a reduction applies or it is a value.

For numbers, zero does not reduce and successor reduces the subterm.
A case expression reduces its argument to a number, and then chooses
the zero or successor branch as appropriate.  A fixpoint replaces
the bound variable by the entire fixpoint term.

Here are the rules formalised in Agda.

\begin{code}
infix 4 _⟶_

data _⟶_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L ⟶ L′
      -----------------
    → L · M ⟶ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M ⟶ M′
      -----------------
    → V · M ⟶ V · M′

  β-ƛ· : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V ⟶ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M ⟶ M′
      ------------------
    → `suc M ⟶ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L ⟶ L′
      -----------------------------------------------------------------
    → `case L [zero⇒ M |suc x ⇒ N ] ⟶ `case L′ [zero⇒ M |suc x ⇒ N ]

  β-case-zero : ∀ {x M N}
      ----------------------------------------
    → `case `zero [zero⇒ M |suc x ⇒ N ] ⟶ M

  β-case-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → `case `suc V [zero⇒ M |suc x ⇒ N ] ⟶ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M ⟶ M [ x := μ x ⇒ M ]
\end{code}


#### Quiz

What does the following term step to?

    (ƛ "x" ⇒ ⌊ "x" ⌋) · (ƛ "x" ⇒ ⌊ "x" ⌋)  ⟶  ???

1.  `` (ƛ "x" ⇒ ⌊ "x" ⌋) ``
2.  `` (ƛ "x" ⇒ ⌊ "x" ⌋) · (ƛ "x" ⇒ ⌊ "x" ⌋) ``
3.  `` (ƛ "x" ⇒ ⌊ "x" ⌋) · (ƛ "x" ⇒ ⌊ "x" ⌋) · (ƛ "x" ⇒ ⌊ "x" ⌋) ``

What does the following term step to?

    (ƛ "x" ⇒ ⌊ "x" ⌋) · (ƛ "x" ⇒ ⌊ "x" ⌋) · (ƛ "x" ⇒ ⌊ "x" ⌋)  ⟶  ???

1.  `` (ƛ "x" ⇒ ⌊ "x" ⌋) ``
2.  `` (ƛ "x" ⇒ ⌊ "x" ⌋) · (ƛ "x" ⇒ ⌊ "x" ⌋) ``
3.  `` (ƛ "x" ⇒ ⌊ "x" ⌋) · (ƛ "x" ⇒ ⌊ "x" ⌋) · (ƛ "x" ⇒ ⌊ "x" ⌋) ``

What does the following term step to?  (Where `two` and `sucᶜ` are as defined above.)

    two · sucᶜ · `zero  ⟶  ???

1.  `` sucᶜ · (sucᶜ · `zero) ``
2.  `` (ƛ "z" ⇒ sucᶜ · (sucᶜ · ⌊ "z" ⌋)) · `zero ``
3.  `` `zero ``


## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `⟶*` of the step function `⟶`.

The reflexive and transitive closure `⟶*` of an arbitrary relation `⟶`
is the smallest relation that includes `⟶` and is also reflexive
and transitive.  We could define this directly, as follows.
\begin{code}
module Closure (A : Set) (_⟶_ : A → A → Set) where

  data _⟶*_ : A → A → Set where

    refl : ∀ {M}
        --------
      → M ⟶* M

    trans : ∀ {L M N}
      → L ⟶* M
      → M ⟶* N
        --------
      → L ⟶* N

    inc : ∀ {M N}
      → M ⟶ N
        --------
      → M ⟶* N
\end{code}
Here we use a module to define the reflexive and transitive
closure of an arbitrary relation.
The three clauses specify that `⟶*` is reflexive and transitive,
and that `⟶` implies `⟶*`.

However, it will prove more convenient to define the transitive
closure as a sequence of zero or more steps of the underlying
relation, along lines similar to that for reasoning about
chains of equalities
Chapter [Equality]({{ site.baseurl }}{% link out/plta/Equality.md %}).
\begin{code}
module Chain (A : Set) (_⟶_ : A → A → Set) where

  infix  2 _⟶*_
  infix  1 begin_
  infixr 2 _⟶⟨_⟩_
  infix  3 _∎

  data _⟶*_ : A → A → Set where
    _∎ : ∀ M
        ---------
      → M ⟶* M

    _⟶⟨_⟩_ : ∀ L {M N}
      → L ⟶ M
      → M ⟶* N
        ---------
      → L ⟶* N

  begin_ : ∀ {M N} → (M ⟶* N) → (M ⟶* N)
  begin M⟶*N = M⟶*N
\end{code}
We can read this as follows.

* From term `M`, we can take no steps,
  giving a step of type `M ⟶* M`.
  It is written `M ∎`.

* From term `L` we can take a single of type `L ⟶ M`
  followed by zero or more steps of type `M ⟶* N`,
  giving a step of type `L ⟶* N`,
  It is written `L ⟨ L⟶M ⟩ M⟶*N`,
  where `L⟶M` and `M⟶*N` are steps of the appropriate type.

The notation is chosen to allow us to lay
out example reductions in an appealing way,
as we will see in the next section.

We then instantiate the second module to our specific notion
of reduction step.
\begin{code}
open Chain (Term) (_⟶_)
\end{code}


#### Exercise (`closure-equivalent`)

Show that the two notions of reflexive and transitive closure
above are equivalent.


## Examples

Here is a sample reduction demonstrating that two plus two is four.
\begin{code}
_ : four ⟶* `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  ⟶⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (plus · ⌊ "m" ⌋ · ⌊ "n" ⌋) ])
        · two · two
  ⟶⟨ ξ-·₁ (β-ƛ· (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
      `case two [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (plus · ⌊ "m" ⌋ · ⌊ "n" ⌋) ])
         · two
  ⟶⟨ β-ƛ· (V-suc (V-suc V-zero)) ⟩
    `case two [zero⇒ two |suc "m" ⇒ `suc (plus · ⌊ "m" ⌋ · two) ]
  ⟶⟨ β-case-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  ⟶⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (plus · ⌊ "m" ⌋ · ⌊ "n" ⌋) ])
        · `suc `zero · two)
  ⟶⟨ ξ-suc (ξ-·₁ (β-ƛ· (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
      `case `suc `zero [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (plus · ⌊ "m" ⌋ · ⌊ "n" ⌋) ])
        · two)
  ⟶⟨ ξ-suc (β-ƛ· (V-suc (V-suc V-zero))) ⟩
    `suc (`case `suc `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ⌊ "m" ⌋ · two) ])
  ⟶⟨ ξ-suc (β-case-suc V-zero) ⟩
    `suc `suc (plus · `zero · two)
  ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (plus · ⌊ "m" ⌋ · ⌊ "n" ⌋) ])
        · `zero · two)
  ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ· V-zero))) ⟩
    `suc `suc ((ƛ "n" ⇒
      `case `zero [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (plus · ⌊ "m" ⌋ · ⌊ "n" ⌋) ])
        · two)
  ⟶⟨ ξ-suc (ξ-suc (β-ƛ· (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (`case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ⌊ "m" ⌋ · two) ])
  ⟶⟨ ξ-suc (ξ-suc β-case-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎
\end{code}

And here is a similar sample reduction for Church numerals.
\begin{code}
_ : fourᶜ ⟶* `suc `suc `suc `suc `zero
_ =
  begin
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ⌊ "m" ⌋ · ⌊ "s" ⌋ · (⌊ "n" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋))
      · twoᶜ · twoᶜ · sucᶜ · `zero
  ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ· V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ⌊ "s" ⌋ · (⌊ "n" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋))
      · twoᶜ · sucᶜ · `zero
  ⟶⟨ ξ-·₁ (ξ-·₁ (β-ƛ· V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ⌊ "s" ⌋ · (twoᶜ · ⌊ "s" ⌋ · ⌊ "z" ⌋)) · sucᶜ · `zero
  ⟶⟨ ξ-·₁ (β-ƛ· V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ⌊ "z" ⌋)) · `zero
  ⟶⟨ β-ƛ· V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  ⟶⟨ ξ-·₁ (β-ƛ· V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ⌊ "z" ⌋)) · (twoᶜ · sucᶜ · `zero)
  ⟶⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ· V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ⌊ "z" ⌋)) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ⌊ "z" ⌋)) · `zero)
  ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ⌊ "z" ⌋)) · (sucᶜ · (sucᶜ · `zero))
  ⟶⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ· V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ⌊ "z" ⌋)) · (sucᶜ · (`suc `zero))
  ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ⌊ "z" ⌋)) · (`suc `suc `zero)
  ⟶⟨ β-ƛ· (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc `suc `zero)
  ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  ⟶⟨ β-ƛ· (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎
\end{code}

In the next chapter, we will see how to compute such reduction sequences.


#### Exercise (`mul-ex`)

Using the term `mul` you defined earlier, write out the reduction
sequence demonstrating that two times two is four.


## Syntax of types

We have just two types.

  * Functions, `A ⇒ B`
  * Naturals, `` `ℕ ``

As before, to avoid overlap we use variants of the names used by Agda.

Here is the syntax of types in BNF.

    A, B, C  ::=  A ⇒ B | `ℕ

And here it is formalised in Agda.

\begin{code}
infixr 6 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type
\end{code}

### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus,

* ``(`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ`` stands for ``((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ))``
* `plus · two · two` stands for `(plus · two) · two`.

### Quiz

* What is the type of the following term?

    ƛ "s" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋  · `zero)

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.

* What is the type of the following term?

    (ƛ "s" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋  · `zero)) · sucᵐ

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.


## Typing

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

A _context_ associates variables with types.  We let `Γ` and `Δ` range
over contexts.  We write `∅` for the empty context, and `Γ , x ⦂ A`
for the context that extends `Γ` by mapping variable `x` to type `A`.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ``

is the context that associates variable ` "s" ` with type `` `ℕ ⇒ `ℕ ``,
and variable ` "z" ` with type `` `ℕ ``.

Contexts are formalised as follows.

\begin{code}
infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context
\end{code}

We have two forms of _judgement_.  The first is written

    Γ ∋ x ⦂ A

and indicates in context `Γ` that variable `x` has type `A`.
It is called _lookup_.
For example

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

give us the types associated with variables ` "z" ` and ` "s" `, respectively.
The symbol `∋` (pronounced "ni", for "in" backwards) is chosen because
checking that `Γ ∋ x ⦂ A` is anologous to checking whether `x ⦂ A` appears
in a list corresponding to `Γ`.

If two variables in a context have the same name, then lookup
should return the most recently bound variable, which _shadows_
the other variables.  For example,

* `` ∅ , "x" : `ℕ ⇒ `ℕ , "x" : `ℕ ∋ "x" ⦂ `ℕ

Here `` "x" ⦂ `ℕ ⇒ `ℕ `` is shadowed by `` "x" ⦂ `ℕ ``.

Lookup is formalised as follows.
\begin{code}
infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A
\end{code}

The constructors `Z` and `S` correspond roughly to the constructors
`here` and `there` for the element-of relation `_∈_` on lists.
Constructor `S` takes an additional paramemer, which ensures that
when we look up a variable that it is not _shadowed_ by another
variable with the same name earlier in the list.

The second judgement is written

    Γ ⊢ M ⦂ A

and indicates in context `Γ` that term `M` has type `A`.
Context `Γ` provides types for all the free variables in `M`.
For example

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋) ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)) ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)) ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

Typing is formalised as follows.
\begin{code}
infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  Ax : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -------------
    → Γ ⊢ ⌊ x ⌋ ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A
\end{code}

Each type rule is named after the constructor for the
corresponding term.

Most of the rules have a second name,
derived from a convention in logic, whereby the rule is
named after the type connective that it concerns;
rules to introduce and to
eliminate each connective are labeled `-I` and `-E`, respectively. As we
read the rules from top to bottom, introduction and elimination rules
do what they say on the tin: the first _introduces_ a formula for the
connective, which appears in the conclusion but not in the premises;
while the second _eliminates_ a formula for the connective, which appears in
a premise but not in the conclusion. An introduction rule describes
how to construct a value of the type (abstractions yield functions,
`` `suc `` and `` `zero `` yield naturals), while an elimination rule describes
how to deconstruct a value of the given type (applications use
functions, case expressions use naturals).

The rules are deterministic, in that at most one rule applies to every term.


### Checking inequality and postulating the impossible

The following function makes it convenient to assert an inequality.
\begin{code}
_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y  with x ≟ y
...       | no  x≢y  =  x≢y
...       | yes _    =  ⊥-elim impossible
  where postulate impossible : ⊥
\end{code}
Here `_≟_` is the function that tests two identifiers for equality.
We intend to apply the function only when the
two arguments are indeed unequal, and indicate that the second
case should never arise by postulating a term `impossible` of
with the empty type `⊥`.  If we use ^C ^N to normalise the term

    "a" ≠ "a"

Agda will return an answer warning us that the impossible has occurred:

    ⊥-elim (.plta.Lambda.impossible "a" "a" refl)

While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.


### Example type derivations

Type derivations correspond to trees. In informal notation, here
is a type derivation for the Church numberal two:

    ∋s                        ∋s                          ∋z
    ------------------- ⌊_⌋   ------------------- ⌊_⌋    --------------- ⌊_⌋
    Γ₂ ⊢ ⌊ "s" ⌋ ⦂ A ⇒ A        Γ₂ ⊢ ⌊ "s" ⌋ ⦂ A ⇒ A         Γ₂ ⊢ ⌊ "z" ⌋ ⦂ A
    ------------------- ⌊_⌋   ------------------------------------------ _·_
    Γ₂ ⊢ ⌊ "s" ⌋ ⦂ A ⇒ A        Γ₂ ⊢ ⌊ "s" ⌋ · ⌊ "z" ⌋ ⦂ A
    -------------------------------------------------- _·_
    Γ₂ ⊢ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋) ⦂ A
    ---------------------------------------------- ⊢ƛ
    Γ₁ ⊢ ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋) ⦂ A ⇒ A
    ---------------------------------------------------------- ⊢ƛ
    ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋) ⦂ A ⇒ A

where `∋s` and `∋z` abbreviate the two derivations:

                 ---------------- Z
    "s" ≢ "z"    Γ₁ ∋ "s" ⦂ A ⇒ A
    ----------------------------- S        ------------- Z
    Γ₂ ∋ "s" ⦂ A ⇒ A                       Γ₂ ∋ "z" ⦂ A

and where `Γ₁ = ∅ , s ⦂ A ⇒ A` and `Γ₂ = ∅ , s ⦂ A ⇒ A , z ⦂ A`.

Here is the above typing derivation formalised in Agda.
\begin{code}
Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {A} → ∅ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (Ax ∋s · (Ax ∋s · Ax ∋z)))
  where

  ∋s = S ("s" ≠ "z") Z
  ∋z = Z
\end{code}

Here are the typings corresponding to our first example.
\begin{code}
⊢two : ∅ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∅ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (Ax ∋m) (Ax ∋n)
         (⊢suc (Ax ∋+ · Ax ∋m′ · Ax ∋n′)))))
  where
  ∋+  = (S ("+" ≠ "m") (S ("+" ≠ "n") (S ("+" ≠ "m") Z)))
  ∋m  = (S ("m" ≠ "n") Z)
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = (S ("n" ≠ "m") Z)

⊢four : ∅ ⊢ four ⦂ `ℕ
⊢four = ⊢plus · ⊢two · ⊢two
\end{code}
The two occcurrences of variable `"n"` in the original term appear
in different contexts, and correspond here to the two different
lookup judgements, `∋n` and `∋n′`.  The first looks up `"n"` in
a context that ends with the binding for "n", while the second looks
it up in a context extended by the binding for "m" in the second
branch of the case expression.

Here are typings for the remainder of the Church example.
\begin{code}
⊢plusᶜ : ∀ {A} → ∅ ⊢ plusᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (Ax ∋m · Ax ∋s · (Ax ∋n · Ax ∋s · Ax ∋z)))))
  where
  ∋m = S ("m" ≠ "z") (S ("m" ≠ "s") (S ("m" ≠ "n") Z))
  ∋n = S ("n" ≠ "z") (S ("n" ≠ "s") Z)
  ∋s = S ("s" ≠ "z") Z
  ∋z = Z

⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (Ax ∋n))
  where
  ∋n = Z

⊢fourᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ⦂ `ℕ
⊢fourᶜ = ⊢plusᶜ · ⊢twoᶜ · ⊢twoᶜ · ⊢sucᶜ · ⊢zero
\end{code}


### Interaction with Agda

Construction of a type derivation may be done interactively.
Start with the declaration:

    ⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
    ⊢sucᶜ = ?

Typing C-l causes Agda to create a hole and tell us its expected type.

    ⊢sucᶜ = { }0
    ?0 : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `sucᶜ` in `⊢ƛ`, which is typed using `ƛ`. The
`ƛ` rule in turn takes one argument, which Agda leaves as a hole.

    ⊢sucᶜ = ⊢ƛ { }1
    ?1 : ∅ , "n" ⦂ `ℕ ⊢ `suc ⌊ "n" ⌋ ⦂ `ℕ

We can fill in the hole by type C-c C-r again.

    ⊢sucᶜ = ⊢ƛ (⊢suc { }2)
    ?2 : ∅ , "n" ⦂ `ℕ ⊢ ⌊ "n" ⌋ ⦂ `ℕ

And again.

    ⊢suc′ = ⊢ƛ (⊢suc (Ax { }3))
    ?3 : ∅ , "n" ⦂ `ℕ ∋ "n" ⦂ `ℕ

A further attempt with C-c C-r yields the message:

    Don't know which constructor to introduce of Z or S

We can fill in `Z` by hand. If we type C-c C-space, Agda will confirm we are done.

    ⊢suc′ = ⊢ƛ (⊢suc (Ax Z))

The entire process can be automated using Agsy, invoked with C-c C-a.

Chapter [Inference]({{ site.baseurl }}{% link out/plta/DeBruijn.md %})
will show how to use Agda to compute type derivations directly.


### Lookup is injective

The lookup relation `Γ ∋ x ⦂ A` is injective, in that for each `Γ` and `x`
there is at most one `A` such that the judgement holds.
\begin{code}
∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z        Z          =  refl
∋-injective Z        (S x≢ _)   =  ⊥-elim (x≢ refl)
∋-injective (S x≢ _) Z          =  ⊥-elim (x≢ refl)
∋-injective (S _ ∋x) (S _ ∋x′)  =  ∋-injective ∋x ∋x′
\end{code}

The typing relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `ƛ "x" ⇒ "x"` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term `` `zero ·
`suc `zero ``.  In other words, no type `A` is the type of this term.  It
cannot be typed, because doing so requires that the first term in the
application is both a natural and a function.

\begin{code}
nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)
\end{code}

As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ ⌊ "x" ⌋ · ⌊ "x" ⌋ `` It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`.

\begin{code}
nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ⌊ "x" ⌋ · ⌊ "x" ⌋ ⦂ A)
nope₂ (⊢ƛ (Ax ∋x · Ax ∋x′))  =  contradiction (∋-injective ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()
\end{code}


#### Quiz

For each of the following, given a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ⌊ "y" ⌋ · ⌊ "x" ⌋ ⦂ A ``
2. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ⌊ "x" ⌋ · ⌊ "y" ⌋ ⦂ A ``
3. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ⌊ "y" ⌋ · ⌊ "x" ⌋ ⦂ A ``

For each of the following, give type `A`, `B`, and `C` for which it is derivable,
or explain why there are no such types.

1. `` ∅ , "x" ⦂ A ⊢ ⌊ "x" ⌋ · ⌊ "x" ⌋ ⦂ B ``
2. `` ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ⌊ "x" ⌋ · (⌊ "y" ⌋ · ⌊ "z" ⌋) ⦂ C ``


#### Exercise (`mul-type`)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well-typed.


## Unicode

This chapter uses the following unicode

    ⇒    U+21D2: RIGHTWARDS DOUBLE ARROW (\=>)
    ƛ    U+019B: LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    ·    U+00B7: MIDDLE DOT (\cdot)
    😇   U+1F607: SMILING FACE WITH HALO
    😈   U+1F608: SMILING FACE WITH HORNS
    ⟶  U+27F9: LONG RIGHTWARDS ARROW (\r5, \-->)
    ξ    U+03BE: GREEK SMALL LETTER XI (\Gx or \xi)
    β    U+03B2: GREEK SMALL LETTER BETA (\Gb or \beta)
    ∋    U+220B: CONTAINS AS MEMBER (\ni)
    ⊢    U+22A2: RIGHT TACK (\vdash or \|-)
    ⦂    U+2982: Z NOTATION TYPE COLON (\:)

