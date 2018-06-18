---
title     : "Lambda: Introduction to Lambda Calculus"
layout    : page
permalink : /Lambda/
---


\begin{code}
module plta.Lambda where
\end{code}

[Parts of this chapter take their text from chapter _Stlc_
of _Software Foundations_ (_Programming Language Foundations_).
Those parts will be revised.]

The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It captures the key concept of
_functional abstraction_, which appears in pretty much every programming
language, in the form of either functions, procedures, or methods.
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations.
We will instead echo Plotkin's Programmable Computable
Functions (PCF), and add operations on natural numbers and
recursive function definitions.

This chapter formalises the simply-typed lambda calculus, giving its
syntax, small-step semantics, and typing rules.  The next chapter
[LambdaProp]({{ site.baseurl }}{% link out/plta/LambdaProp.md %})
reviews its main properties, including
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
\end{code}

## Syntax of terms

Terms have seven constructs. Three are for the core lambda calculus:

  * Variables, `# x`
  * Abstractions, `ƛ x ⇒ N`
  * Applications, `L · M`

Three are for the naturals:

  * Zero, `` `zero ``
  * Successor, `` `suc ``
  * Case, `` `case L [zero⇒ M |suc x ⇒ N ] ``

And one is for recursion:

  * Fixpoint, `μ x ⇒ M`

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
      # x
      ƛ x ⇒ N
      L · M
      `zero
      `suc M
      `case L [zero⇒ M |suc x ⇒ N]
      μ x ⇒ M

And here it is formalised in Agda.
\begin{code}
Id : Set
Id = String

infix  6  ƛ_⇒_
infix  6  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  #_

data Term : Set where
  #_                       :  Id → Term
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
         `case # "m"
           [zero⇒ # "n"
           |suc "m" ⇒ `suc (# "+" · # "m" · # "n") ]

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
function that accepts two arguments and applies the first to the
second _n_ times.  This is called the _Church representation_ of the
naturals.  Here are some example terms: the Church numeral two, a
function that adds Church numerals, a function to compute successor,
and a term that computes two plus two.
\begin{code}
twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         # "m" · # "s" · (# "n" · # "s" · # "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (# "n")

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


### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `# x`
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
and `N` the _body_ of the abstraction.  One of the most important
aspects of lambda calculus is that consistent renaming of bound variables
leaves the meaning of a term unchanged.  Thus the five terms

* `` ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z") ``
* `` ƛ "f" ⇒ ƛ "x" ⇒ # "f" · (# "f" · # "x") ``
* `` ƛ "sam" ⇒ ƛ "zelda" ⇒ # "sam" · (# "sam" · # "zelda") ``
* `` ƛ "z" ⇒ ƛ "s" ⇒ # "z" · (# "z" · # "s") ``
* `` ƛ "😇" ⇒ ƛ "😈" ⇒ # "😇" · (# "😇" · # "😈" ) ``

are all considered equivalent.  Following the convention introduced
by Haskell Curry, who used the Greek letter `α` (_alpha_) to label such rules,
this equivalence relation is called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms.

* `` ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z") ``
  has both `s` and `z` as bound variables.

* `` ƛ "z" ⇒ # "s" · (# "s" · # "z") ``
  has `s` bound and `z` free.

* `` # "s" · (# "s" · # "z") ``
  has both `s` and `z` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.

Different occurrences of a variable may be bound and free.
In the term

    (ƛ "x" ⇒ # "x") · # "x"

the inner occurrence of `x` is bound while the outer occurrence is free.
Note that by alpha renaming, the term above is equivalent to

    (ƛ "y" ⇒ # "y") · # "x"

in which `y` is bound and `x` is free.  A common convention, called the
_Barendregt convention_, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.

Case and recursion also introduce bound variables, which are also subject
to alpha renaming. In the term

    μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
      `case # "m"
        [zero⇒ # "n"
        |suc "m" ⇒ `suc (# "+" · # "m" · # "n") ]

notice that there are two binding occurrences of `m`, one in the first
line and one in the last line.  It is equivalent to the following term,

    μ "plus" ⇒ ƛ "x" ⇒ ƛ "y" ⇒
      `case # "x"
        [zero⇒ # "y"
        |suc "x′" ⇒ `suc (# "plus" · # "x′" · # "y") ]

where the two binding occurrences corresponding to `m` now have distinct
names, `x` and `x′`.


## Values

We only consider reduction of _closed_ terms,
those that contain no free variables.  We consider
a precise definition of free variables in Chapter
[LambdaProp]({{ site.baseurl }}{% link out/plta/LambdaProp.md %}).

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

      (ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z")) · sucᶜ · `zero
    ⟶
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · "z")) · `zero
    ⟶
      sucᶜ · (sucᶜ · `zero)

where we substitute `sucᶜ` for `` # "s" `` and `` `zero `` for `` # "z" ``
in the body of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
"substitute term `V` for free occurrences of variable `x` in term `N`",
or, more compactly, "substitute `V` for `x` in `N`".
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since in fact we
always substitute values.

Here are some examples.

* `` # "s" [ "s" := sucᶜ ] `` yields `` sucᶜ ``
* `` # "z" [ "s" := sucᶜ ] `` yields `` # "z" ``
* `` (# "s" · # "z") [ "s" := sucᶜ ] `` yields `` sucᶜ · # "z" ``
* `` (# "s" · (# "s" · # "z")) [ "s" := sucᶜ ] `` yields `` sucᶜ · (sucᶜ · # "z") ``
* `` (ƛ "z" ⇒ # "s" · (# "s" · # "z")) [ "s" := sucᶜ ] `` yields
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · # "z") ``
* `` (ƛ "y" ⇒ # "y") [ "x" := `zero ] `` yields `` ƛ "y" ⇒ # "y" ``
* `` (ƛ "x" ⇒ # "x") [ "x" := `zero ] `` yields `` ƛ "x" ⇒ # "x" ``
* `` (ƛ "y" ⇒ # "x") [ "x" := `zero ] `` yields `` ƛ "y" ⇒ # `zero ``

The last but one example is important: substituting `` `zero `` for `x` in
`` ƛ "x" ⇒ # "x" `` does _not_ yield `` ƛ "x" ⇒ `zero ``.
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
infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(# x) [ y := V ] with x ≟ y
... | yes _  =  V
... | no  _  =  # x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _  =  ƛ x ⇒ N
... | no  _  =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] =  L [ y := V ] · M [ y := V ]
(`zero) [ y := V ] = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
(`case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _  =  `case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _  =  `case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _  =  μ x ⇒ N
... | no  _  =  μ x ⇒ N [ y := V ]
\end{code}

The two key cases are variables and abstraction.

* For variables, we compare `w`, the variable we are substituting for,
with `x`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x` unchanged.

* For abstractions, we compare `w`, the variable we are substituting for,
with `x`, the variable bound in the abstraction. If they are the same,
we yield the abstraction unchanged, otherwise we subsititute inside the body.

Case expressions and recursion also have bound variables that
are treated similarly to those in lambda abstractions.
In all other cases, we push substitution recursively into
the subterms.


#### Examples

Here is confirmation that the examples above are correct.

\begin{code}
_ : (# "s") [ "s" := sucᶜ ] ≡  sucᶜ
_ = refl

_ : (# "z") [ "s" := sucᶜ ] ≡  # "z"
_ = refl

_ : (# "s" · # "z") [ "s" := sucᶜ ] ≡  sucᶜ · # "z"
_ = refl

_ : (# "s" · # "s" · # "z") [ "s" := sucᶜ ] ≡  sucᶜ · sucᶜ · # "z"
_ = refl

_ : (ƛ "z" ⇒ # "s" · # "s" · # "z") [ "s" := sucᶜ ] ≡  ƛ "z" ⇒ sucᶜ · sucᶜ · # "z"
_ = refl

_ : (ƛ "y" ⇒ # "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ # "y"
_ = refl

_ : (ƛ "x" ⇒ # "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ # "x"
_ = refl

_ : (ƛ "x" ⇒ # "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
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

In an informal presentation of the operational semantics,
the rules for reduction of lambda terms are written as follows.

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

    (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x")  ⟶  ???

1.  `` (ƛ "x" ⇒ # "x") ``
2.  `` (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") ``
3.  `` (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") ``

What does the following term step to?

    (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x")  ⟶  ???

1.  `` (ƛ "x" ⇒ # "x") ``
2.  `` (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") ``
3.  `` (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") · (ƛ "x" ⇒ # "x") ``

What does the following term step to?  (Where `two` and `sucᶜ` are as defined above.)

    two · sucᶜ · `zero  ⟶  ???

1.  `` sucᶜ · (sucᶜ · `zero) ``
2.  `` (ƛ "z" ⇒ sucᶜ · (sucᶜ · # "z")) · `zero ``
3.  `` `zero ``


## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `⟶*` of the step function `⟶`.
Here it is formalised in Agda, along similar lines to what we defined in
Chapter [Equality]({{ site.baseurl }}{% link out/plta/Equality.md %}).

\begin{code}
infix  2 _⟶*_
infix  1 begin_
infixr 2 _⟶⟨_⟩_
infix  3 _∎

data _⟶*_ : Term → Term → Set where
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
  (It is written `M ∎`.)

* From term `L` we can take a single of type `L ⟶ M`
  followed by zero or more steps of type `M ⟶* N`,
  giving a step of type `L ⟶* N`.
  (It is written `L ⟨ L⟶M ⟩ M⟶*N`,
  where `L⟶M` and `M⟶*N` are steps of the appropriate type.)

The names have been chosen to allow us to lay
out example reductions in an appealing way.
Here is a sample reduction demonstating that two plus two is four.
\begin{code}
_ : four ⟶* `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  ⟶⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      `case # "m" [zero⇒ # "n" |suc "m" ⇒ `suc (plus · # "m" · # "n") ])
        · two · two
  ⟶⟨ ξ-·₁ (β-ƛ· (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
      `case two [zero⇒ # "n" |suc "m" ⇒ `suc (plus · # "m" · # "n") ])
         · two
  ⟶⟨ β-ƛ· (V-suc (V-suc V-zero)) ⟩
    `case two [zero⇒ two |suc "m" ⇒ `suc (plus · # "m" · two) ]
  ⟶⟨ β-case-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  ⟶⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      `case # "m" [zero⇒ # "n" |suc "m" ⇒ `suc (plus · # "m" · # "n") ])
        · `suc `zero · two)
  ⟶⟨ ξ-suc (ξ-·₁ (β-ƛ· (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
      `case `suc `zero [zero⇒ # "n" |suc "m" ⇒ `suc (plus · # "m" · # "n") ])
        · two)
  ⟶⟨ ξ-suc (β-ƛ· (V-suc (V-suc V-zero))) ⟩
    `suc (`case `suc `zero [zero⇒ two |suc "m" ⇒ `suc (plus · # "m" · two) ])
  ⟶⟨ ξ-suc (β-case-suc V-zero) ⟩
    `suc `suc (plus · `zero · two)
  ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      `case # "m" [zero⇒ # "n" |suc "m" ⇒ `suc (plus · # "m" · # "n") ])
        · `zero · two)
  ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ· V-zero))) ⟩
    `suc `suc ((ƛ "n" ⇒
      `case `zero [zero⇒ # "n" |suc "m" ⇒ `suc (plus · # "m" · # "n") ])
        · two)
  ⟶⟨ ξ-suc (ξ-suc (β-ƛ· (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (`case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · # "m" · two) ])
  ⟶⟨ ξ-suc (ξ-suc β-case-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎
\end{code}

And here is a similar sample reduction for Church numerals.
\begin{code}
_ : fourᶜ ⟶* `suc `suc `suc `suc `zero
_ =
  begin
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ # "m" · # "s" · (# "n" · # "s" · # "z"))
      · twoᶜ · twoᶜ · sucᶜ · `zero
  ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ· V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · # "s" · (# "n" · # "s" · # "z"))
      · twoᶜ · sucᶜ · `zero
  ⟶⟨ ξ-·₁ (ξ-·₁ (β-ƛ· V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · # "s" · (twoᶜ · # "s" · # "z")) · sucᶜ · `zero
  ⟶⟨ ξ-·₁ (β-ƛ· V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · # "z")) · `zero
  ⟶⟨ β-ƛ· V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  ⟶⟨ ξ-·₁ (β-ƛ· V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · # "z")) · (twoᶜ · sucᶜ · `zero)
  ⟶⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ· V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · # "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · # "z")) · `zero)
  ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · # "z")) · (sucᶜ · (sucᶜ · `zero))
  ⟶⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ· V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · # "z")) · (sucᶜ · (`suc `zero))
  ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · # "z")) · (`suc `suc `zero)
  ⟶⟨ β-ƛ· (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc `suc `zero)
  ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  ⟶⟨ β-ƛ· (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎
\end{code}

In the next chapter, we will see how to compute such reduction sequences.


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

    ƛ "s" ⇒ # "s" · (# "s"  · `zero)

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.

* What is the type of the following term?

    (ƛ "s" ⇒ # "s" · (# "s"  · `zero)) · sucᵐ

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

* `` `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ``

is the context that associates variable ` "s" ` with type `` `ℕ ⇒ `ℕ ``,
and variable ` "z" ` with type `` `ℕ ``.

We have two forms of _judgement_.  The first is written

    Γ ∋ x ⦂ A

and indicates in context `Γ` that variable `x` has type `A`.
For example

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

give us the types associated with variables ` "z" ` and ` "s" `, respectively.
The symbol `∋` (pronounced "ni", for "in" backwards) is chosen because
checking that `Γ ∋ x ⦂ A` is anologous to checking whether `x ⦂ A` appears
in a list of variables and types corresponding to `Γ`.

The second judgement is written

    Γ ⊢ M ⦂ A

and indicates in context `Γ` that term `M` has type `A`.
Context `Γ` provides types for all the free variables in `M`.
For example

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ # "s" · (# "s" · # "z") ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ (ƛ "z" ⇒ # "s" · (# "s" · # "z")) ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z")) ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

The proof rules come in pairs, with rules to introduce and to
eliminate each connective, labeled `-I` and `-E`, respectively. As we
read the rules from top to bottom, introduction and elimination rules
do what they say on the tin: the first _introduces_ a formula for the
connective, which appears in the conclusion but not in the premises;
while the second _eliminates_ a formula for the connective, which appears in
a premise but not in the conclusion. An introduction rule describes
how to construct a value of the type (abstractions yield functions,
`` `suc `` and `` `zero `` yield naturals), while an elimination rule describes
how to deconstruct a value of the given type (applications use
functions, case expressions use naturals).

Here are contexts, lookup rules, and type rules formalised in Agda.

\begin{code}
infix  4  _∋_⦂_
infix  4  _⊢_⦂_
infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
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

  ℕ-I₁ : ∀ {Γ}
      -------------
    → Γ ⊢ `zero ⦂ `ℕ

  ℕ-I₂ : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  ℕ-E : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      --------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  Fix : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      ------------------
    → Γ ⊢ μ x ⇒ M ⦂ A
\end{code}

The rules are deterministic, in that
at most one rule applies to every term.


### Example type derivations

Here is a typing example.  First, here is how
it would be written in an informal description of the
formal semantics.

Derivation of for the Church numeral two:

    ∋s                        ∋s                          ∋z
    ------------------- Ax    ------------------- Ax     --------------- Ax
    Γ₂ ⊢ # "s" ⦂ A ⇒ A        Γ₂ ⊢ # "s" ⦂ A ⇒ A         Γ₂ ⊢ # "z" ⦂ A
    ------------------- Ax    ------------------------------------------ ⇒-E
    Γ₂ ⊢ # "s" ⦂ A ⇒ A        Γ₂ ⊢ # "s" · # "z" ⦂ A
    -------------------------------------------------- ⇒-E
    Γ₂ ⊢ # "s" · (# "s" · # "z") ⦂ A
    ---------------------------------------------- ⇒-I
    Γ₁ ⊢ ƛ "z" ⇒ # "s" · (# "s" · # "z") ⦂ A ⇒ A
    ---------------------------------------------------------- ⇒-I
    ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z") ⦂ A ⇒ A

Where `∋s` and `∋z` abbreviate the two derivations:


                 ---------------- Z
    "s" ≢ "z"    Γ₁ ∋ "s" ⦂ A ⇒ A
    ----------------------------- S        ------------- Z
    Γ₂ ∋ "s" ⦂ A ⇒ A                       Γ₂ ∋ "z" ⦂ A

and where `Γ₁ = ∅ , s ⦂ A ⇒ A` and `Γ₂ = ∅ , s ⦂ A ⇒ A , z ⦂ A`.

Here is the above derivation formalised in Agda.

\begin{code}
Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {A} → ∅ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⇒-I (⇒-I (⇒-E (Ax ∋s) (⇒-E (Ax ∋s) (Ax ∋z))))
  where

  s≢z : "s" ≢ "z"
  s≢z ()

  ∋s = S s≢z Z
  ∋z = Z
\end{code}

Typing for the first example.
\begin{code}
⊢two : ∅ ⊢ two ⦂ `ℕ
⊢two = ℕ-I₂ (ℕ-I₂ ℕ-I₁)

⊢plus : ∅ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = Fix (⇒-I (⇒-I (ℕ-E (Ax ∋m) (Ax ∋n)
         (ℕ-I₂ (⇒-E (⇒-E (Ax ∋+) (Ax ∋m′)) (Ax ∋n′))))))
  where
  ∋+  = (S (λ()) (S (λ()) (S (λ()) Z)))
  ∋m  = (S (λ()) Z)
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = (S (λ()) Z)

⊢four : ∅ ⊢ four ⦂ `ℕ
⊢four = ⇒-E (⇒-E ⊢plus ⊢two) ⊢two
\end{code}

Typing for the rest of the Church example.
\begin{code}
⊢plusᶜ : ∀ {A} → ∅ ⊢ plusᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = ⇒-I (⇒-I (⇒-I (⇒-I (⇒-E (⇒-E (Ax ∋m) (Ax ∋s))
                             (⇒-E (⇒-E (Ax ∋n) (Ax ∋s)) (Ax ∋z))))))
  where
  ∋m = S (λ()) (S (λ()) (S (λ()) Z))
  ∋n = S (λ()) (S (λ()) Z)
  ∋s = S (λ()) Z
  ∋z = Z

⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⇒-I (ℕ-I₂ (Ax ∋n))
  where
  ∋n = Z

⊢fourᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ⦂ `ℕ
⊢fourᶜ = ⇒-E (⇒-E (⇒-E (⇒-E ⊢plusᶜ ⊢twoᶜ) ⊢twoᶜ) ⊢sucᶜ) ℕ-I₁
\end{code}

*(((Rename I and E rules with the constructors and a turnstyle)))*

*(((Explain the alternative names with I and E)))*

*(((Copy ≠ from chapter Inference and use it to replace `λ()` in examples)))*


#### Interaction with Agda

*(((rewrite the following)))*

Construction of a type derivation is best done interactively.
Start with the declaration:

    ⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
    ⊢sucᶜ = ?

Typing C-l causes Agda to create a hole and tell us its expected type.

    ⊢sucᶜ = { }0
    ?0 : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `sucᶜ` in a `λ`, which is typed using `⇒-I`. The
`⇒-I` rule in turn takes one argument, which Agda leaves as a hole.

    ⊢sucᶜ = ⇒-I { }0
    ?0 : ∅ , x ⦂ `ℕ ⊢ if ` x then false else true ⦂ `ℕ

Again we fill in the hole by typing C-c C-r. Agda observes that the
outermost term is now `if_then_else_`, which is typed using ``ℕ-E`. The
``ℕ-E` rule in turn takes three arguments, which Agda leaves as holes.

    ⊢sucᶜ = ⇒-I (`ℕ-E { }0 { }1 { }2)
    ?0 : ∅ , x ⦂ `ℕ ⊢ ` x ⦂
    ?1 : ∅ , x ⦂ `ℕ ⊢ false ⦂ `ℕ
    ?2 : ∅ , x ⦂ `ℕ ⊢ true ⦂ `ℕ

Again we fill in the three holes by typing C-c C-r in each. Agda observes
that `` ` x ``, `false`, and `true` are typed using `Ax`, ``ℕ-I₂`, and
``ℕ-I₁` respectively. The `Ax` rule in turn takes an argument, to show
that `(∅ , x ⦂ `ℕ) x = just `ℕ`, which can in turn be specified with a
hole. After filling in all holes, the term is as above.

The entire process can be automated using Agsy, invoked with C-c C-a.

### Lookup is injective

Note that `Γ ∋ x ⦂ A` is injective.
\begin{code}
∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z        Z          =  refl
∋-injective Z        (S x≢ _)   =  ⊥-elim (x≢ refl)
∋-injective (S x≢ _) Z          =  ⊥-elim (x≢ refl)
∋-injective (S _ ∋x) (S _ ∋x′)  =  ∋-injective ∋x ∋x′
\end{code}

The relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `ƛ "x" ⇒ "x"` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term `` `suc `zero ·
`zero ``.  In other words, no type `A` is the type of this term.  It
cannot be typed, because doing so requires that the first term in the
application is both a natural and a function.

\begin{code}
nope₁ : ∀ {A} → ¬ (∅ ⊢ `suc `zero · `zero ⦂ A)
nope₁ (⇒-E () _)
\end{code}

As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ # "x" · # "x" `` It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`.

\begin{code}
nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ # "x" · # "x" ⦂ A)
nope₂ (⇒-I (⇒-E (Ax ∋x) (Ax ∋x′)))  =  contradiction (∋-injective ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()
\end{code}


#### Quiz

For each of the following, given a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , y ⦂ A ⊢ λ[ x ⦂ `ℕ ] ` x ⦂ `ℕ ⇒ `ℕ ``
2. `` ∅ ⊢ λ[ y ⦂ `ℕ ⇒ `ℕ ] λ[ x ⦂ `ℕ ] ` y · ` x ⦂ A ``
3. `` ∅ ⊢ λ[ y ⦂ `ℕ ⇒ `ℕ ] λ[ x ⦂ `ℕ ] ` x · ` y ⦂ A ``
4. `` ∅ , x ⦂ A ⊢ λ[ y : `ℕ ⇒ `ℕ ] `y · `x : A ``

For each of the following, give type `A`, `B`, `C`, and `D` for which it is derivable,
or explain why there are no such types.

1. `` ∅ ⊢ λ[ y ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ ] λ[ x ⦂ `ℕ ] ` y · ` x ⦂ A ``
2. `` ∅ , x ⦂ A ⊢ x · x ⦂ B ``
3. `` ∅ , x ⦂ A , y ⦂ B ⊢ λ[ z ⦂ C ] ` x · (` y · ` z) ⦂ D ``



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
    ⦂    U+2982: Z NOTATION TYPE COLON (\:)

