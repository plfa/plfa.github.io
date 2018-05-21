---
title     : "Lambda: Introduction to Lambda Calculus"
layout    : page
permalink : /Lambda
---

The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It embodies the concept of
_functional abstraction_, which shows up in almost every programming
language in some form (as functions, procedures, or methods).
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations.
We will instead echo the power of Plotkin's Programmable Computable
Functions (PCF), and add operations on natural numbers and
recursive function definitions.

This chapter formalises the simply-typed lambda calculus, giving its
syntax, small-step semantics, and typing rules.  The next chapter
[LambdaProp](LambdaProp) reviews its main properties, including
progress and preservation.  Following chapters will look at a number
of variants of lambda calculus.

Readers should be warned up front: the approach we take here is
_not_ our recommended approach to formalisation.  It turns out that
using De Bruijn indices and inherently-typed terms, as we will do in
Chapter [DeBruijn](DeBruijn), leads to a more compact formulation.
Nonetheless, we begin with named variables, partly because such terms
are easier to read and partly because the development is more traditional.

*(((Say something about how I stole from but improved upon SF)))*


## Imports

\begin{code}
module Lambda where

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
  * Case, `` `case L [zero⇒ M |suc x⇒ N ]

And one is for recursion:

  * Fixpoint, `μ x ⇒ M`

Abstraction is also called lambda abstraction, and is the construct
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
then successor, and tightest of all is the constructor for variables.  Case
expressions are self-bracketing.


### Example terms

Here are some example terms: the naturals two and four, the recursive
definition of a function to naturals, and a term that computes
two plus two.
\begin{code}
tm2 tm4 tm+ tm2+2 : Term
tm2    =  `suc `suc `zero
tm4    =  `suc `suc `suc `suc `zero
tm+    =  μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
            `case # "m"
              [zero⇒ # "n"
              |suc "m" ⇒ `suc (# "+" · # "m" · # "n") ]
tm2+2  =  tm+ · tm2 · tm2            
\end{code}
The recursive definition of addition is similar to our original
definition of `_+_` for naturals, as given in Chapter [Natural](Naturals).

As a second example, we use higher-order functions to represent
natural numbers.  In particular, the number _n_ is represented by a
function that accepts two arguments and applies the first to the
second _n_ times.  This is called the _Church representation_ of the
naturals.  Similar to before, we define: the numerals two and four, a
function to add numerals, a function to convert numerals to naturals,
and a term that computes two plus two.
\begin{code}
ch2 ch4 ch+ chℕ ch2+2 : Term
ch2    =  ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z")
ch4    =  ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · (# "s" · (# "s" · # "z")))
ch+    =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
            # "m" · # "s" · (# "n" · # "s" · # "z")
chℕ    =  ƛ "n" ⇒ # "n" · (ƛ "m" ⇒ `suc (# "m")) · `zero
ch2+2  =  ch+ · ch2 · ch2
\end{code}
Two takes two arguments `s` and `z`, and applies `s` twice to `z`;
similarly for four.  Addition takes two numerals `m` and `n`, a
function `s` and an argument `z`, and it uses `m` to apply `s` to the
result of using `n` to apply `s` to `z`; hence `s` is applied `m` plus
`n` times to `z`, yielding the Church numeral for the sum of `m` and
`n`.  The conversion function takes a numeral `n` and instantiates its
first argument to the successor function and its second argument to
zero.

### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `# x`
for a term that is a variable. Agda requires we distinguish.
Often researchers use `var x` rather than `# x`, but we chose
the latter as less noisy.

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
aspects of lambda calculus is consistent renaming of bound variables
leaves the meaning of a term unchanged.  Thus the five terms

* `` ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z") ``
* `` ƛ "f" ⇒ ƛ "x" ⇒ # "f" · (# "f" · # "x") ``
* `` ƛ "fred" ⇒ ƛ "xander" ⇒ # "fred" · (# "fred" · # "xander") ``
* `` λ[ 😇 ∶ 𝔹 ⇒ 𝔹 ] λ[ 😈  ∶ 𝔹 ] ` 😇 · (` 😇 · ` 😈 ) ``  
* `` ƛ "z" ⇒ ƛ "s" ⇒ # "z" · (# "z" · # "s") ``

are all considered equivalent.  Following the convention introduced
by Haskell Curry, this equivalence relation is called _alpha renaming_.

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
Barendregt convention, is to use alpha renaming to ensure that the bound
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
[LambdaProp](LambdaProp).

*rewrite (((*
A term is a value if it is fully reduced.
For booleans, the situation is clear: `true` and
`false` are values, while conditionals are not.
For functions, applications are not values, because
we expect them to further reduce, and variables are
not values, because we focus on closed terms.
Following convention, we treat all abstractions
as values.
*)))*

The predicate `Value M` holds if term `M` is a value.

\begin{code}
data Value : Term → Set where

  value-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  value-zero :
      -----------
      Value `zero

  value-suc : ∀ {V}
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
We consider this approach in a [later chapter](Untyped).

## Substitution

*((( rewrite examples with `not` )))*

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

*((( add material about binding in case and μ )))*

The two key cases are variables and abstraction.

* For variables, we compare `w`, the variable we are substituting for,
with `x`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x` unchanged.

* For abstractions, we compare `w`, the variable we are substituting for,
with `x`, the variable bound in the abstraction. If they are the same,
we yield the abstraction unchanged, otherwise we subsititute inside the body.

In all other cases, we push substitution recursively into
the subterms.



#### Examples

Here is confirmation that the examples above are correct.

\begin{code}
_ : (# "s" · # "s" · # "z") [ "z" := `zero ] ≡  # "s" · # "s" · `zero
_ = refl

_ : `zero [ "m" := `zero ] ≡ `zero
_ = refl

_ : (`suc `suc # "n") [ "n" := `suc `suc `zero ] ≡ `suc `suc `suc `suc `zero
_ = refl

_ : (ƛ "x" ⇒ # "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ # "x"
_ = refl

_ : (ƛ "x" ⇒ # "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "y" ⇒ # "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ # "y"
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
infix 4 _⟹_ 

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
      ------------------------------
    → (ƛ x ⇒ N) · V ⟹ N [ x := V ]

  ξsuc : ∀ {M M′}
    → M ⟹ M′
      ------------------
    → `suc M ⟹ `suc M′

  ξcase : ∀ {x L L′ M N}
    → L ⟹ L′    
      -----------------------------------------------------------------
    → `case L [zero⇒ M |suc x ⇒ N ] ⟹ `case L′ [zero⇒ M |suc x ⇒ N ]

  βcase-zero : ∀ {x M N}
      ----------------------------------------
    → `case `zero [zero⇒ M |suc x ⇒ N ] ⟹ M

  βcase-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → `case `suc V [zero⇒ M |suc x ⇒ N ] ⟹ N [ x := V ]

  βμ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M ⟹ M [ x := μ x ⇒ M ]
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

*(((REDUCTION EXAMPLES GO HERE, ONCE I CAN COMPUTE THEM)))*
\begin{code}
\end{code}

Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.


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

* ``(`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ`` abbreviates ``((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ))``
* `# "+" · # "m" · # "n"` abbreviates `(# "+" · # "m") · # "n"`.

### Quiz

* What is the type of the following term?

    ƛ "s" ⇒ # "s" · (# "s"  · `zero)

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  4. `` `ℕ ⇒ `ℕ ``
  5. `` `ℕ ``

  Give more than one answer if appropriate.

* What is the type of the following term?

    (ƛ "s" ⇒ # "s" · (# "s"  · `zero)) · (ƛ "m" ⇒ `suc # "m")

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  4. `` `ℕ ⇒ `ℕ ``
  5. `` `ℕ ``

  Give more than one answer if appropriate.



## Typing

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

*(((update following later)))*

In general, we use typing _judgements_ of the form

    Γ ⊢ M ⦂ A

to assert in type environment `Γ` that term `M` has type `A`.
Environment `Γ` provides types for all the free variables in `M`.

Here are three examples. 

* `` ∅ , "f" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ # "f" · (# "f" · # "x") ⦂  `ℕ ``
* `` ∅ , "f" ⦂ `ℕ ⇒ `ℕ ⊢ (ƛ "x" ⇒ # "f" · (# "f" · # "x")) ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "f" ⇒ ƛ "x" ⇒ # "f" · (# "f" · # "x")) ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

Environments are partial maps from identifiers to types, built using `∅`
for the empty map, and `Γ , x ⦂ A` for the map that extends
environment `Γ` by mapping variable `x` to type `A`.

*(((It's redundant to have two versions of the rules)))*

*(((Need text to explain `Γ ∋ x ⦂ A`)))*

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

    ------------- `ℕ-I₁
    Γ ⊢ true ⦂ `ℕ

    -------------- `ℕ-I₂
    Γ ⊢ false ⦂ `ℕ

    Γ ⊢ L : `ℕ
    Γ ⊢ M ⦂ A
    Γ ⊢ N ⦂ A
    -------------------------- `ℕ-E
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

  `ℕ-E : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      --------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ⦂ A
\end{code}

### Example type derivations

Here is a typing example.  First, here is how
it would be written in an informal description of the
formal semantics.

Derivation of for the Church numeral two:

    ∋s                        ∋s                          ∋z
    ------------------- Ax    ------------------- Ax     --------------- Ax
    Γ₂ ⊢ # "s" ⦂ `ℕ ⇒ `ℕ        Γ₂ ⊢ # "s" ⦂ `ℕ ⇒ `ℕ         Γ₂ ⊢ # "z" ⦂ `ℕ
    ------------------- Ax    ------------------------------------------ ⇒-E
    Γ₂ ⊢ # "s" ⦂ `ℕ ⇒ `ℕ        Γ₂ ⊢ # "s" · # "z" ⦂ `ℕ
    --------------------------------------------------  ⇒-E
    Γ₂ ⊢ # "s" · (# "s" · # "z") ⦂ `ℕ
    ---------------------------------------------- ⇒-I
    Γ₁ ⊢ ƛ "z" ⇒ # "s" · (# "s" · # "z") ⦂ `ℕ ⇒ `ℕ
    ---------------------------------------------------------- ⇒-I
    ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z") ⦂ `ℕ ⇒ `ℕ

Where `∋s` and `∋z` abbreviate the two derivations:


                 ---------------- Z           
    "s" ≢ "z"    Γ₁ ∋ "s" ⦂ B ⇒ B          
    ----------------------------- S        ------------- Z  
    Γ₂ ∋ "s" ⦂ B ⇒ B                       Γ₂ ∋ "z" ⦂ `ℕ

where `Γ₁ = ∅ , s ⦂ `ℕ ⇒ `ℕ` and `Γ₂ = ∅ , s ⦂ `ℕ ⇒ `ℕ , z ⦂ `ℕ`.

*((( possibly add another example, for plus )))*

Here is the above derivation formalised in Agda.

\begin{code}
⊢ch2 : ∅ ⊢ ch2 ⦂ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
⊢ch2 = ⇒-I (⇒-I (⇒-E (Ax ⊢s) (⇒-E (Ax ⊢s) (Ax ⊢z))))
  where

  s≢z : "s" ≢ "z"
  s≢z ()

  ⊢s = S s≢z Z
  ⊢z = Z
\end{code}


#### Interaction with Agda

*(((rewrite the followign)))*

Construction of a type derivation is best done interactively.
Start with the declaration:

    ⊢not : ∅ ⊢ not ⦂ `ℕ ⇒ `ℕ
    ⊢not = ?

Typing C-l causes Agda to create a hole and tell us its expected type.

    ⊢not = { }0
    ?0 : ∅ ⊢ not ⦂ `ℕ ⇒ `ℕ

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `not` in a `λ`, which is typed using `⇒-I`. The
`⇒-I` rule in turn takes one argument, which Agda leaves as a hole.

    ⊢not = ⇒-I { }0
    ?0 : ∅ , x ⦂ `ℕ ⊢ if ` x then false else true ⦂ `ℕ

Again we fill in the hole by typing C-c C-r. Agda observes that the
outermost term is now `if_then_else_`, which is typed using ``ℕ-E`. The
``ℕ-E` rule in turn takes three arguments, which Agda leaves as holes.

    ⊢not = ⇒-I (`ℕ-E { }0 { }1 { }2)
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
    ⦂    U+2982: Z NOTATION TYPE COLON (\:)
    ·    U+00B7: MIDDLE DOT (\cdot)
    😇   U+1F607: SMILING FACE WITH HALO
    😈   U+1F608: SMILING FACE WITH HORNS
    ′    U+2032: PRIME (\')
    ⟹  U+27F9: LONG RIGHTWARDS DOUBLE ARROW (\r6)
    ξ    U+03BE: GREEK SMALL LETTER XI (\Gx or \xi)
    β    U+03B2: GREEK SMALL LETTER BETA (\Gb or \beta)

Note that ′ (U+2032: PRIME) is not the same as ' (U+0027: APOSTROPHE).
