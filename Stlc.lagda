---
title         : "Stlc: The Simply Typed Lambda-Calculus"
layout        : default
hide-implicit : false
extra-script : [agda-extra-script.html]
extra-style  : [agda-extra-style.html]
permalink     : "sf/Stlc.html"
---

\begin{code}
module Stlc where
\end{code}

<div class="hidden">
\begin{code}
open import Maps using (Id; id; _≟_; PartialMap; module PartialMap)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Product using (∃; ∄; _,_)
open import Function using (_∘_; _$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
\end{code}
</div>

# The Simply Typed Lambda-Calculus

The simply typed lambda-calculus (STLC) is a tiny core
calculus embodying the key concept of _functional abstraction_,
which shows up in pretty much every real-world programming
language in some form (functions, procedures, methods, etc.).

We will follow exactly the same pattern as in the previous chapter
when formalizing this calculus (syntax, small-step semantics,
typing rules) and its main properties (progress and preservation).
The new technical challenges arise from the mechanisms of
_variable binding_ and _substitution_.  It which will take some
work to deal with these.


## Overview

The STLC is built on some collection of _base types_:
booleans, numbers, strings, etc.  The exact choice of base types
doesn't matter much---the construction of the language and its
theoretical properties work out the same no matter what we
choose---so for the sake of brevity let's take just $$bool$$ for
the moment.  At the end of the chapter we'll see how to add more
base types, and in later chapters we'll enrich the pure STLC with
other useful constructs like pairs, records, subtyping, and
mutable state.

Starting from boolean constants and conditionals, we add three
things:

  - variables
  - function abstractions
  - application

This gives us the following collection of abstract syntax
constructors (written out first in informal BNF notation---we'll
formalize it below).

$$
  \begin{array}{rll}
    \text{Terms}\;s,t,u
    ::=  & x & \text{variable} \\
    \mid & \lambda x : A . t & \text{abstraction} \\
    \mid & s\;t & \text{application} \\
    \mid & true & \text{constant true} \\
    \mid & false & \text{constant false} \\
    \mid & \text{if }s\text{ then }t\text{ else }u & \text{conditional}
  \end{array}
$$

In a lambda abstraction $$\lambda x : A . t$$, the variable $$x$$ is called the
_parameter_ to the function; the term $$t$$ is its _body_.  The annotation $$:A$$
specifies the type of arguments that the function can be applied to.

Some examples:

  - The identity function for booleans:

    $$\lambda x:bool. x$$.
  - The identity function for booleans, applied to the boolean $$true$$:

    $$(\lambda x:bool. x)\;true$$.
  - The boolean "not" function:

    $$\lambda x:bool. \text{if }x\text{ then }false\text{ else }true$$.
  - The constant function that takes every (boolean) argument to $$true$$:

    $$\lambda x:bool. true$$.
  - A two-argument function that takes two booleans and returns the
    first one:

    $$\lambda x:bool. \lambda y:bool. x$$.

    As in Agda, a two-argument function is really a
    one-argument function whose body is also a one-argument function.
  - A two-argument function that takes two booleans and returns the
    first one, applied to the booleans $$false$$ and $$true$$:

    $$(\lambda x:bool. \lambda y:bool. x)\;false\;true$$.

    As in Agda, application associates to the left---i.e., this
    expression is parsed as

    $$((\lambda x:bool. \lambda y:bool. x)\;false)\;true$$.

  - A higher-order function that takes a _function_ $$f$$ (from booleans
    to booleans) as an argument, applies $$f$$ to $$true$$, and applies
    $$f$$ again to the result:

    $$\lambda f:bool\rightarrow bool. f\;(f\;true)$$.

  - The same higher-order function, applied to the constantly $$false$$
    function:

    $$(\lambda f:bool\rightarrow bool. f\;(f\;true))\;(\lambda x:bool. false)$$.

As the last several examples show, the STLC is a language of
_higher-order_ functions: we can write down functions that take
other functions as arguments and/or return other functions as
results.

The STLC doesn't provide any primitive syntax for defining _named_
functions---all functions are "anonymous."  We'll see in chapter
`MoreStlc` that it is easy to add named functions to what we've
got---indeed, the fundamental naming and binding mechanisms are
exactly the same.

The _types_ of the STLC include $$bool$$, which classifies the
boolean constants $$true$$ and $$false$$ as well as more complex
computations that yield booleans, plus _arrow types_ that classify
functions.

$$
    \text{Types}\;A,B ::= bool \mid A \rightarrow B
$$

For example:

  - $$\lambda x:bool. false$$ has type $$bool\rightarrow bool$$;
  - $$\lambda x:bool. x$$ has type $$bool\rightarrow bool$$;
  - $$(\lambda x:bool. x)\;true$$ has type $$bool$$;
  - $$\lambda x:bool. \lambda y:bool. x$$ has type
    $$bool\rightarrow bool\rightarrow bool$$
    (i.e., $$bool\rightarrow (bool\rightarrow bool)$$)
  - $$(\lambda x:bool. \lambda y:bool. x)\;false$$ has type $$bool\rightarrow bool$$
  - $$(\lambda x:bool. \lambda y:bool. x)\;false\;true$$ has type $$bool$$

## Syntax

We begin by formalizing the syntax of the STLC.
Unfortunately, $$\rightarrow$$ is already used for Agda's function type,
so we will STLC's function type as `_⇒_`.


### Types

\begin{code}
data Type : Set where
  bool : Type
  _⇒_  : Type → Type → Type
\end{code}

<div class="hidden">
\begin{code}
infixr 5 _⇒_
\end{code}
</div>


### Terms

\begin{code}
data Term : Set where
  var   : Id → Term
  app   : Term → Term → Term
  abs   : Id → Type → Term → Term
  true  : Term
  false : Term
  if_then_else_ : Term → Term → Term → Term
\end{code}

<div class="hidden">
\begin{code}
infixr 8 if_then_else_
\end{code}
</div>

Note that an abstraction $$\lambda x:A.t$$ (formally, `abs x A t`) is
always annotated with the type $$A$$ of its parameter, in contrast
to Agda (and other functional languages like ML, Haskell, etc.),
which use _type inference_ to fill in missing annotations.  We're
not considering type inference here.

Some examples...

\begin{code}
x = id 0
y = id 1
z = id 2
\end{code}

<div class="hidden">
\begin{code}
{-# DISPLAY zero = x #-}
{-# DISPLAY suc zero = y #-}
{-# DISPLAY suc (suc zero) = z #-}
\end{code}
</div>

$$\text{idB} = \lambda x:bool. x$$.

\begin{code}
idB = (abs x bool (var x))
\end{code}

$$\text{idBB} = \lambda x:bool\rightarrow bool. x$$.

\begin{code}
idBB = (abs x (bool ⇒ bool) (var x))
\end{code}

$$\text{idBBBB} = \lambda x:(bool\rightarrow bool)\rightarrow (bool\rightarrow bool). x$$.

\begin{code}
idBBBB = (abs x ((bool ⇒ bool) ⇒ (bool ⇒ bool)) (var x))
\end{code}

$$\text{k} = \lambda x:bool. \lambda y:bool. x$$.

\begin{code}
k = (abs x bool (abs y bool (var x)))
\end{code}

$$\text{notB} = \lambda x:bool. \text{if }x\text{ then }false\text{ else }true$$.

\begin{code}
notB = (abs x bool (if (var x) then false else true))
\end{code}

<div class="hidden">
\begin{code}
{-# DISPLAY abs 0 bool (var 0) = idB #-}
{-# DISPLAY abs 0 (bool ⇒ bool) (var 0) = idBB #-}
{-# DISPLAY abs 0 ((bool ⇒ bool) ⇒ (bool ⇒ bool)) (var 0) = idBBBB #-}
{-# DISPLAY abs 0 bool (abs y bool (var 0)) = k #-}
{-# DISPLAY abs 0 bool (if (var 0) then false else true) = notB #-}
\end{code}
</div>

## Operational Semantics

To define the small-step semantics of STLC terms, we begin,
as always, by defining the set of values.  Next, we define the
critical notions of _free variables_ and _substitution_, which are
used in the reduction rule for application expressions.  And
finally we give the small-step relation itself.

### Values

To define the values of the STLC, we have a few cases to consider.

First, for the boolean part of the language, the situation is
clear: $$true$$ and $$false$$ are the only values.  An $$\text{if}$$
expression is never a value.

Second, an application is clearly not a value: It represents a
function being invoked on some argument, which clearly still has
work left to do.

Third, for abstractions, we have a choice:

  - We can say that $$\lambda x:A. t$$ is a value only when $$t$$ is a
    value---i.e., only if the function's body has been
    reduced (as much as it can be without knowing what argument it
    is going to be applied to).

  - Or we can say that $$\lambda x:A. t$$ is always a value, no matter
    whether $$t$$ is one or not---in other words, we can say that
    reduction stops at abstractions.

Agda makes the first choice---for example,

\begin{code}
test_normalizeUnderLambda : (λ (x : ℕ) → 3 + 4) ≡ (λ (x : ℕ) → 7)
test_normalizeUnderLambda = refl
\end{code}

Most real-world functional programming languages make the second
choice---reduction of a function's body only begins when the
function is actually applied to an argument.  We also make the
second choice here.

\begin{code}
data Value : Term → Set where
  abs   : ∀ {x A t}
        → Value (abs x A t)
  true  : Value true
  false : Value false
\end{code}

Finally, we must consider what constitutes a _complete_ program.

Intuitively, a "complete program" must not refer to any undefined
variables.  We'll see shortly how to define the _free_ variables
in a STLC term.  A complete program is _closed_---that is, it
contains no free variables.

Having made the choice not to reduce under abstractions, we don't
need to worry about whether variables are values, since we'll
always be reducing programs "from the outside in," and that means
the small-step relation will always be working with closed terms.


### Substitution

Now we come to the heart of the STLC: the operation of
substituting one term for a variable in another term.  This
operation is used below to define the operational semantics of
function application, where we will need to substitute the
argument term for the function parameter in the function's body.
For example, we reduce

$$(\lambda x:bool. \text{if }x\text{ then }true\text{ else }x)\;false$$

to

$$\text{if }false\text{ then }true\text{ else }false$$

by substituting $$false$$ for the parameter $$x$$ in the body of the
function.

In general, we need to be able to substitute some given term $$s$$
for occurrences of some variable $$x$$ in another term $$t$$.  In
informal discussions, this is usually written $$[x:=s]t$$ and
pronounced "substitute $$x$$ with $$s$$ in $$t$$."

Here are some examples:

  - $$[x:=true](\text{if }x\text{ then }x\text{ else }false)$$
     yields $$\text{if }true\text{ then }true\text{ else }false$$

  - $$[x:=true]x$$
    yields $$true$$

  - $$[x:=true](\text{if }x\text{ then }x\text{ else }y)$$
    yields $$\text{if }true\text{ then }true\text{ else }y$$

  - $$[x:=true]y$$
    yields $$y$$

  - $$[x:=true]false$$
    yields $$false$$ (vacuous substitution)

  - $$[x:=true](\lambda y:bool. \text{if }y\text{ then }x\text{ else }false)$$
    yields $$\lambda y:bool. \text{if }y\text{ then }true\text{ else }false$$

  - $$[x:=true](\lambda y:bool. x)$$
    yields $$\lambda y:bool. true$$

  - $$[x:=true](\lambda y:bool. y)$$
    yields $$\lambda y:bool. y$$

  - $$[x:=true](\lambda x:bool. x)$$
    yields $$\lambda x:bool. x$$

The last example is very important: substituting $$x$$ with $$true$$ in
$$\lambda x:bool. x$$ does _not_ yield $$\lambda x:bool. true$$!  The reason for
this is that the $$x$$ in the body of $$\lambda x:bool. x$$ is _bound_ by the
abstraction: it is a new, local name that just happens to be
spelled the same as some global name $$x$$.

Here is the definition, informally...

$$
  \begin{aligned}
    &[x:=s]x                &&= s \\
    &[x:=s]y                &&= y \;\{\text{if }x\neq y\} \\
    &[x:=s](\lambda x:A. t) &&= \lambda x:A. t \\
    &[x:=s](\lambda y:A. t) &&= \lambda y:A. [x:=s]t \;\{\text{if }x\neq y\} \\
    &[x:=s](t1\;t2)         &&= ([x:=s]t1) ([x:=s]t2) \\
    &[x:=s]true             &&= true \\
    &[x:=s]false            &&= false \\
    &[x:=s](\text{if }t1\text{ then }t2\text{ else }t3) &&=
       \text{if }[x:=s]t1\text{ then }[x:=s]t2\text{ else }[x:=s]t3
  \end{aligned}
$$

... and formally:

\begin{code}
[_:=_]_ : Id -> Term -> Term -> Term
[ x := v ] (var y) with x ≟ y
... | yes x=y = v
... | no  x≠y = var y
[ x := v ] (app s t) = app ([ x := v ] s) ([ x := v ] t)
[ x := v ] (abs y A t) with x ≟ y
... | yes x=y = abs y A t
... | no  x≠y = abs y A ([ x := v ] t)
[ x := v ] true  = true
[ x := v ] false = false
[ x := v ] (if s then t else u) =
  if [ x := v ] s then [ x := v ] t else  [ x := v ] u
\end{code}

<div class="hidden">
\begin{code}
infix 9 [_:=_]_
\end{code}
</div>

_Technical note_: Substitution becomes trickier to define if we
consider the case where $$s$$, the term being substituted for a
variable in some other term, may itself contain free variables.
Since we are only interested here in defining the small-step relation
on closed terms (i.e., terms like $$\lambda x:bool. x$$ that include
binders for all of the variables they mention), we can avoid this
extra complexity here, but it must be dealt with when formalizing
richer languages.


#### Exercise: 3 stars (subst-correct)
The definition that we gave above defines substitution as a _function_.
Suppose, instead, we wanted to define substitution as an inductive _relation_.
We've begun the definition by providing the `data` header and
one of the constructors; your job is to fill in the rest of the constructors
and prove that the relation you've defined coincides with the function given
above.
\begin{code}
data [_:=_]_==>_ (x : Id) (s : Term) : Term -> Term -> Set where
  var1 : [ x := s ] (var x) ==> s
  {- FILL IN HERE -}
\end{code}

\begin{code}
postulate
  subst-correct : ∀ s x t t'
                → [ x := s ] t ≡ t'
                → [ x := s ] t ==> t'
\end{code}


### Reduction

The small-step reduction relation for STLC now follows the
same pattern as the ones we have seen before.  Intuitively, to
reduce a function application, we first reduce its left-hand
side (the function) until it becomes an abstraction; then we
reduce its right-hand side (the argument) until it is also a
value; and finally we substitute the argument for the bound
variable in the body of the abstraction.  This last rule, written
informally as

$$
(\lambda x : A . t) v \Longrightarrow [x:=v]t
$$

is traditionally called "beta-reduction".

$$
\begin{array}{cl}
  \frac{value(v)}{(\lambda x : A . t) v \Longrightarrow [x:=v]t}&(red)\\\\
  \frac{s \Longrightarrow s'}{s\;t \Longrightarrow s'\;t}&(app1)\\\\
  \frac{value(v)\quad t \Longrightarrow t'}{v\;t \Longrightarrow v\;t'}&(app2)
\end{array}
$$

... plus the usual rules for booleans:

$$
\begin{array}{cl}
  \frac{}{(\text{if }true\text{ then }t_1\text{ else }t_2) \Longrightarrow t_1}&(iftrue)\\\\
  \frac{}{(\text{if }false\text{ then }t_1\text{ else }t_2) \Longrightarrow t_2}&(iffalse)\\\\
  \frac{s \Longrightarrow s'}{\text{if }s\text{ then }t_1\text{ else }t_2
    \Longrightarrow \text{if }s\text{ then }t_1\text{ else }t_2}&(if)
\end{array}
$$

Formally:

\begin{code}
data _==>_ : Term → Term → Set where
  red     : ∀ {x A s t}
          → Value t
          → app (abs x A s) t ==> [ x := t ] s
  app1    : ∀ {s s' t}
          → s ==> s'
          → app s t ==> app s' t
  app2    : ∀ {s t t'}
          → Value s
          → t ==> t'
          → app s t ==> app s t'
  if      : ∀ {s s' t u}
          → s ==> s'
          → if s then t else u ==> if s' then t else u
  iftrue  : ∀ {s t}
          → if true then s else t ==> s
  iffalse : ∀ {s t}
          → if false then s else t ==> t
\end{code}

<div class="hidden">
\begin{code}
infix 1 _==>_
\end{code}
</div>

\begin{code}
data Multi (R : Term → Term → Set) : Term → Term → Set where
  refl : ∀ {x} -> Multi R x x
  step : ∀ {x y z} -> R x y -> Multi R y z -> Multi R x z
\end{code}

\begin{code}
_==>*_ : Term → Term → Set
_==>*_ = Multi _==>_
\end{code}

<div class="hidden">
\begin{code}
{-# DISPLAY Multi _==>_ = _==>*_ #-}
\end{code}
</div>

### Examples

Example:

$$((\lambda x:bool\rightarrow bool. x) (\lambda x:bool. x)) \Longrightarrow^* (\lambda x:bool. x)$$.

\begin{code}
step-example1 : (app idBB idB) ==>* idB
step-example1 = step (red abs)
              $ refl
\end{code}

Example:

$$(\lambda x:bool\rightarrow bool. x) \;((\lambda x:bool\rightarrow bool. x)\;(\lambda x:bool. x))) \Longrightarrow^* (\lambda x:bool. x)$$.

\begin{code}
step-example2 : (app idBB (app idBB idB)) ==>* idB
step-example2 = step (app2 abs (red abs))
              $ step (red abs)
              $ refl
\end{code}

Example:

$$((\lambda x:bool\rightarrow bool. x)\;(\lambda x:bool. \text{if }x\text{ then }false\text{ else }true))\;true\Longrightarrow^* false$$.

\begin{code}
step-example3 : (app (app idBB notB) true) ==>* false
step-example3 = step (app1 (red abs))
              $ step (red true)
              $ step iftrue
              $ refl
\end{code}

Example:

$$((\lambda x:bool\rightarrow bool. x)\;((\lambda x:bool. \text{if }x\text{ then }false\text{ else }true)\;true))\Longrightarrow^* false$$.

\begin{code}
step-example4 : (app idBB (app notB true)) ==>* false
step-example4 = step (app2 abs (red true))
              $ step (app2 abs iftrue)
              $ step (red false)
              $ refl
\end{code}

#### Exercise: 2 stars (step-example5)

\begin{code}
postulate
  step-example5 : (app (app idBBBB idBB) idB) ==>* idB
\end{code}

## Typing

Next we consider the typing relation of the STLC.

### Contexts

_Question_: What is the type of the term "$$x\;y$$"?

_Answer_: It depends on the types of $$x$$ and $$y$$!

I.e., in order to assign a type to a term, we need to know
what assumptions we should make about the types of its free
variables.

This leads us to a three-place _typing judgment_, informally
written $$\Gamma\vdash t : A$$, where $$\Gamma$$ is a
"typing context"---a mapping from variables to their types.

Informally, we'll write $$\Gamma , x:A$$ for "extend the partial function
$$\Gamma$$ to also map $$x$$ to $$A$$."  Formally, we use the function `_,_∶_`
(or "update") to add a binding to a context.

\begin{code}
Ctxt : Set
Ctxt = PartialMap Type

∅ : Ctxt
∅ = PartialMap.empty

_,_∶_ : Ctxt -> Id -> Type -> Ctxt
_,_∶_ = PartialMap.update
\end{code}

<div class="hidden">
\begin{code}
infixl 3 _,_∶_
\end{code}
</div>


### Typing Relation

$$
  \begin{array}{cl}
  \frac{\Gamma\;x = A}{\Gamma\vdash{x:A}}&(var)\\\\
  \frac{\Gamma,x:A\vdash t:B}{\Gamma\vdash (\lambda x:A.t) : A\rightarrow B}&(abs)\\\\
  \frac{\Gamma\vdash s:A\rightarrow B\quad\Gamma\vdash t:A}{\Gamma\vdash (s\;t) : B}&(app)\\\\
  \frac{}{\Gamma\vdash true : bool}&(true)\\\\
  \frac{}{\Gamma\vdash false : bool}&(true)\\\\
  \frac{\Gamma\vdash s:bool \quad \Gamma\vdash t1:A \quad \Gamma\vdash t2:A}{\Gamma\vdash\text{if }s\text{ then }t1\text{ else }t2 : A}&(if)
  \end{array}
$$

We can read the three-place relation $$\Gamma\vdash (t : A)$$ as:
"to the term $$t$$ we can assign the type $$A$$ using as types for
the free variables of $$t$$ the ones specified in the context
$$\Gamma$$."

\begin{code}
data _⊢_∶_ : Ctxt -> Term -> Type -> Set where
  var           : ∀ {Γ} x {A}
                → Γ x ≡ just A
                → Γ ⊢ var x ∶ A
  abs           : ∀ {Γ} {x} {A} {B} {s}
                → Γ , x ∶ A ⊢ s ∶ B
                → Γ ⊢ abs x A s ∶ A ⇒ B
  app           : ∀ {Γ} {A} {B} {s} {t}
                → Γ ⊢ s ∶ A ⇒ B
                → Γ ⊢ t ∶ A
                → Γ ⊢ app s t ∶ B
  true          : ∀ {Γ}
                → Γ ⊢ true  ∶ bool
  false         : ∀ {Γ}
                → Γ ⊢ false ∶ bool
  if_then_else_ : ∀ {Γ} {s} {t} {u} {A}
                → Γ ⊢ s ∶ bool
                → Γ ⊢ t ∶ A
                → Γ ⊢ u ∶ A
                → Γ ⊢ if s then t else u ∶ A
\end{code}

<div class="hidden">
\begin{code}
infix 1 _⊢_∶_
\end{code}
</div>


### Examples

\begin{code}
typing-example1 : ∅ ⊢ idB ∶ bool ⇒ bool
typing-example1 = abs (var x refl)
\end{code}

Another example:

$$\varnothing\vdash \lambda x:A. \lambda y:A\rightarrow A. y\;(y\;x) : A\rightarrow (A\rightarrow A)\rightarrow A$$.

\begin{code}
typing-example2 : ∅ ⊢
  (abs x bool
    (abs y (bool ⇒ bool)
      (app (var y)
        (app (var y) (var x)))))
  ∶ (bool ⇒ (bool ⇒ bool) ⇒ bool)
typing-example2 =
  (abs
    (abs
      (app (var y refl)
        (app (var y refl) (var x refl) ))))
\end{code}

#### Exercise: 2 stars (typing-example3)
Formally prove the following typing derivation holds:

$$\exists A, \varnothing\vdash \lambda x:bool\rightarrow B. \lambda y:bool\rightarrow bool. \lambda z:bool. y\;(x\;z) : A$$.

\begin{code}
postulate
  typing-example3 : ∃ λ A → ∅ ⊢
    (abs x (bool ⇒ bool)
      (abs y (bool ⇒ bool)
        (abs z bool
          (app (var y) (app (var x) (var z)))))) ∶ A
\end{code}

We can also show that terms are _not_ typable.  For example, let's
formally check that there is no typing derivation assigning a type
to the term $$\lambda x:bool. \lambda y:bool. x\;y$$---i.e.,


$$\nexists A, \varnothing\vdash \lambda x:bool. \lambda y:bool. x\;y : A$$.

\begin{code}
postulate
  typing-nonexample1 : ∄ λ A → ∅ ⊢
    (abs x bool
      (abs y bool
        (app (var x) (var y)))) ∶ A
\end{code}

#### Exercise: 3 stars, optional (typing-nonexample2)
Another nonexample:

$$\nexists A, \exists B, \varnothing\vdash \lambda x:A. x\;x : B$$.

\begin{code}
postulate
  typing-nonexample2 : ∄ λ A → ∃ λ B → ∅ ⊢
    (abs x B (app (var x) (var x))) ∶ A
\end{code}
