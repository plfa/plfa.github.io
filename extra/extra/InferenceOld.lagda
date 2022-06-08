---
title     : "Inference: Bidirectional type inference"
permalink : /Inference/
---

\begin{code}
module plfa.Inference where
\end{code}

So far in our development, type derivations for the corresponding
term have been provided by fiat.
In Chapter [Lambda]({{ site.baseurl }}{% link out/plfa/Lambda.md %})
type derivations were given separately from the term, while
in Chapter [DeBruijn]({{ site.baseurl }}{% link out/plfa/DeBruijn.md %})
the type derivation was inherently part of the term.

In practice, one often writes down a term with a few decorations and
applies an algorithm to _infer_ the corresponding type derivation.
Indeed, this is exactly what happens in Agda: we specify the types for
top-level function declarations, and the remaining type information is
inferred from this.  The style of inference used is descended from an
algorithm called _bidirectional_ type inference, which will be
presented in this chapter.

This chapter ties our previous developments together. We begin with
a term with some type annotations, quite close to the raw terms of
Chapter [Lambda]({{ site.baseurl }}{% link out/plfa/Lambda.md %}),
and from it we compute a term with inherent types, in the style of
Chapter [DeBruijn]({{ site.baseurl }}{% link out/plfa/DeBruijn.md %}).

## Introduction: Inference rules as algorithms {#algorithms}

In the calculus we have considered so far, a term may have more than
one type.  For example,

    (ƛ x ⇒ x) ⦂ (A ⇒ A)

for _every_ type `A`.  We start by considering a small language for
lambda terms where every term has a unique type.  All we need do
is decorate each abstraction term with the type of its argument.
This gives us the grammar:

    L, M, N ::=                         decorated terms
      x                                   variable
      ƛ x ⦂ A ⇒ N                         abstraction (decorated)
      L · M                               application

Each of the associated type rules can be read as an algorithm for
type checking.  For each typing judgment, we label each position
as either an _input_ or an _output_.

For the judgment

    Γ ∋ x ⦂ A

we take the context `Γ` and the variable `x` as inputs, and the
type `A` as output.  Consider the rules:

    ----------------- Z
    Γ , x ⦂ A ∋ x ⦂ A

    Γ ∋ y ⦂ B
    ----------------- S
    Γ , x ⦂ A ∋ y ⦂ B

From the inputs we can determine which rule applies: if the last
variable in the context matches the given variable then the first
rule applies, else the second.  (For de Bruijn indices, it is even
easier: zero matches the first rule and successor the second.)
For the first rule, the output type can be read off as the last
type in the input context. For the second rule, the inputs of the
conclusion determine the inputs of the hypothesis, and the ouptut
of the hypothesis determines the output of the conclusion.

For the judgment

    Γ ⊢ M ⦂ A

we take the context `Γ` and term `M` as inputs, and the type `A`
as ouput. Consider the rules:

    Γ ∋ x ⦂ A
    -----------
    Γ ⊢ ` x ⦂ A

    Γ , x ⦂ A ⊢ N ⦂ B
    ---------------------------
    Γ ⊢ (ƛ x ⦂ A ⇒ N) ⦂ (A ⇒ B)

    Γ ⊢ L ⦂ A ⇒ B
    Γ ⊢ M ⦂ A′
    A ≡ A′
    -------------
    Γ ⊢ L · M ⦂ B

The term input determines which rule applies: variables use the first
rule, abstractions the second, and applications the third.  In such a
situation, we say the rules are _syntax directed_.  For the
variable rule, the inputs of the conclusion determine the inputs of
the hypothesis, and the output of the hypothesis determines the output
of the conclusion.  Same for the abstraction rule — the bound variable
and argument type of the abstraction are carried into the context of
the hypothesis, and this is why we added the argument type to the
abstraction.  For the application rule, we add a third hypothesis to
check whether domain of the function matches the type of the argument;
this judgment is decidable when both types are given as inputs. The
inputs of the conclusion determine the inputs of the first two
hypotheses, the outputs of the first two hypotheses determine the
inputs of the third hypothesis, and the output of the first hypothesis
determines the output of the conclusion.

Converting the above to an algorithm is straightforwart, as is adding
naturals and fixpoint.  We omit the details.  Instead, we consider a
detailed description of an approach that requires less obtrusive
decoration.  The idea is to break the normal typing judgment into two
judgments, one that produces the type as an output (as above), and
another that takes it as an input.


## Synthesising and inheriting types

In addition to the lookup judgment for variables, which will remain
as before, we now have two judgments for the type of the term.

    Γ ⊢ M ↑ A
    Γ ⊢ M ↓ A

The first of these _synthesises_ the type of a term, as before,
while the second _inherits_ the type.  In the first, the context
and term are inputs and the type is an output, while in the
second, all three of the context, term, and type are inputs.

Which terms use synthesis and which inheritance?  Our approach will be
that the main term in a _deconstructor_ are typed via synthesis while
_constructors_ a typed via inheritance.  For instance, the function in
an application is typed via synthesis, but an abstraction is typed via
inheritance.  The inherited type in an abstraction term serves the
same purpose as the argument type decoration of the previous section.

Terms that deconstruct a value of a type always have a main term
(supplying an argument of the required type) and often have
side-terms.  For application, the main term supplies the function and
the side term supplies the argument.  For case terms, the main term
supplies a natural and the side terms are the two branches.  In a
deconstructor, the main term will be typed using synthesis but the
side terms will be typed using inheritance.  As we will see, this
leads naturally to an application as a whole being typed by synthesis,
while a case term as a whole will be typed by inheritance.
Variables are naturally typed by synthesis, since we can look up
the type in the input context.  Fixed points will be naturally
typed by inheritance.

In order to get a syntax-directed type system we break terms into two
kinds, `Term⁺` and `Term⁻, which are typed by synthesis and
inheritance, respectively.  At some points, we may expect a subterm to
be typed by synthesis when in fact it is typed by inheritance, or
vice-versa, and this gives rise to two new term forms.

For instance, we said above that the argument of an application is
typed by inheritance and that variables are typed by synthesis, giving
a mismatch if the argument of an application is a variable.  Hence, we
need a way to treat a synthesized term as if it is inherited.  We
introduce a new term form, `M ↑` for this purpose.  The typing judgment
checks that the inherited and synthesised types match.

Similarly, we said above that the function of an application is typed
by synthesis and that abstractions are typed by inheritance, giving a
mismatch if the function of an application is a variable.  Hence, we
need a way to treat an inherited term as if it is synthesised.  We
introduce a new term form `M ↓ A` for this purpose.  The typing
judgment returns `A` as the synthesized type of the term as a whole,
as well as using it as the inherited type for `M`.

The term form `M ↓ A` represents the only place terms need to
be decorated with types.  It only appears when switching from
synthesis to inheritance, that is, when a term that _deconstructs_
a value of a type contains a term that _constructs_ a value of a
type, in other words, a place where a β reduction will occur.
Typically, we will find that such declarations are only required
on top level declarations.

We can extract the grammar for terms from the above:

    L⁺, M⁺, N⁺ ::=                      terms with synthesized type
      x                                   variable
      L⁺ · M-                             application
      M⁻ ↓ A                              switch to inherited

    L⁻, M⁻, N⁻ ::=                      terms with inherited type
      ƛ x ⇒ N                             abstraction
      `zero                               zero
      `suc M⁻                             successor
      case L⁺ [zero⇒ M⁻ |suc x ⇒ N⁻ ]     case
      μ x ⇒ N                             fixpoint
      M ↑                                 switch to synthesized

With the grammar in hand, we can begin the formal development.


## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; foldr; filter; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.String using (String; _≟_; _++_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)

pattern [_]       w        =  w ∷ []
pattern [_,_]     w x      =  w ∷ x ∷ []
pattern [_,_,_]   w x y    =  w ∷ x ∷ y ∷ []
pattern [_,_,_,_] w x y z  =  w ∷ x ∷ y ∷ z ∷ []
\end{code}

Once we have a type derivation, it will be easy to construct
from it the inherently typed representation.  In order that we
can compare with our previous development, we import
module `pfla.DeBruijn`.

\begin{code}
open import plfa.DeBruijn as DB using (Type; `ℕ; _⇒_)
\end{code}

The phrase `as DB` allows us to refer to definitions
from that module as, for instance, `DB._⊢_`, which is
invoked as `Γ DB.⊢ A`, where `Γ` has type
`DB.Context` and `A` has type `DB.Type`.  We also import
`Type` and its constructors directly, so the latter may
also be referred to as just `Type`.


## Syntax

First, we get all our infix declarations out of the way.
We list separately operators for judgments and terms.

\begin{code}
infix   4  _∋_⦂_
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_⦂_

infix   5  ƛ_⇒_
infix   5  μ_⇒_
infix   6  _↑
infix   6  _↓_
infixl  7  _·_
infix   8  `suc_
infix   9  `_
\end{code}

Identifiers are as before.
\begin{code}
Id : Set
Id = String
\end{code}

And so are contexts. (Recall that `Type` is imported from
[DeBruijn]({{ site.baseurl }}{% link out/plfa/DeBruijn.md %}).)
\begin{code}
data Context : Set where
  ∅      : Context
  _,_⦂_ : Context → Id → Type → Context
\end{code}

The syntax of terms is defined by mutual recursion.
We use `Term⁺` and `Term⁻`
for terms with synthesized and inherited types, respectively.
Note the inclusion of the switching forms,
`M ↓ A` and `M ↑`.
\begin{code}
data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  `_                        : Id → Term⁺
  _·_                       : Term⁺ → Term⁻ → Term⁺
  _↓_                       : Term⁻ → Type → Term⁺

data Term⁻ where
  ƛ_⇒_                     : Id → Term⁻ → Term⁻
  `zero                    : Term⁻
  `suc_                    : Term⁻ → Term⁻
  `case_[zero⇒_|suc_⇒_]    : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
  μ_⇒_                     : Id → Term⁻ → Term⁻
  _↑                       : Term⁺ → Term⁻
\end{code}
The choice as to whether each term is synthesized or
inherited follows the discussion above, and can be read
off from the preceding (informal) grammar.  Main terms in
deconstructors synthesise, constructors and side terms
in deconstructors inherit.

## Example terms

We can recreate the examples from preceding chapters.
First, computing two plus two on naturals.
\begin{code}
two : Term⁻
two = `suc (`suc `zero)

plus : Term⁺
plus = (μ "p" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          `case (` "m") [zero⇒ ` "n" ↑
                        |suc "m" ⇒ `suc (` "p" · (` "m" ↑) · (` "n" ↑) ↑) ])
            ↓ `ℕ ⇒ `ℕ ⇒ `ℕ

2+2 : Term⁺
2+2 = plus · two · two
\end{code}
The only change is to decorate with down and up arrows as required.
The only type decoration required is for `plus`.

Next, computing two plus two with Church numerals.
\begin{code}
Ch : Type
Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

twoᶜ : Term⁻
twoᶜ = (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)

plusᶜ : Term⁺
plusᶜ = (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
           ` "m" · (` "s" ↑) · (` "n" · (` "s" ↑) · (` "z" ↑) ↑) ↑)
             ↓ Ch ⇒ Ch ⇒ Ch

sucᶜ : Term⁻
sucᶜ = ƛ "x" ⇒ `suc (` "x" ↑)

2+2ᶜ : Term⁺
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
\end{code}
The only type decoration required is for `plusᶜ`.  One is not even
required for `sucᶜ`, which inherits its type as an argument of `plusᶜ`.

## Bidirectional type checking

The typing rules for variables are as in
[Lambda]({{ site.baseurl }}{% link out/plfa/Lambda.md %}).
\begin{code}
data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      --------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      -----------------
    → Γ , y ⦂ B ∋ x ⦂ A
\end{code}

As with syntax, the judgments for synthesizing
and inheriting types are mutually recursive.
\begin{code}
data _⊢_↑_ : Context → Term⁺ → Type → Set
data _⊢_↓_ : Context → Term⁻ → Type → Set

data _⊢_↑_ where

  Ax : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ↑ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑ A ⇒ B
    → Γ ⊢ M ↓ A
      -------------
    → Γ ⊢ L · M ↑ B

  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
      ---------------
    → Γ ⊢ (M ↓ A) ↑ A

data _⊢_↓_ where

  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ↓ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ↓ A ⇒ B

  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ↓ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ↓ `ℕ
      ---------------
    → Γ ⊢ `suc M ↓ `ℕ

  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ↑ `ℕ
    → Γ ⊢ M ↓ A
    → Γ , x ⦂ `ℕ ⊢ N ↓ A
      -------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x ⦂ A ⊢ N ↓ A
      -----------------
    → Γ ⊢ μ x ⇒ N ↓ A

  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≡ B
      -------------
    → Γ ⊢ (M ↑) ↓ B
\end{code}
We follow the same convention as
Chapter [Lambda]({{ site.baseurl }}{% link out/plfa/Lambda.md %}),
prefacing the constructor with `⊢` to derive the name of the
corresponding type rule.

The most interesting rules are those for `⊢↑` and `⊢↓`.
The former both passes the type decoration as the inherited type and returns
it as the synthesised type.  The latter takes the synthesised type and the
inherited type and confirms they are identical.  (It should remind you of
the equality test in the application rule in the first
[section]({{ site.baseurl }}{% link out/plfa/Inference.md %}/#algorithms).)


## Type equality

The rule for `M ↑` requires the ability to decide whether two types
are equal.  It is straightforward to code.
\begin{code}
_≟Tp_ : (A B : Type) → Dec (A ≡ B)
`ℕ      ≟Tp `ℕ              =  yes refl
`ℕ      ≟Tp (A ⇒ B)         =  no λ()
(A ⇒ B) ≟Tp `ℕ              =  no λ()
(A ⇒ B) ≟Tp (A′ ⇒ B′)
  with A ≟Tp A′ | B ≟Tp B′
...  | no A≢    | _         =  no λ{refl → A≢ refl}
...  | yes _    | no B≢     =  no λ{refl → B≢ refl}
...  | yes refl | yes refl  =  yes refl
\end{code}


## Type inference monad

One construct you will find in the functional programmer's toolbox
is the _monad_, which can describe error handling, state, and
many other computational effects.  Here we introduce a monad to
manage error messages in our inferencer.

Type inference will either yield a value (such as a synthesized type)
or an error message (for instance, when inherited and synthesized
types differ).  An error message is given by a string.
\begin{code}
Message : Set
Message = String
\end{code}
The type `I A` represents the result of inference, where `A` is an
arbitrary Agda set representing the type of the result returned;
in our case, we will return evidence for type judgments.
Note here `A` ranges over
Agda sets rather than types of our target lambda calculus.
\begin{code}
data I (A : Set) : Set where
  error⁺  : Message → Term⁺ → List Type → I A
  error⁻  : Message → Term⁻ → List Type → I A
  return  : A → I A
\end{code}
There are three possible constructors, two for errors and one to
return a value.  An error also takes a message, a term, and a list of
types relevant to the error; there is one variant for each sort of
term.  Return embeds values of type `A` into the type `I A`.

We need a way to compose functions that may return error messages,
and monads provide the required structure.
A monad is equipped with an operation, usually written `_>>=_`
and pronounced _bind_.
\begin{code}
_>>=_ : ∀ {A B : Set} → I A → (A → I B) → I B
error⁺ msg M As >>= k  =  error⁺ msg M As
error⁻ msg M As >>= k  =  error⁻ msg M As
return x        >>= k  =  k x
\end{code}
If the left argument raises an error, the bind term raises
the same error.  If the right argument returns a value, the
bind term applies its left argument to that value.
There is a conflict in our conventions: here `A` ranges over Agda
sets, while `As` ranges over types of our target lambda calculus.

A monad is a bit like a monoid, in that it should satisfy something
akin to a left and right identity law and an associativity law.  The
role of the identity is played by `return`.  In our case,
all three laws are trivial to prove.
\begin{code}
identityˡ : ∀ {A B : Set} (x : A) (k : A → I B) → return x >>= k ≡ k x
identityˡ x k = refl

identityʳ : ∀ {A B : Set} (m : I A) → m >>= (λ x → return x) ≡ m
identityʳ (error⁺ _ _ _)  =  refl
identityʳ (error⁻ _ _ _)  =  refl
identityʳ (return _)      =  refl

assoc : ∀ {X Y Z : Set} (m : I X) (k : X → I Y) (h : Y → I Z) →
  (m >>= λ x → k x) >>= (λ y → h y)  ≡  m >>= (λ x → k x >>= (λ y → h y))
assoc (error⁺ _ _ _)  k h  =  refl
assoc (error⁻ _ _ _)  k h  =  refl
assoc (return _)      k h  =  refl
\end{code}
The left-hand side of the associativity law can be abbreviated to
`(m >>= k) >>= h`, but it is written as above to make clear that
the law is about re-arranging parentheses.

## Syntactic sugar for monads

Agda has built-in syntax to support the use of monads, which
translates into applications of the binding operator `_>>=_`.  Such
translation of one construct into another is referred to as _syntactic
sugar_, and we will apply it to sweeten our subsequent presentation.

Writing

    do x ← M
       N

translates to

    M >>= λ x → N

Here `x` is an Agda variable and `M` and `N` are terms of Agda
(rather than of our target lambda calculus).  Applying the notations
we have learned to Agda itself, we can write

    Γ ⊢ M : I A
    Γ , x : A ⊢ N : I B
    -------------------
    Γ ⊢ (do x ← M
            N)    : I B

That is, term `M` has type `I A`, variable `x` has type `A`, and term
`N` has type `I B` and may contain `x` as a free variable, and the
whole term has type `I B`.  One can read this as follows:
Evaluate `M`; if it fails, yield the error message; if it succeeds,
bind `x` to the value returned and evaluate `N`.

Similarly, writing

    do x ← L
       y ← M
       N

translates to

    L >>= λ x → (M >>= λ y → N)

If `x` does not appear free in `N`, then by the associative law we
can parenthesise either way; though `x` may appear free in `N`.
We can describe the types as before:

    Γ ⊢ L : I A
    Γ , x : A ⊢ M : I B
    Γ , x : A , y : B ⊢ N : I C
    ---------------------------
    Γ ⊢ (do x ← L
            y ← M
            N)    : I C

We can read this as: Evaluate `L`; if it fails, yield the error
message; if it succeeds, bind `x` the the value returned and
evaluate `M`; if it fails, yield the error message; if it
succeeds, bind `y` to the value returned and evaluate `N`.

Additionally, writing

    do P ← L
         where Q → M
       N

translates to

    L >>= λ{ P → N ; Q → M }


where `P`, `Q` are Agda patterns, and `L`, `M`, `N` are Agda terms.
Extending our notation to allow a pattern to the left of a turnstyle, we have:

    Γ ⊢ L : I A
    Γ , P : A ⊢ N : I B
    Γ , Q : A ⊢ M : I B
    ---------------------------
    Γ ⊢ (do P ← L
              where Q → M
            N)            : I B

One can read this form as follows: Evaluate `M`; if it fails, yield
the error message; if it succeeds, match `P` to the value returned and
evaluate `N` (which may contain variables matched by `P`); otherwise
match `Q` to the value returned and evaluate `M` (which may contain
variables matched by `Q`); one of `P` and `Q` must match.

The notations extend to any number of bindings or patterns. Thus,

    do x₁ ← M₁
       ...
       xₙ ← Mₙ
       N

translates to

    M₁ >>= (λ x₁ → ... Mₙ >>= (λ xₙ → N)...)

and

    do P ← L
         where Q₁ → M₁
               ...
               Qₙ → Mₙ
       N

translates to

    L >>= λ{ P → N ; Q₁ → M₁ ; ... ; Qₙ → Mₙ }

We will apply this sugar to sweeten our subsequent presentation.


## Lookup type of a variable in the context

Given a context `Γ` and a variable `x`, we return a type `A` and
evidence that `Γ ∋ x ⦂ A`.  If `x` does not appear in `Γ`, then
we raise an error.
\begin{code}
lookup : ∀ (Γ : Context) (x : Id) → I (∃[ A ](Γ ∋ x ⦂ A))
lookup ∅ x  =
  error⁺ "variable not bound" (` x) []
lookup (Γ , y ⦂ B) x with x ≟ y
... | yes refl =
  return ⟨ B , Z ⟩
... | no x≢y =
  do ⟨ A , ⊢x ⟩ ← lookup Γ x
     return ⟨ A , S x≢y ⊢x ⟩
\end{code}
There are three cases.

* If the context is empty, we raise an error.

* If the variable appears in the most recent binding, we
  return its corresponding type.

* If the variable does not appear in the most recent binding,
  we recurse.

## Synthesize and inherit types

The table has been set, the starters consumed, and we are ready
for the main course.  We have two mutually recursive functions,
one for synthesis and one for inheritance.  Synthesis is given
a context `Γ` and a synthesis term `M` and
returns a type `A` and evidence that `Γ ⊢ M ↑ A`.
Inheritance is given a context `Γ`, an inheritance term `M`,
and a type `A` and reuturns evidence that `Γ ⊢ M ↓ A`.
An error is raised when appropriate.
\begin{code}
synthesize : ∀ (Γ : Context) (M : Term⁺) → I (∃[ A ](Γ ⊢ M ↑ A))
inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type) → I (Γ ⊢ M ↓ A)
\end{code}

We first consider the code for synthesis.
\begin{code}
synthesize Γ (` x) =
  do ⟨ A , ⊢x ⟩ ← lookup Γ x
     return ⟨ A , Ax ⊢x ⟩
synthesize Γ (L · M) =
  do ⟨ A ⇒ B , ⊢L ⟩ ← synthesize Γ L
       where ⟨ `ℕ , _ ⟩ → error⁺ "must apply function" (L · M) []
     ⊢M ← inherit Γ M A
     return ⟨ B , ⊢L · ⊢M ⟩
synthesize Γ (M ↓ A) =
  do ⊢M ← inherit Γ M A
     return ⟨ A , ⊢↓ ⊢M ⟩
\end{code}
There are three cases.

* If the term is a variable, we use lookup as defined above.

* If the term is an application, we recurse to synthesize the type of
  the function.  We check that the synthesied type is a function of
  the form `A ⇒ B`.  If it is not (e.g., it is of type `` `ℕ ``), then
  we report an error.  The argument is typed by inheriting `A`, and
  type `B` is returned as the synthesised type of the term as a whole.

* If the term switches from synthesized to inherited, then the type
  decoration `A` in the contained term is typed by inheriting `A`, and
  `A` is also returned as the synthesized type of the term as a whole.

We next consider the code for inheritance.
\begin{code}
inherit Γ (ƛ x ⇒ N) (A ⇒ B) =
  do ⊢N ← inherit (Γ , x ⦂ A) N B
     return (⊢ƛ ⊢N)
inherit Γ (ƛ x ⇒ N) `ℕ =
  error⁻ "lambda cannot be of type natural" (ƛ x ⇒ N) []
inherit Γ `zero `ℕ =
  return ⊢zero
inherit Γ `zero (A ⇒ B) =
  error⁻ "zero cannot be function" `zero [ A ⇒ B ]
inherit Γ (`suc M) `ℕ =
  do ⊢M ← inherit Γ M `ℕ
     return (⊢suc ⊢M)
inherit Γ (`suc M) (A ⇒ B) =
  error⁻ "suc cannot be function" (`suc M) [ A ⇒ B ]
inherit Γ (`case L [zero⇒ M |suc x ⇒ N ]) A =
  do ⟨ `ℕ , ⊢L ⟩ ← synthesize Γ L
       where ⟨ B ⇒ C , _ ⟩ → error⁻ "cannot case on function"
                                    (`case L [zero⇒ M |suc x ⇒ N ])
                                    [ B ⇒ C ]
     ⊢M ← inherit Γ M A
     ⊢N ← inherit (Γ , x ⦂ `ℕ) N A
     return (⊢case ⊢L ⊢M ⊢N)
inherit Γ (μ x ⇒ M) A =
  do ⊢M ← inherit (Γ , x ⦂ A) M A
     return (⊢μ ⊢M)
inherit Γ (M ↑) B =
  do ⟨ A , ⊢M ⟩ ← synthesize Γ M
     yes A≡B ← return (A ≟Tp B)
       where no _ → error⁻ "inheritance and synthesis conflict" (M ↑) [ A , B ]
     return (⊢↑ ⊢M A≡B)
\end{code}
There are nine cases.  We consider those for abstraction
and for switching from inherited to synthesized.

* If the term is an abstraction and the inherited type is of the form `A ⇒ B`
  then we extend the context by giving the variable type `A` and
  recuse to type the body by inheriting type `B`.

* If the term is an abstraction and the inherited type is not a function
  (e.g., of the form `` `ℕ ``), then we report an error.

* If the term switches from inherited to synthesised, then
  we synthesise the type of the contained term and compare it
  to the inherited type. If they are not equal, we raise an error.

The remaining cases are similar, and their code can pretty much be
read directly from the corresponding typing rules.

## Testing the example terms

First, we copy a function introduced earlier that makes it easy to
compute the evidence that two variable names are distinct.
\begin{code}
_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y  with x ≟ y
...       | no  x≢y  =  x≢y
...       | yes _    =  ⊥-elim impossible
  where postulate impossible : ⊥
\end{code}

Here is the result of typing two plus two on naturals.
\begin{code}
⊢2+2 : ∅ ⊢ 2+2 ↑ `ℕ
⊢2+2 =
  (⊢↓
   (⊢μ
    (⊢ƛ
     (⊢ƛ
      (⊢case (Ax (S ("m" ≠ "n") Z)) (⊢↑ (Ax Z) refl)
       (⊢suc
        (⊢↑
         (Ax
          (S ("p" ≠ "m")
           (S ("p" ≠ "n")
            (S ("p" ≠ "m") Z)))
          · ⊢↑ (Ax Z) refl
          · ⊢↑ (Ax (S ("n" ≠ "m") Z)) refl)
         refl))))))
   · ⊢suc (⊢suc ⊢zero)
   · ⊢suc (⊢suc ⊢zero))
\end{code}
We confirm that synthesis on the relevant term returns
natural as the type and the above derivation.
\begin{code}
_ : synthesize ∅ 2+2 ≡ return ⟨ `ℕ , ⊢2+2 ⟩
_ = refl
\end{code}
Indeed, the above derivation was computed by evaluating the
term on the left, and editing.  The only editing required is to
replace Agda's representation of the evidence that two strings are
unequal (which it can print not read) by equivalent calls to `≠`.

Here is the result of typing two plus two with Church numerals.
\begin{code}
⊢2+2ᶜ : ∅ ⊢ 2+2ᶜ ↑ `ℕ
⊢2+2ᶜ =
  ⊢↓
  (⊢ƛ
   (⊢ƛ
    (⊢ƛ
     (⊢ƛ
      (⊢↑
       (Ax
        (S ("m" ≠ "z")
         (S ("m" ≠ "s")
          (S ("m" ≠ "n") Z)))
        · ⊢↑ (Ax (S ("s" ≠ "z") Z)) refl
        ·
        ⊢↑
        (Ax
         (S ("n" ≠ "z")
          (S ("n" ≠ "s") Z))
         · ⊢↑ (Ax (S ("s" ≠ "z") Z)) refl
         · ⊢↑ (Ax Z) refl)
        refl)
       refl)))))
  ·
  ⊢ƛ
  (⊢ƛ
   (⊢↑
    (Ax (S ("s" ≠ "z") Z) ·
     ⊢↑ (Ax (S ("s" ≠ "z") Z) · ⊢↑ (Ax Z) refl)
     refl)
    refl))
  ·
  ⊢ƛ
  (⊢ƛ
   (⊢↑
    (Ax (S ("s" ≠ "z") Z) ·
     ⊢↑ (Ax (S ("s" ≠ "z") Z) · ⊢↑ (Ax Z) refl)
     refl)
    refl))
  · ⊢ƛ (⊢suc (⊢↑ (Ax Z) refl))
  · ⊢zero
\end{code}
We confirm that synthesis on the relevant term returns
natural as the type and the above derivation.
\begin{code}
_ : synthesize ∅ 2+2ᶜ ≡ return ⟨ `ℕ , ⊢2+2ᶜ ⟩
_ = refl
\end{code}
Again, the above derivation was computed by evaluating the
term on the left, and editing.

## Testing the error cases

It is important not just to check that code works as intended,
but also that it fails as intended.  Here is one test case to
exercise each of the possible error messages.
\begin{code}
_ : synthesize ∅ ((ƛ "x" ⇒ ` "y" ↑) ↓ (`ℕ ⇒ `ℕ)) ≡
  error⁺ "variable not bound" (` "y") []
_ = refl

_ : synthesize ∅ ((two ↓ `ℕ) · two) ≡
  error⁺ "must apply function"
    ((`suc (`suc `zero) ↓ `ℕ) · `suc (`suc `zero)) []
_ = refl

_ : synthesize ∅ (twoᶜ ↓ `ℕ) ≡
  error⁻ "lambda cannot be of type natural"
    (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)) []
_ = refl

_ : synthesize ∅ (`zero ↓ `ℕ ⇒ `ℕ) ≡
  error⁻ "zero cannot be function" `zero [ `ℕ ⇒ `ℕ ]
_ = refl

_ : synthesize ∅ (two ↓ `ℕ ⇒ `ℕ) ≡
  error⁻ "suc cannot be function" (`suc (`suc `zero)) [ `ℕ ⇒ `ℕ ]
_ = refl

_ : synthesize ∅
      ((`case (twoᶜ ↓ Ch) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡
  error⁻ "cannot case on function"
    `case (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑))
          ↓ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ]
    [ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ]
_ = refl

_ : synthesize ∅ (((ƛ "x" ⇒ ` "x" ↑) ↓ `ℕ ⇒ (`ℕ ⇒ `ℕ))) ≡
  error⁻ "inheritance and synthesis conflict" (` "x" ↑) [ `ℕ , `ℕ ⇒ `ℕ ]
_ = refl
\end{code}


## Erasure

From the evidence that a decorated term has the correct type it is
easy to extract the corresponding inherently typed term.  We use the
name `DB` to refer to the code in
Chapter [DeBruijn]({{ site.baseurl }}{% link out/plfa/DeBruijn.md %}).
It is easy to define an _erasure_ function that takes evidence of a
type judgment into the corresponding inherently typed term.

First, we give code to erase a context.
\begin{code}
∥_∥Γ : Context → DB.Context
∥ ∅ ∥Γ = DB.∅
∥ Γ , x ⦂ A ∥Γ = ∥ Γ ∥Γ DB., A
\end{code}
It simply drops the variable names.

Next, we give code to erase a lookup judgment.
\begin{code}
∥_∥∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ∥ Γ ∥Γ DB.∋ A
∥ Z ∥∋ =  DB.Z
∥ S x≢ ⊢x ∥∋ =  DB.S ∥ ⊢x ∥∋
\end{code}
It just drops the evidence that variable names are distinct.

Finally, we give the code to erase a typing judgment.
Just as there are two mutually recursive typing judgments,
there are two mutually recursive erasure functions.
\begin{code}
∥_∥⁺ : ∀ {Γ M A} → Γ ⊢ M ↑ A → ∥ Γ ∥Γ DB.⊢ A
∥_∥⁻ : ∀ {Γ M A} → Γ ⊢ M ↓ A → ∥ Γ ∥Γ DB.⊢ A

∥ Ax ⊢x ∥⁺ =  DB.` ∥ ⊢x ∥∋
∥ ⊢L · ⊢M ∥⁺ =  ∥ ⊢L ∥⁺ DB.· ∥ ⊢M ∥⁻
∥ ⊢↓ ⊢M ∥⁺ =  ∥ ⊢M ∥⁻

∥ ⊢ƛ ⊢N ∥⁻ =  DB.ƛ ∥ ⊢N ∥⁻
∥ ⊢zero ∥⁻ =  DB.`zero
∥ ⊢suc ⊢M ∥⁻ =  DB.`suc ∥ ⊢M ∥⁻
∥ ⊢case ⊢L ⊢M ⊢N ∥⁻ =  DB.case ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁻ ∥ ⊢N ∥⁻
∥ ⊢μ ⊢M ∥⁻ =  DB.μ ∥ ⊢M ∥⁻
∥ ⊢↑ ⊢M refl ∥⁻ =  ∥ ⊢M ∥⁺
\end{code}
Erasure replaces constructors for each typing judgment
by the corresponding term constructor from `DB`.  The
constructors that correspond to switching from synthesized
to inherited or vice versa are dropped.

We confirm that the erasure of the type derivations in
this chapter yield the corresponding inherently typed terms
from the earlier chapter.
\begin{code}
_ : ∥ ⊢2+2 ∥⁺ ≡ DB.2+2
_ = refl

_ : ∥ ⊢2+2ᶜ ∥⁺ ≡ DB.2+2ᶜ
_ = refl
\end{code}
Thus, we have confirmed that bidirectional type inference to
convert decorated versions of the lambda terms from
Chapter [Lambda]({{ site.baseurl }}{% link out/plfa/Lambda.md %})
to the inherently typed terms of
Chapter [DeBruijn]({{ site.baseurl }}{% link out/plfa/DeBruijn.md %}).

#### Exercise (`decoration`)

Extend bidirectional inference to include each of the constructs in
Chapter [More]({{ site.baseurl }}{% link out/plfa/More.md %}).


## Bidirectional inference in Agda

Agda itself uses bidirectional inference.  This explains why
constructors can be overloaded while other defined names cannot — here
by _overloaded_ we mean that the same name can be used for
constructors of different types.  Constructors are typed by
inheritance, and so the name is available when resolving the
constructor, whereas variables are typed by synthesis, and so each
variable must have a unique type.


## Unicode

This chapter uses the following unicode

    ↓  U+2193:  DOWNWARDS ARROW (\d)
    ↑  U+2191:  UPWARDS ARROW (\u)
    ←  U+2190:  LEFTWARDS ARROW (\l)
    ∥  U+2225:  PARALLEL TO (\||)
