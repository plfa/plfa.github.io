---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It embodies the concept of
_functional abstraction_, which shows up in almsot every programming
language in some form (as functions, procedures, or methods).
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has just the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations;
we will be slightly more pragmatic and choose booleans as our base type.

This chapter formalises the STLC (syntax, small-step semantics, and typing rules),
and the next chapter reviews its main properties (progress and preservation).
The new technical challenges arise from the mechanisms of
_variable binding_ and _substitution_.

We've already seen how to formalize a language with
variables ([Imp]({{ "Imp" | relative_url }})).
There, however, the variables were all global.
In the STLC, we need to handle the variables that name the
parameters to functions, and these are _bound_ variables.
Moreover, instead of just looking up variables in a global store,
we'll need to reduce function applications by _substituting_
arguments for parameters in function bodies.

We choose booleans as our base type for simplicity.  At the end of the
chapter we'll see how to add numbers as a base type, and in later
chapters we'll enrich STLC with useful constructs like pairs, sums,
lists, records, subtyping, and mutable state.

## Imports

\begin{code}
open import Maps using (Id; id; _≟_; PartialMap; module PartialMap)
open PartialMap using (∅) renaming (_,_↦_ to _,_∶_)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
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

    A, B, C ::=
      A ⇒ B   -- functions
      𝔹        -- booleans

And here it is formalised in Agda.

\begin{code}
infixr 20 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  𝔹 : Type
\end{code}

Terms have six constructs. Three are for the core lambda calculus:
  * Variables, `` ` x ``
  * Abstractions, `λ[ x ∶ A ] N`
  * Applications, `L · M`
and three are for the base type, booleans:
  * True, `true`
  * False, `false`
  * Conditions, `if L then M else N`
Abstraction is also called lambda abstraction, and is the construct
from which the calculus takes its name. 

With the exception of variables, each construct either constructs
a value of a given type (abstractions yield functions, true and
false yield booleans) or deconstructs it (applications use functions,
conditionals use booleans). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in BNF.

    L, M, N ::= ` x | λ[ x ∶ A ] N 




\begin{code}
infixl 20 _·_
infix  15 λ[_∶_]_
infix  15 if_then_else_

data Term : Set where
  ` : Id → Term
  λ[_∶_]_ : Id → Type → Term → Term
  _·_ : Term → Term → Term
  true : Term
  false : Term
  if_then_else_ : Term → Term → Term → Term
\end{code}

Each type introduces its own constructs, which come in pairs,
one to introduce (or construct) values of the type, and one to eliminate
(or deconstruct) them.

CONTINUE FROM HERE



Example terms.
\begin{code}
f x : Id
f  =  id 0
x  =  id 1

not two : Term 
not =  λ[ x ∶ 𝔹 ] (if ` x then false else true)
two =  λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x)
\end{code}

## Values

\begin{code}
data Value : Term → Set where
  value-λ     : ∀ {x A N} → Value (λ[ x ∶ A ] N)
  value-true  : Value true
  value-false : Value false
\end{code}

## Substitution

\begin{code}
_[_:=_] : Term → Id → Term → Term
(` x′) [ x := V ] with x ≟ x′
... | yes _ = V
... | no  _ = ` x′
(λ[ x′ ∶ A′ ] N′) [ x := V ] with x ≟ x′
... | yes _ = λ[ x′ ∶ A′ ] N′
... | no  _ = λ[ x′ ∶ A′ ] (N′ [ x := V ])
(L′ · M′) [ x := V ] =  (L′ [ x := V ]) · (M′ [ x := V ])
(true) [ x := V ] = true
(false) [ x := V ] = false
(if L′ then M′ else N′) [ x := V ] = if (L′ [ x := V ]) then (M′ [ x := V ]) else (N′ [ x := V ])
\end{code}

## Reduction rules

\begin{code}
infix 10 _⟹_ 

data _⟹_ : Term → Term → Set where
  βλ· : ∀ {x A N V} → Value V →
    (λ[ x ∶ A ] N) · V ⟹ N [ x := V ]
  ξ·₁ : ∀ {L L′ M} →
    L ⟹ L′ →
    L · M ⟹ L′ · M
  ξ·₂ : ∀ {V M M′} →
    Value V →
    M ⟹ M′ →
    V · M ⟹ V · M′
  βif-true : ∀ {M N} →
    if true then M else N ⟹ M
  βif-false : ∀ {M N} →
    if false then M else N ⟹ N
  ξif : ∀ {L L′ M N} →
    L ⟹ L′ →    
    if L then M else N ⟹ if L′ then M else N
\end{code}

## Reflexive and transitive closure


\begin{code}
infix 10 _⟹*_ 
infixr 2 _⟹⟨_⟩_
infix  3 _∎

data _⟹*_ : Term → Term → Set where
  _∎ : ∀ M → M ⟹* M
  _⟹⟨_⟩_ : ∀ L {M N} → L ⟹ M → M ⟹* N → L ⟹* N  

reduction₁ : not · true ⟹* false
reduction₁ =
    not · true
  ⟹⟨ βλ· value-true ⟩
    if true then false else true
  ⟹⟨ βif-true ⟩
    false
  ∎

reduction₂ : two · not · true ⟹* true
reduction₂ =
    two · not · true
  ⟹⟨ ξ·₁ (βλ· value-λ) ⟩
    (λ[ x ∶ 𝔹 ] not · (not · ` x)) · true
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



## Type rules

\begin{code}
Context : Set
Context = PartialMap Type

infix 10 _⊢_∶_

data _⊢_∶_ : Context → Term → Type → Set where
  Ax : ∀ {Γ x A} →
    Γ x ≡ just A →
    Γ ⊢ ` x ∶ A
  ⇒-I : ∀ {Γ x N A B} →
    Γ , x ∶ A ⊢ N ∶ B →
    Γ ⊢ λ[ x ∶ A ] N ∶ A ⇒ B
  ⇒-E : ∀ {Γ L M A B} →
    Γ ⊢ L ∶ A ⇒ B →
    Γ ⊢ M ∶ A →
    Γ ⊢ L · M ∶ B
  𝔹-I₁ : ∀ {Γ} →
    Γ ⊢ true ∶ 𝔹
  𝔹-I₂ : ∀ {Γ} →
    Γ ⊢ false ∶ 𝔹
  𝔹-E : ∀ {Γ L M N A} →
    Γ ⊢ L ∶ 𝔹 →
    Γ ⊢ M ∶ A →
    Γ ⊢ N ∶ A →
    Γ ⊢ if L then M else N ∶ A    
\end{code}

## Example type derivations

\begin{code}
typing₁ : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹
typing₁ = ⇒-I (𝔹-E (Ax refl) 𝔹-I₂ 𝔹-I₁)

typing₂ : ∅ ⊢ two ∶ (𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹
typing₂ = ⇒-I (⇒-I (⇒-E (Ax refl) (⇒-E (Ax refl) (Ax refl))))
\end{code}

Construction of a type derivation is best done interactively.
We start with the declaration:

    typing₁ : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹
    typing₁ = ?

Typing C-l causes Agda to create a hole and tell us its expected type.

    typing₁ = { }0
    ?0 : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `not` in a `λ`, which is typed using `⇒-I`. The
`⇒-I` rule in turn takes one argument, which Agda leaves as a hole.

    typing₁ = ⇒-I { }0
    ?0 : ∅ , x ∶ 𝔹 ⊢ if ` x then false else true ∶ 𝔹

Again we fill in the hole by typing C-c C-r. Agda observes that the
outermost term is now `if_then_else_`, which is typed using `𝔹-E`. The
`𝔹-E` rule in turn takes three arguments, which Agda leaves as holes.

    typing₁ = ⇒-I (𝔹-E { }0 { }1 { }2)
    ?0 : ∅ , x ∶ 𝔹 ⊢ ` x ∶
    ?1 : ∅ , x ∶ 𝔹 ⊢ false ∶ 𝔹
    ?2 : ∅ , x ∶ 𝔹 ⊢ true ∶ 𝔹

Again we fill in the three holes by typing C-c C-r in each. Agda observes
that `` ` x ``, `false`, and `true` are typed using `Ax`, `𝔹-I₂`, and
`𝔹-I₁` respectively. The `Ax` rule in turn takes an argument, to show
that `(∅ , x ∶ 𝔹) x = just 𝔹`, which can in turn be specified with a
hole. After filling in all holes, the term is as above.

The entire process can be automated using Agsy, invoked with C-c C-a.


