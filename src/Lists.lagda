---
title     : "Lists: Lists and other data types"
layout    : page
permalink : /Lists
---

This chapter gives examples of other data types in Agda, as well as
introducing polymorphic types and functions.

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
\end{code}

## Lists

Lists are defined in Agda as follows.
\begin{code}
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
\end{code}
Let's unpack this definition. The phrase

    List (A : Set) : Set

tells us that `List` is a function from a `Set` to a `Set`.
We write `A` consistently for the argument of `List` throughout
the declaration.  The next two lines tell us that `[]` (pronounced *nil*)
is the empty list of type `A`, and that `_∷_` (pronounced *cons*,
short for *constructor*) takes a value of type `A` and a `List A` and
returns a `List A`.  Operator `_∷_` has precedence level 5 and associates
to the right.

For example,
\begin{code}
ex₀ : List ℕ
ex₀ = 0 ∷ 1 ∷ 2 ∷ []
\end{code}
denotes the list of the first three natural numbers.  Since `_::_`
associates to the right, the term above parses as `0 ∷ (1 ∷ (2 ∷ []))`.
Here `0` is the first element of the list, called the *head*,
and `1 ∷ (2 ∷ [])` is a list of the remaining elements, called the
*tail*. Lists are a rather strange beast: a head and a tail, 
nothing in between, and the tail is itself another list!

The definition of lists could also be written as follows.
\begin{code}
data List′ : Set → Set where
  []′ : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A
\end{code}
This is essentially equivalent to the previous definition,
and lets us see that constructors `[]` and `_∷_` each act as
if they take an implicit argument, the type of the list.

The previous form is preferred because it is more compact
and easier to read; using it also improves Agda's ability to
reason about when a function definition based on pattern matching
is well defined. An important difference is that in the previous
form we must write `List A` consistently everywhere, whereas in
the second form it would be permitted to replace an occurrence
of `List A` by `List ℕ`, say.

Including the lines
\begin{code}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}
\end{code}
tells Agda that the type `List` corresponds to the Haskell type
list, and the constructors `[]` and `_∷_` correspond to nil and
cons respectively, allowing a more efficient representation of lists.

## List syntax

We can write lists more conveniently be introducing the following definitions.
\begin{code}
infix 5 [_
infixr 6 _,_
infix 7 _]

[_ : ∀ {A : Set} → List A → List A
[ xs  =  xs

_,_ : ∀ {A : Set} → A → List A → List A
x , xs = x ∷ xs

_] : ∀ {A : Set} → A → List A
x ] = x ∷ []
\end{code}

These permit lists to be written in traditional notation.
\begin{code}
ex₁ : [ 0 , 1 , 2 ] ≡ 0 ∷ 1 ∷ 2 ∷ []
ex₁ = refl
\end{code}
The precedences mean that `[ 0 , 1 , 2 ]` parses as
`[ (0 , (1 , (2 ])))`, which evaluates to `0 ∷ 1 ∷ 2 ∷ []`,
as desired.

Note our syntactic trick only applies to non-empty lists.
The empty list must be written `[]`.  Writing `[ ]` fails
to parse.


## Sections

Richard Bird introduced a convenient notation for partially applied binary
operators, called *sections*.  If `_⊕_` is an arbitrary binary operator, we
write `(x ⊕)` for the function which applied to `y` returns `x ⊕ y`, and
we write `(⊕ y)` for the function which applied to `x` also returns `x ⊕ y`.

For example, here are definitions of the sections for cons.
\begin{code}
_∷ : ∀ {A : Set} → A → List A → List A
(x ∷) xs = x ∷ xs

∷_ : ∀ {A : Set} → List A → A → List A
(∷ xs) x = x ∷ xs
\end{code}
We will make use of the first of these in the next section.


## Append

Our first function on lists is written `_++_` and pronounced
*append*.  
\begin{code}
infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
\end{code}
The type `A` is an implicit argument to append.
The empty list appended to a list `ys` is the same as `ys`.
A list with head `x` and tail `xs` appended to a list `ys`
yields a list with head `x` and with tail consisting of
`xs` appended to `ys`.

Here is an example, showing how to compute the result
of appending the list `[ 0 , 1 , 2 ]` to the list `[ 3 , 4 ]`.
\begin{code}
ex₂ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
ex₂ =
  begin
    [ 0 , 1 , 2 ] ++ [ 3 , 4 ]
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎
\end{code}


## Reasoning about append

We can reason about lists in much the same way that we reason
about numbers.  Here is the proof that append is associative.
\begin{code}
++-assoc : ∀ {A : Set} (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc [] ys zs =
  begin
    [] ++ (ys ++ zs)
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    ([] ++ ys) ++ zs
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs) ++ (ys ++ zs)
  ≡⟨⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨ cong (x ∷) (++-assoc xs ys zs) ⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨⟩
    ((x ∷ xs) ++ ys) ++ zs
  ∎
\end{code}
The proof is by induction. The base case instantiates the
first argument to `[]`, and follows by straightforward computation.
The inductive case instantiates the first argument to `x ∷ xs`,
and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated by a recursive
invocation of the proof, in this case `++-assoc xs ys zs`.
Applying the congruence `cong (x ∷)` promotes the inductive hypothesis

    xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs

to the equivalence needed in the proof

    x ∷ (xs ++ (ys ++ zs)) ≡ x ∷ ((xs ++ ys) ++ zs)

The section notation `(x ∷)` makes it convenient to invoke the congruence.

## Length

\begin{code}
length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)
\end{code}

## Reverse

## Map

## Fold

\begin{code}
map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

ex₃ : length ([ 1 , 2 , 3 ]) ≡ 3
ex₃ = refl

ex₄ : map (λ x → x * x) ([ 1 , 2 , 3 ]) ≡ [ 1 , 4 , 9 ]
ex₄ = refl

ex₅ : foldr _+_ 0 ([ 1 , 2 , 3 ]) ≡ 6
ex₅ = refl

ex₆ : length {ℕ} [] ≡ zero
ex₆ = refl
\end{code}

\begin{code}
length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys = 
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎
\end{code}

\begin{code}
data _∈_ {A : Set} (x : A) : List A → Set where
  here : {y : A} {ys : List A} → x ≡ y → x ∈ y ∷ ys
  there : {y : A} {ys : List A} → x ∈ ys → x ∈ y ∷ ys

infix 4 _∈_
\end{code}

## Unicode

    ∷  U+2237  PROPORTION  (\::)
