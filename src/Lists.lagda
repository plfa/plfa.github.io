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
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
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

    {-# BUILTIN LIST List #-}

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


## Append

Our first function on lists is written `_++_` and pronounced
*append*.  
\begin{code}
infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
\end{code}
The type `A` is an implicit argument to append, making it
a *polymorphic* function (one that can be used at many types).
The empty list appended to another list yields the other list.
A non-empty list appended to another list yields a list with
head the same as the head of the first list and
tail the same as the tail of the first list appended to the second list.

Here is an example, showing how to compute the result
of appending two lists.
\begin{code}
ex₂ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
ex₂ =
  begin
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
Appending two lists requires time linear in the
number of elements in the first list.


## Reasoning about append

We can reason about lists in much the same way that we reason
about numbers.  Here is the proof that append is associative.
\begin{code}
++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎
\end{code}
The proof is by induction on the first argument. The base case instantiates
to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs`,
and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated by a recursive
invocation of the proof, in this case `++-assoc xs ys zs`.

Agda supports a variant of the *section* notation introduced by Richard Bird.
If `_⊕_` is an arbitrary binary operator, we
write `(x ⊕_)` for the function which applied to `y` returns `x ⊕ y`, and
we write `(_⊕ y)` for the function which applied to `x` also returns `x ⊕ y`.
Applying the congruence `cong (x ∷_)` promotes the inductive hypothesis

    xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs

to the equivalence

    x ∷ (xs ++ (ys ++ zs)) ≡ x ∷ ((xs ++ ys) ++ zs)

which is needed in the proof.

It is also easy to show that `[]` is a left and right identity for `_++_`.
That it is a left identity is immediate from the definition.
\begin{code}
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎
\end{code}
That it is a right identity follows by simple induction.
\begin{code}
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎
\end{code}
These three properties establish that `_++_` and `[]` form
a *monoid* over lists.

## Length

Our next function finds the length of a list.
\begin{code}
length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)
\end{code}
Again, it takes an implicit parameter `A`.
The length of the empty list is zero.
The length of a non-empty list
is one greater than the length of the tail of the list.

Here is an example showing how to compute the length of a list.
\begin{code}
ex₃ : length ([ 0 , 1 , 2 ]) ≡ 3
ex₃ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎
\end{code}
Computing the length of a list requires time
linear in the number of elements in the list.

In the second-to-last line, we cannot write
simply `length []`  but must instead write
`length {ℕ} []`.  This is because Agda has
insufficient information to infer the implicit
parameter; after all, `[]` could just as well
be an empty list with elements of any type.


## Reasoning about length

The length of one list appended to another is the
sum of the lengths of the lists.
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
The proof is by induction on the first arugment. The base case instantiates
to `[]`, and follows by straightforward computation.
As before, Agda cannot infer the implicit type parameter to `length`,
and it must be given explicitly.
The inductive case instantiates to `x ∷ xs`,
and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated by a recursive
invocation of the proof, in this case `length-++ xs ys`, and it is promoted
by the congruence `cong suc`.


## Reverse

Using append, it is easy to formulate a function to reverse a list.
\begin{code}
reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]
\end{code}
The reverse of the empty list is the empty list.
The reverse of a non-empty list
is the reverse of its tail appended to a unit list
containing its head.

Here is an example showing how to reverse a list.
\begin{code}
ex₄ : reverse ([ 0 , 1 , 2 ]) ≡ [ 2 , 1 , 0 ]
ex₄ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎
\end{code}
Reversing a list in this way takes time *quadratic* in the length of
the list. This is because reverse ends up appending lists of lengths
`1`, `2`, up to `n - 1`, where `n` is the length of the list being
reversed, append takes time linear in the length of the first
list, and the sum of the numbers up to `n` is `n * (n + 1) / 2`.
(We will validate that last fact later in this chapter.)

## Reasoning about reverse

*Exercise* `reverse-++-commute`

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first.

    reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

*Exercise* `reverse-involutive`

A function is an *involution* if when applied twice it acts
as the identity function.  Show that reverse is an involution.

    reverse (reverse xs) ≡ xs

## Faster reverse

The definition above, while easy to reason about, is less efficient than
one might expect since it takes time quadratic in the length of the list.
The idea is that we generalise reverse to take an additional argument.
\begin{code}
shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys =  shunt xs (x ∷ ys)
\end{code}
The definition is by recursion on the first argument. The second argument
actually becomes *larger*, but this is not a problem because the argument
on which we recurse becomes *smaller*.

Shunt is related to reverse as follows.
\begin{code}
shunt-reverse : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) ([ x ]) ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎
\end{code}
The proof is by induction on the first argument.
The base case instantiates to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs` and follows by the inductive
hypothesis and associativity of append.  When we invoke the inductive hypothesis,
the second argument actually becomes *larger*, but this is not a problem because
the argument on which we induct becomes *smaller*.

Generalising on an auxiliary argument, which becomes larger as the argument on
which we recurse or induct becomes smaller, is a common trick. It belongs in
you sling of arrows, ready to slay the right problem.

Having defined shunt be generalisation, it is now easy to respecialise to
give a more efficient definition of reverse.
\begin{code}
reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []
\end{code}

Given our previous lemma, it is straightforward to show
the two definitions equivalent.
\begin{code}
reverses : ∀ {A : Set} (xs : List A) → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎
\end{code}

Here is an example showing fast reverse of the list `[ 0 , 1 , 2 ]`.
\begin{code}
ex₅ : reverse′ ([ 0 , 1 , 2 ]) ≡ [ 2 , 1 , 0 ]
ex₅ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩  
    2 ∷ 1 ∷ 0 ∷ []
  ∎
\end{code}
Now the time to reverse a list is linear in the length of the list.

## Map

Map applies a function to every element of a list to generate a corresponding list.
Map is an example of a *higher-order function*, one which takes a function as an
argument and returns a function as a result.
\begin{code}
map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
\end{code}
Map of the empty list is the empty list.
Map of a non-empty list yields a list
with head the same as the function applied to the head of the given list,
and tail the same as map of the function applied to the tail of the given list.

Here is an example showing how to use map to increment every element of a list.
\begin{code}
ex₆ : map suc ([ 0 , 1 , 2 ]) ≡ [ 1 , 2 , 3 ]
ex₆ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ∎
\end{code}
Map requires time linear in the length of the list.

It is often convenient to exploit currying by applying
map to a function to yield a new function, and at a later
point applying the resulting function.
\begin{code}
sucs : List ℕ → List ℕ
sucs = map suc

ex₇ : sucs ([ 0 , 1 , 2 ]) ≡ [ 1 , 2 , 3 ]
ex₇ = ex₆
\end{code}

Any type that is parameterised on another type, such as lists, has a
corresponding map, which accepts a function and returns a function
from the type parameterised on the domain of the function to the type
parameterised on the range of the function. Further, a type that is
parameterised on *n* types will have a map that is parameterised on
*n* functions.


*Exercise* `map-compose`

The composition of two functions applies one and then the other.
\begin{code}
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)
\end{code}
Prove that the map of a composition is equal to the composition of two maps.

    map (f ∘ g) ≡ map f ∘ map g

The last step of the proof requires extensionality.
\begin{code}
postulate
  extensionality : ∀ {A B : Set} → {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
\end{code}

*Exercise* `map-++-commute`

Prove the following relationship between map and append.

    map f (xs ++ ys) ≡ map f xs ++ map f ys


## Fold

Fold takes an operator and a value, and uses the operator to combine
each of the elements of the list, taking the given value as the result
for the empty list.  
\begin{code}
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []       = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs
\end{code}
Fold of the empty list is the given value.
Fold of a non-empty list uses the operator to combine
the head of the list and the fold of the tail of the list.

Here is an example showing how to use fold to find the sum of a list.
\begin{code}
ex₈ : foldr _+_ 0 ([ 1 , 2 , 3 , 4 ]) ≡ 10
ex₈ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎    
\end{code}
Fold requires time linear in the length of the list.

It is often convenient to exploit currying by applying
fold to an operator and a value to yield a new function,
and at a later point applying the resulting function.
\begin{code}
sum : List ℕ → ℕ
sum = foldr _+_ 0

ex₉ : sum ([ 1 , 2 , 3 , 4 ]) ≡ 10
ex₉ = ex₈
\end{code}

Just as the list type has two constructors, `[]` and `_∷_`,
so the fold function takes two arguments, `e` and `_⊕_`
(in addition to the list argument).
In general, a data type with *n* constructors will have
a corresponding fold function that takes *n* arguments.

*Exercise* (`product`)

Use fold to define a function to find the product of a list of numbers.

    product ([ 1 , 2 , 3 , 4 ]) ≡ 24

*Exercise* (`foldr-++`)

Show that fold and append are related as follows.

    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

*Exercise* (`map-is-foldr`)  <!-- `mapIsFold` in Data.List.Properties -->

Show that map can be defined using fold.

    map f ≡ foldr (λ x xs → f x ∷ xs) []

This requires extensionality.


## Monoids

Typically when we use a fold the operator is associative and the
value is a left and right identity for the value, meaning that the
operator and the value form a *monoid*.

We can define a monoid as a suitable record type.
\begin{code}
record Monoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open Monoid
\end{code}

As examples, sum and zero, multiplication and one, and append and the empty
list, are all examples of monoids.
\begin{code}
+-monoid : Monoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : Monoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → Monoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }
\end{code}

If `_⊕_` and `e` form a monoid, then we can re-express fold on the
same operator and an arbitrary value.
\begin{code}
fold-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → Monoid _⊗_ e →
  ∀ (y : A) (xs : List A) → foldr _⊗_ e xs ⊗ y ≡ foldr _⊗_ y xs
fold-monoid _⊗_ e ⊗-monoid y [] =
  begin
    foldr _⊗_ e [] ⊗ y
  ≡⟨⟩
    (e ⊗ y)
  ≡⟨ identityˡ ⊗-monoid y ⟩
    y
  ≡⟨⟩
   foldr _⊗_ y []
  ∎
fold-monoid _⊗_ e ⊗-monoid y (x ∷ xs) =
  begin
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ≡⟨⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨ assoc ⊗-monoid x (foldr _⊗_ e xs) y ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ cong (x ⊗_) (fold-monoid _⊗_ e ⊗-monoid y xs) ⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨⟩
    foldr _⊗_ y (x ∷ xs)
  ∎
\end{code}

As a consequence of `foldr-++` and `fold-monoid`, it is easy to show

    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys


## Element

\begin{code}
data _∈_ {A : Set} (x : A) : List A → Set where
  here : {y : A} {ys : List A} → x ≡ y → x ∈ y ∷ ys
  there : {y : A} {ys : List A} → x ∈ ys → x ∈ y ∷ ys

infix 4 _∈_
\end{code}

## Unicode

    ∷  U+2237  PROPORTION  (\::)
    ⊗  (\otimes)
