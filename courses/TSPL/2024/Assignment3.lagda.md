---
title     : "Assignment3: TSPL Assignment 3"
permalink : /TSPL/2024/Assignment3/
---

```
module Assignment3 where
```

## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using Gradescope. Go to the course page under Learn.
Select "Assessment", then select "Assignment Submission".
Please ensure your files execute correctly under Agda!


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

You are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself). Do not publish solutions to the coursework.

## Deadline and late policy

The deadline and late policy for this assignment are specified on
Learn in the "Coursework Planner". There are no extensions and
no ETAs. Coursework is marked best three out of four. Guidance
on late submissions is at

> [https://web.inf.ed.ac.uk/node/4533](https://web.inf.ed.ac.uk/node/4533)

## Lists

```
module Lists where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; sym; trans; cong)
  open Eq.≡-Reasoning
  open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
  open import Data.Nat.Properties using
    (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Function using (_∘_)
  open import Level using (Level)
  open import plfa.part1.Isomorphism using (_≃_; _⇔_)
```


```
  open import plfa.part1.Lists
    hiding (downFrom; Tree; leaf; node; merge)
```

#### Exercise `reverse-++-distrib` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first:

    reverse (xs ++ ys) ≡ reverse ys ++ reverse xs


#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution:

    reverse (reverse xs) ≡ xs


#### Exercise `map-compose` (practice)

Prove that the map of a composition is equal to the composition of two maps:

    map (g ∘ f) ≡ map g ∘ map f

The last step of the proof requires extensionality.

```agda
  -- Your code goes here
```

#### Exercise `map-++-distribute` (practice)

Prove the following relationship between map and append:

    map f (xs ++ ys) ≡ map f xs ++ map f ys

```agda
  -- Your code goes here
```

#### Exercise `map-Tree` (practice)

Define a type of trees with leaves of type `A` and internal
nodes of type `B`:
```agda
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    node : Tree A B → B → Tree A B → Tree A B
```
Define a suitable map operator over trees:

    map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D

```agda
  -- Your code goes here
```

#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example:

    product [ 1 , 2 , 3 , 4 ] ≡ 24

```agda
  -- Your code goes here
```

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows:

    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

```agda
  -- Your code goes here
```

#### Exercise `foldr-∷` (practice)

Show

    foldr _∷_ [] xs ≡ xs

Show as a consequence of `foldr-++` above that

    xs ++ ys ≡ foldr _∷_ ys xs


```agda
  -- Your code goes here
```

#### Exercise `map-is-foldr` (practice)

Show that map can be defined using fold:

    map f ≡ foldr (λ x xs → f x ∷ xs) []

The proof requires extensionality.

```agda
  -- Your code goes here
```

#### Exercise `fold-Tree` (practice)

Define a suitable fold function for the type of trees given earlier:

    fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C


```agda
  -- Your code goes here
```

#### Exercise `map-is-fold-Tree` (practice)

Demonstrate an analogue of `map-is-foldr` for the type of trees.

```agda
  -- Your code goes here
```

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows:
```agda
  downFrom : ℕ → List ℕ
  downFrom zero     =  []
  downFrom (suc n)  =  n ∷ downFrom n
```
For example:
```agda
  _ : downFrom 3 ≡ [ 2 , 1 , 0 ]
  _ = refl
```
Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`:

    sum (downFrom n) * 2 ≡ n * (n ∸ 1)

```agda
  -- Your code goes here
```

#### Exercise `foldl` (practice)

Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example:

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

```agda
  -- Your code goes here
```


#### Exercise `foldr-monoid-foldl` (practice)

Show that if `_⊗_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.

```agda
  -- Your code goes here
```


#### Exercise `Any-++-⇔` (recommended)

Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.

```agda
  -- Your code goes here
```

#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.

```agda
  -- Your code goes here
```

#### Exercise `¬Any⇔All¬` (recommended)

Show that `Any` and `All` satisfy a version of De Morgan's Law:

    (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs

(Can you see why it is important that here `_∘_` is generalised
to arbitrary levels, as described in the section on
[universe polymorphism](/Equality/#unipoly)?)

Do we also have the following?

    (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs

If so, prove; if not, explain why.


```agda
  -- Your code goes here
```

#### Exercise `¬Any≃All¬` (stretch)

Show that the equivalence `¬Any⇔All¬` can be extended to an isomorphism.
You will need to use extensionality.

```agda
  -- Your code goes here
```

#### Exercise `All-∀` (practice)

Show that `All P xs` is isomorphic to `∀ x → x ∈ xs → P x`.

```agda
  -- You code goes here
```


#### Exercise `Any-∃` (practice)

Show that `Any P xs` is isomorphic to `∃[ x ] (x ∈ xs × P x)`.

```agda
  -- You code goes here
```


#### Exercise `Any?` (stretch)

Just as `All` has analogues `all` and `All?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `Any?` which determine whether a predicate holds
for some element of a list.  Give their definitions.

```agda
  -- Your code goes here
```


#### Exercise `split` (stretch)

The relation `merge` holds when two lists merge to give a third list.
```agda
  data merge {A : Set} : (xs ys zs : List A) → Set where

    [] :
        --------------
        merge [] [] []

    left-∷ : ∀ {x xs ys zs}
      → merge xs ys zs
        --------------------------
      → merge (x ∷ xs) ys (x ∷ zs)

    right-∷ : ∀ {y xs ys zs}
      → merge xs ys zs
        --------------------------
      → merge xs (y ∷ ys) (y ∷ zs)
```

For example,
```agda
  _ : merge [ 1 , 4 ] [ 2 , 3 ] [ 1 , 2 , 3 , 4 ]
  _ = left-∷ (right-∷ (right-∷ (left-∷ [])))

```

Given a decidable predicate and a list, we can split the list
into two lists that merge to give the original list, where all
elements of one list satisfy the predicate, and all elements of
the other do not satisfy the predicate.

Define the following variant of the traditional `filter` function on
lists, which given a decidable predicate and a list returns a list of
elements that satisfy the predicate and a list of elements that don't,
with their corresponding proofs.

    split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
      → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )

```agda
  -- Your code goes here
```


## Lambda

```
module Lambda where
```

## Imports

```agda
  open import Data.Bool using (Bool; true; false; T; not)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.List using (List; _∷_; [])
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Product using (∃-syntax; _×_)
  open import Data.String using (String; _≟_)
  open import Data.Unit using (tt)
  open import Relation.Nullary using (Dec; yes; no; ¬_)
  open import Relation.Nullary.Decidable using (False; toWitnessFalse; ¬?)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
```

```
  open import plfa.part2.Lambda
    hiding (var?; ƛ′_⇒_; case′_[zero⇒_|suc_⇒_]; μ′_⇒_; plus′)
```

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.  Your definition may use `plus` as
defined earlier.

```agda
  -- Your code goes here
```


#### Exercise `mulᶜ` (practice)

Write out the definition of a lambda term that multiplies
two natural numbers represented as Church numerals. Your
definition may use `plusᶜ` as defined earlier (or may not
— there are nice definitions both ways).

```agda
  -- Your code goes here
```


#### Exercise `primed` (stretch) {#primed}

Some people find it annoying to write `` ` "x" `` instead of `x`.
We can make examples with lambda terms slightly easier to write
by adding the following definitions:
```agda
  var? : (t : Term) → Bool
  var? (` _)  =  true
  var? _      =  false

  ƛ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
  ƛ′_⇒_ (` x) N = ƛ x ⇒ N

  case′_[zero⇒_|suc_⇒_] : Term → Term → (t : Term) → {_ : T (var? t)} → Term → Term
  case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]

  μ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
  μ′ (` x) ⇒ N  =  μ x ⇒ N
```

Recall that `T` is a function that maps from the computation world to
the evidence world, as
[defined](/Decidable/#relating-evidence-and-computation)
in Chapter [Decidable](/Decidable/).  We ensure to
use the primed functions only when the respective term argument is a
variable, which we do by providing implicit evidence.  For example, if
we tried to define an abstraction term that binds anything but a
variable:

    _ : Term
    _ = ƛ′ two ⇒ two

Agda would complain it cannot find a value of the bottom type for the
implicit argument. Note the implicit argument's type reduces to `⊥`
when term `t` is anything but a variable.

The definition of `plus` can now be written as follows:
```agda
  plus′ : Term
  plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
            case′ m
              [zero⇒ n
              |suc m ⇒ `suc (+ · m · n) ]
    where
    +  =  ` "+"
    m  =  ` "m"
    n  =  ` "n"
```
Write out the definition of multiplication in the same style.


#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a `with` clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.

```agda
  -- Your code goes here
```


#### Exercise `—↠≲—↠′` (practice)

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

```agda
  -- Your code goes here
```

#### Exercise `plus-example` (practice)

Write out the reduction sequence demonstrating that one plus one is two.

```agda
  -- Your code goes here
```


#### Exercise `Context-≃` (practice)

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

```agda
  -- Your code goes here
```

#### Exercise `⊢mul` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well typed.

```agda
  -- Your code goes here
```


#### Exercise `⊢mulᶜ` (practice)

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

```agda
  -- Your code goes here
```



## Properties

```
module Properties where
```

## Imports

```agda
  open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; cong; cong₂)
  open import Data.String using (String; _≟_)
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Product
    using (_×_; proj₁; proj₂; ∃; ∃-syntax)
    renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Function using (_∘_)
  open import plfa.part1.Isomorphism
  open import plfa.part2.Lambda
```


```
  open import plfa.part2.Properties
    hiding (value?; Canonical_⦂_; unstuck; preserves; wttdgs)
  -- open Lambda using (mul; ⊢mul)
```

#### Exercise `Canonical-≃` (practice)

Well-typed values must take one of a small number of _canonical forms_,
which provide an analogue of the `Value` relation that relates values
to their types.  A lambda expression must have a function type,
and a zero or successor expression must be a natural.
Further, the body of a function must be well typed in a context
containing only its bound variable, and the argument of successor
must itself be canonical:
```agda
  infix  4 Canonical_⦂_

  data Canonical_⦂_ : Term → Type → Set where

    C-ƛ : ∀ {x A N B}
      → ∅ , x ⦂ A ⊢ N ⦂ B
        -----------------------------
      → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

    C-zero :
        --------------------
        Canonical `zero ⦂ `ℕ

    C-suc : ∀ {V}
      → Canonical V ⦂ `ℕ
        ---------------------
      → Canonical `suc V ⦂ `ℕ
```

Show that `Canonical V ⦂ A` is isomorphic to `(∅ ⊢ V ⦂ A) × (Value V)`,
that is, the canonical forms are exactly the well-typed values.

```
  -- Your code goes here
```

#### Exercise `Progress-≃` (practice)

Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M —→ N)`.

```agda
  -- Your code goes here
```

#### Exercise `progress′` (practice)

Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.

```agda
  -- Your code goes here
```

#### Exercise `value?` (practice)

Combine `progress` and `—→¬V` to write a program that decides
whether a well-typed term is a value:
```agda
  postulate
    value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
```

#### Exercise `subst′` (stretch)

Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.

```agda
  -- Your code goes here
```


#### Exercise `mul-eval` (recommended)

Using the evaluator, confirm that two times two is four.

```agda
  -- Your code goes here
```


#### Exercise: `progress-preservation` (practice)

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.

```agda
  -- Your code goes here
```


#### Exercise `subject_expansion` (practice)

We say that `M` _reduces_ to `N` if `M —→ N`,
but we can also describe the same situation by saying
that `N` _expands_ to `M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M —→ N` and `∅ ⊢ N ⦂ A` imply `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.

```agda
  -- Your code goes here
```


#### Exercise `stuck` (practice)

Give an example of an ill-typed term that does get stuck.

```agda
  -- Your code goes here
```

#### Exercise `unstuck` (recommended)

Provide proofs of the three postulates, `unstuck`, `preserves`, and `wttdgs` above.

```agda
  -- Your code goes here
```


## DeBruijn

```
module DeBruijn where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Decidable using (True; toWitness)
```

```
  open import plfa.part2.DeBruijn
    hiding ()
```

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers, now adapted to the intrinsically-typed
de Bruijn representation.

```agda
  -- Your code goes here
```


#### Exercise `V¬—→` (practice)

Following the previous development, show values do
not reduce, and its corollary, terms that reduce are not
values.

```agda
  -- Your code goes here
```

#### Exercise `mul-example` (recommended)

Using the evaluator, confirm that two times two is four.

```agda
  -- Your code goes here
```
