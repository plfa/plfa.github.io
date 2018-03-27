---
title     : "Isomorphism: Isomorphism and Embedding"
layout    : page
permalink : /Isomorphism
---

This section introduces isomorphism as a way of asserting that two
types are equal, and embedding as a way of asserting that one type is
smaller than another.  We apply isomorphisms in the next chapter
to demonstrate that operations on types such as product and sum
satisfy properties akin to associativity, commutativity, and
distributivity.

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
\end{code}

## Function composition

In what follows, we will make use of function composition.
\begin{code}
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)
\end{code}
Thus, `g ∘ f` is the function that first applies `f` and
then applies `g`.


## Isomorphism

In set theory, two sets are isomorphic if they are in one-to-one correspondence.
Here is a formal definition of isomorphism.
\begin{code}
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_ 
\end{code}
Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:
+ A function `to` from `A` to `B`,
+ A function `from` from `B` back to `A`,
+ Evidence `from∘to` asserting that `from` is a *right-identity* for `to`,
+ Evidence `to∘from` asserting that `to` is a *left-identity* for `from`.
In particular, the third asserts that `from ∘ to` is the identity, and
the fourth that `to ∘ from` is the identity, hence the names.
The declaration `open _≃_` makes available the names `to`, `from`,
`from∘to`, and `to∘from`, otherwise we would need to write `_≃_.to` and so on.

The above is our first use of records. A record declaration is equivalent
to a corresponding inductive data declaration.
\begin{code}
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) → 
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g
\end{code}
We construct values of the record type with the syntax:

    record
      { to    = f
      ; from  = g
      ; from∘to = g∘f
      ; to∘from = f∘g
      }

which corresponds to using the constructor of the corresponding
inductive type:

    mk-≃′ f g g∘f f∘g

where `f`, `g`, `g∘f`, and `f∘g` are values of suitable types.


## Isomorphism is an equivalence

Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `from` to be the identity function.
\begin{code}
≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    } 
\end{code}
This is our first use of *lambda expressions*, which provide a compact way to
define functions without naming them.  A term of the form

    λ{ P₁ → N₁; ⋯ ; Pᵢ → Nᵢ }
    
is equivalent to a function `f` defined by the equations

    f P₁ = e₁
    ⋯
    f Pᵢ = eᵢ

where the `Pᵢ` are patterns (left-hand sides of an equation) and the
`Nᵢ` are expressions (right-hand side of an equation).  In the case that
the pattern is a variable, we may also use the syntax

    λ (x : A) → N

which is equivalent to `λ{ x → N }` but allows one to specify the
domain of the function. Often using an anonymous lambda expression is
more convenient than using a named function: it avoids a lengthy type
declaration; and the definition appears exactly where the function is
used, so there is no need for the writer to remember to declare it in
advance, or for the reader to search for the definition elsewhere in
the code.

In the above, `to` and `from` are both bound to identity functions,
and `from∘to` and `to∘from` are both bound to functions that discard
their argument and return `refl`.  In this case, `refl` alone is an
adequate proof since for the left inverse, `λ{y → y} (λ{x → x} x)`
simplifies to `x`, and similarly for the right inverse.

To show isomorphism is symmetric, we simply swap the roles of `to`
and `from`, and `from∘to` and `to∘from`.
\begin{code}
≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B =
  record
    { to      = from A≃B
    ; from    = to   A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }
\end{code}
To show isomorphism is transitive, we compose the `to` and `from` functions, and use
equational reasoning to combine the inverses.
\begin{code}
≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C =
  record
    { to       = to   B≃C ∘ to   A≃B
    ; from     = from A≃B ∘ from B≃C
    ; from∘to  = λ{x →
        begin
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎} 
    ; to∘from = λ{y →
        begin
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎}
     }
\end{code}


## Equational reasoning for isomorphism

It is straightforward to support a variant of equational reasoning for
isomorphism.  We essentially copy the previous definition for
of equality.  We omit the form that corresponds to `_≡⟨⟩_`, since
trivial isomorphisms arise far less often than trivial equalities.

\begin{code}
module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} → A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning
\end{code}


## Embedding

We also need the notion of *embedding*, which is a weakening of
isomorphism.  While an isomorphism shows that two types are in
one-to-one correspondence, and embedding shows that the first type is
included in the second; or, equivalently, that there is a many-to-one
correspondence between the second type and the first.

Here is the formal definition of embedding.
\begin{code}
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_
\end{code}
It is the same as an isomorphism, save that it lacks the `to∘from` field.
Hence, we know that `from` is a right-identity for `to`, but not that `to`
is a left-identity fro `from`.

Embedding is reflexive and transitive, but not symmetric.  The proofs are cut down
versions of the similar proofs for isomorphism, simply dropping the
right inverses.
\begin{code}
≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    } 

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎} 
     }
\end{code}
It is also easy to see that if two types embed in each other,
and the embedding functions correspond, then they are isomorphic.
This is a weak form of anti-symmetry.
\begin{code}
≲-antisym : ∀ {A B : Set} → (A≲B : A ≲ B) → (B≲A : B ≲ A) →
  (to A≲B ≡ from B≲A) → (from A≲B ≡ to B≲A) → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎}
    }
\end{code}
The first three components are copied from the embedding, while the
last combines the left inverse of `B ≲ A` with the equivalences of
the `to` and `from` components from the two embeddings to obtain
the right inverse of the isomorphism.

## Equational reasoning for embedding

We can also support tabular reasoning for embedding,
analogous to that used for isomorphism.

\begin{code}
module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set} → A ≲ B → A ≲ B
  ≲-begin A≲B = A≲B


  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≲ B → B ≲ C → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set) → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning
\end{code}


## Standard library

Definitions similar to those in this chapter can be found in the standard library.
\begin{code}
import Function using (_∘_)
import Function.Inverse using (_↔_)
import Function.LeftInverse using (_↞_)
\end{code}
Here `_↔_` corresponds to our `_≃_`, and `_↞_` corresponds to our `_≲_`.
However, we stick with the definitions given here, mainly because `_↔_` is
specified as a nested record, rather than the flat records used here.

## Unicode

This chapter uses the following unicode.

    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
    ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
