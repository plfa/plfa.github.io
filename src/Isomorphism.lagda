---
title     : "Isomorphism: Isomorphism and Embedding"
layout    : page
permalink : /Isomorphism
---

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
-- open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
-- open import Data.Nat.Properties.Simple using (+-suc)
-- open import Agda.Primitive using (Level; lzero; lsuc)
\end{code}

## Isomorphism

As a prelude, we begin by introducing the notion of isomorphism.
In set theory, two sets are isomorphism if they are in 1-to-1 correspondence.
Here is the formal definition of isomorphism.
\begin{code}
record _≃_ (A B : Set) : Set where
  field
    to : A → B
    fro : B → A
    invˡ : ∀ (x : A) → fro (to x) ≡ x
    invʳ : ∀ (y : B) → to (fro y) ≡ y
open _≃_ 
\end{code}
Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:
+ A function `to` from `A` to `B`,
+ A function `fro` from `B` back to `A`,
+ Evidence `invˡ` asserting that `to` followed by `from` is the identity,
+ Evidence `invʳ` asserting that `from` followed by `to` is the identity.
The declaration `open _≃_` makes avaialable the names `to`, `fro`,
`invˡ`, and `invʳ`, otherwise we would need to write `_≃_.to` and so on.

The above is our first example of a record declaration. It is equivalent
to a corresponding inductive data declaration.
\begin{code}
data _≃′_ : Set → Set → Set where
  mk-≃′ : ∀ {A B : Set} →
         ∀ (to : A → B) →
         ∀ (fro : B → A) → 
         ∀ (invˡ : (∀ (x : A) → fro (to x) ≡ x)) →
         ∀ (invʳ : (∀ (y : B) → to (fro y) ≡ y)) →
         A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g gfx≡x fgy≡y) = f

fro′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
fro′ (mk-≃′ f g gfx≡x fgy≡y) = g

invˡ′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → fro′ A≃B (to′ A≃B x) ≡ x)
invˡ′ (mk-≃′ f g gfx≡x fgy≡y) = gfx≡x

invʳ′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (fro′ A≃B y) ≡ y)
invʳ′ (mk-≃′ f g gfx≡x fgy≡y) = fgy≡y
\end{code}
We construct values of the record type with the syntax:

    record
      { to = f
      ; fro = g
      ; invˡ = gfx≡x
      ; invʳ = fgy≡y
      }

which corresponds to using the constructor of the corresponding
inductive type:

    mk-≃′ f g gfx≡x fgy≡y

where `f`, `g`, `gfx≡x`, and `fgy≡y` are values of suitable types.
      
Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `fro` to be the identity function.
\begin{code}
≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =
  record
    { to = λ x → x
    ; fro = λ y → y
    ; invˡ = λ x → refl
    ; invʳ = λ y → refl
    } 
\end{code}
To show isomorphism is symmetric, we simply swap the roles of `to`
and `fro`, and `invˡ` and `invʳ`.
\begin{code}
≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B =
  record
    { to = fro A≃B
    ; fro = to A≃B
    ; invˡ = invʳ A≃B
    ; invʳ = invˡ A≃B
    }
\end{code}
To show isomorphism is transitive, we compose the `to` and `fro` functions, and use
equational reasoning to combine the inverses.
\begin{code}
≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C =
  record
    { to = λ x → to B≃C (to A≃B x)
    ; fro = λ y → fro A≃B (fro B≃C y)
    ; invˡ = λ x →
        begin
          fro A≃B (fro B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (fro A≃B) (invˡ B≃C (to A≃B x)) ⟩
          fro A≃B (to A≃B x)
        ≡⟨ invˡ A≃B x ⟩
          x
        ∎ 
    ; invʳ = λ y →
        begin
          to B≃C (to A≃B (fro A≃B (fro B≃C y)))
        ≡⟨ cong (to B≃C) (invʳ A≃B (fro B≃C y)) ⟩
          to B≃C (fro B≃C y)
        ≡⟨ invʳ B≃C y ⟩
          y
        ∎
     }
\end{code}

We will make good use of isomorphisms in what follows to demonstrate
that operations on types such as product and sum satisfy properties
akin to associativity, commutativity, and distributivity.


## Tabular reasoning for isomorphism

It is straightforward to support a variant of tabular reasoning for
isomorphism.  We essentially copy the previous definition for
equivalence.  We omit the form that corresponds to `_≡⟨⟩_`, since
trivial isomorphisms arise far less often than trivial equivalences.

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

We will also need the notion of *embedding*, which is a weakening
of isomorphism.  While an isomorphism shows that two types are
in one-to-one correspondence, and embedding shows that the first
type is, in a sense, included in the second; or, equivalently,
that there is a many-to-one correspondence between the second
type and the first.

Here is the formal definition of embedding.
\begin{code}
record _≲_ (A B : Set) : Set where
  field
    to : A → B
    fro : B → A
    invˡ : ∀ (x : A) → fro (to x) ≡ x
open _≲_
\end{code}
It is the same as an isomorphism, save that it lacks the `invʳ` field.
Hence, we know that `fro` is left inverse to `to`, but not that it is
a right inverse.

Embedding is reflexive and transitive.  The proofs are cut down
versions of the similar proofs for isomorphism, simply dropping the
right inverses.
\begin{code}
≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to = λ x → x
    ; fro = λ y → y
    ; invˡ = λ x → refl
    } 

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to = λ x → to B≲C (to A≲B x)
    ; fro = λ y → fro A≲B (fro B≲C y)
    ; invˡ = λ x →
        begin
          fro A≲B (fro B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (fro A≲B) (invˡ B≲C (to A≲B x)) ⟩
          fro A≲B (to A≲B x)
        ≡⟨ invˡ A≲B x ⟩
          x
        ∎ 
     }
\end{code}
It is also easy to see that if two types embed in each other,
and the embedding functions correspond, then they are isomorphic.
This is a weak form of anti-symmetry.
\begin{code}
≲-antisym : ∀ {A B : Set} → (A≲B : A ≲ B) → (B≲A : B ≲ A) →
  (to A≲B ≡ fro B≲A) → (fro A≲B ≡ to B≲A) → A ≃ B
≲-antisym A≲B B≲A to≡fro fro≡to =
  record
    { to   = to A≲B
    ; fro  = fro A≲B
    ; invˡ = invˡ A≲B
    ; invʳ = λ y →
        begin
          to A≲B (fro A≲B y)
        ≡⟨ cong (\w → to A≲B (w y)) fro≡to ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong (\w → w (to B≲A y)) to≡fro ⟩
          fro B≲A (to B≲A y)
        ≡⟨ invˡ B≲A y ⟩
          y
        ∎
    }
\end{code}
The first three components are copied from the embedding, while the
last combines the left inverse of `B ≲ A` with the equivalences of
the `to` and `fro` components from the two embeddings to obtain
the right inverse of the isomorphism.

## Tabular reasoning for embedding

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



