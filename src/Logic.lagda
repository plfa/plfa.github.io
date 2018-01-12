---
title     : "Logic: Propositions as Type"
layout    : page
permalink : /Logic
---

This chapter describes the connection between logical connectives
(conjunction, disjunction, implication, for all, there exists,
equivalence) and datatypes (product, sum, function, dependent
function, dependent product, Martin Löf equivalence).

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
\end{code}

This chapter introduces the basic concepts of logic, including
conjunction, disjunction, true, false, implication, negation,
universal quantification, and existential quantification.
Each concept of logic is represented by a corresponding standard
data type.

+ *conjunction* is *product*
+ *disjunction* is *sum*
+ *true* is *unit type*
+ *false* is *empty type*
+ *implication* is *function space*
+ *negation* is *function to empty type*
+ *universal quantification* is *dependent function*
+ *existential quantification* is *dependent product*

We also discuss how equality is represented, and the relation
between *intuitionistic* and *classical* logic.


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
≃-tran : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-tran A≃B B≃C =
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

≲-tran : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-tran A≲B B≲C =
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





## Conjunction is product

Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type.
\begin{code}
data _×_ : Set → Set → Set where
  _,_ : ∀ {A B : Set} → A → B → A × B
\end{code}
If `A` and `B` are propositions then `A × B` is
also a proposition.  Evidence that `A × B` holds is of the form
`(x , y)`, where `x` is evidence that `A` holds and
`y` is evidence that `B` holds.

Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds.
\begin{code}
fst : ∀ {A B : Set} → A × B → A
fst (x , y) = x

snd : ∀ {A B : Set} → A × B → B
snd (x , y) = y
\end{code}
If `w` is evidence that `A × B` holds, then `fst w` is evidence
that `A` holds, and `snd w` is evidence that `B` holds.

Equivalently, we could also declare product as a record type.
\begin{code}
record _×′_ (A B : Set) : Set where
  field
    fst′ : A
    snd′ : B
open _×′_
\end{code}
We construct values of the record type with the syntax:

    record
      { fst′ = x
      ; snd′ = y
      }

which corresponds to using the constructor of the corresponding
inductive type:

    ( x , y)

where `x` is a value of type `A` and `y` is a value of type `B`.

We set the precedence of conjunction so that it binds less
tightly than anything save disjunction, and of the pairing
operator so that it binds less tightly than any arithmetic
operator.
\begin{code}
infixr 2 _×_
infixr 4 _,_
\end{code}
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)` and
`(m * n , p)` parses as `((m * n) , p)`.

Given two types `A` and `B`, we refer to `A x B` as the
*product* of `A` and `B`.  In set theory, it is also sometimes
called the *cartesian product*, and in computing it corresponds
to a *record* type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members.
\begin{code}
data Bool : Set where
  true : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
\end{code}
Then the type `Bool × Tri` has six members:

    (true  , aa)    (true  , bb)    (true ,  cc)
    (false , aa)    (false , bb)    (false , cc)

For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
\begin{code}
×-count : Bool × Tri → ℕ
×-count (true , aa) = 1
×-count (true , bb) = 2
×-count (true , cc) = 3
×-count (false , aa) = 4
×-count (false , bb) = 5
×-count (false , cc) = 6
\end{code}

Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative *up to
isomorphism*.

For commutativity, the `to` function swaps a pair, taking `(x , y)` to
`(y , x)`, and the `fro` function does the same (up to renaming).
Instantiating the patterns correctly in `invˡ` and `invʳ` is essential.
Replacing the definition of `invˡ` by `λ w → refl` will not work;
and similarly for `invʳ`, which does the same (up to renaming).
\begin{code}
×-comm : ∀ {A B : Set} → (A × B) ≃ (B × A)
×-comm = record
  { to = λ { (x , y) → (y , x)}
  ; fro = λ { (y , x) → (x , y)}
  ; invˡ = λ { (x , y) → refl }
  ; invʳ = λ { (y , x) → refl }
  }
\end{code}
Being *commutative* is different from being *commutative up to
isomorphism*.  Compare the two statements:

    m * n ≡ n * m
    A × B ≃ B × A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
*not* the same as `Tri × Bool`.  But there is an isomorphism
between the two types.  For
instance, `(true , aa)`, which is a member of the former, corresponds
to `(aa , true)`, which is a member of the latter.

For associativity, the `to` function reassociates two uses of pairing,
taking `((x , y) , z)` to `(x , (y , z))`, and the `fro` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplificition.
\begin{code}
×-assoc : ∀ {A B C : Set} → ((A × B) × C) ≃ (A × (B × C))
×-assoc = record
  { to = λ { ((x , y) , z) → (x , (y , z)) }
  ; fro = λ { (x , (y , z)) → ((x , y) , z) }
  ; invˡ = λ { ((x , y) , z) → refl }
  ; invʳ = λ { (x , (y , z)) → refl }
  }
\end{code}

Again, being *associative* is not the same as being *associative
up to isomorphism*.  For example, the type `(ℕ × Bool) × Tri`
is *not* the same as `ℕ × (Bool × Tri)`. But there is an
isomorphism between the two types. For instance `((1 , true) , aa)`,
which is a member of the former, corresponds to `(1 , (true , aa))`,
which is a member of the latter.

Here we have used lambda-expressions with pattern matching.
For instance, the term

    λ { (x , y) → (y , x) }

corresponds to the function `h`, where `h` is defined by
\begin{code}
h : ∀ {A B : Set} → A × B → B × A
h (x , y) = (y , x)
\end{code}
Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition elsewhere in the code.

## Disjunction is sum

Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type.
\begin{code}
data _⊎_ : Set → Set → Set where
  inj₁  : ∀ {A B : Set} → A → A ⊎ B
  inj₂ : ∀ {A B : Set} → B → A ⊎ B
\end{code}
If `A` and `B` are propositions then `A ⊎ B` is
also a proposition.  Evidence that `A ⊎ B` holds is either of the form
`inj₁ x`, where `x` is evidence that `A` holds, or `inj₂ y`, where
`y` is evidence that `B` holds.

Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conlude that `C` holds.
\begin{code}
⊎-elim : ∀ {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
⊎-elim f g (inj₁ x) = f x
⊎-elim f g (inj₂ y) = g y
\end{code}
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.

We set the precedence of disjunction so that it binds less tightly
than any other operator.
\begin{code}
infix 1 _⊎_
\end{code}
Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.

Given two types `A` and `B`, we refer to `A ⊎ B` as the
*sum* of `A` and `B`.  In set theory, it is also sometimes
called the *disjoint union*, and in computing it corresponds
to a *variant record* type. Among other reasons for
calling it the sum, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.
For instance, consider a type `Bool` with three members, and
a type `Tri` with three members, as defined earlier.
Then the type `Bool ⊎ Tri` has five members:

    (inj₁ true)     (inj₂ aa)
    (inj₁ false)    (inj₂ bb)
                    (inj₂ cc)

For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
\begin{code}
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)  = 1
⊎-count (inj₁ false) = 2
⊎-count (inj₂ aa)    = 3
⊎-count (inj₂ bb)    = 4
⊎-count (inj₂ cc)    = 5
\end{code}

Sum on types also shares a property with sum on numbers in that it is
commutative and associative *up to isomorphism*.

For commutativity, the `to` function swaps the two constructors,
taking `inj₁ x` to `inj₂ x`, and `inj₂ y` to `inj₁ y`; and the `fro`
function does the same (up to renaming). Replacing the definition of
`invˡ` by `λ w → refl` will not work; and similarly for `invʳ`, which
does the same (up to renaming).
\begin{code}
+-comm : ∀ {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
+-comm = record
  { to   = λ { (inj₁ x) → (inj₂ x)
             ; (inj₂ y) → (inj₁ y)
             }
  ; fro  = λ { (inj₁ y) → (inj₂ y)
             ; (inj₂ x) → (inj₁ x)
             }
  ; invˡ = λ { (inj₁ x) → refl
             ; (inj₂ y) → refl
             }
  ; invʳ = λ { (inj₁ y) → refl
             ; (inj₂ x) → refl
             }
  }
\end{code}
Being *commutative* is different from being *commutative up to
isomorphism*.  Compare the two statements:

    m + n ≡ n + m
    A + B ≃ B + A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m + n` and `n + m` are equal to `5`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool + Tri` is
*not* the same as `Tri + Bool`.  But there is an isomorphism between
the two types.  For instance, `inj₁ true`, which is a member of the
former, corresponds to `inj₂ true`, which is a member of the latter.

For associativity, the `to` function reassociates, and the `fro` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplificition.
\begin{code}
+-assoc : ∀ {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
+-assoc = record
  { to   = λ { (inj₁ (inj₁ x)) → (inj₁ x)
             ; (inj₁ (inj₂ y)) → (inj₂ (inj₁ y))
             ; (inj₂ z)        → (inj₂ (inj₂ z))
             }
  ; fro  = λ { (inj₁ x)        → (inj₁ (inj₁ x))
             ; (inj₂ (inj₁ y)) → (inj₁ (inj₂ y))
             ; (inj₂ (inj₂ z)) → (inj₂ z)
             }
  ; invˡ = λ { (inj₁ (inj₁ x)) → refl
             ; (inj₁ (inj₂ y)) → refl
             ; (inj₂ z)        → refl
             }
  ; invʳ = λ { (inj₁ x)        → refl
             ; (inj₂ (inj₁ y)) → refl
             ; (inj₂ (inj₂ z)) → refl
             }
  }
\end{code}

Again, being *associative* is not the same as being *associative
up to isomorphism*.  For example, the type `(ℕ + Bool) + Tri`
is *not* the same as `ℕ + (Bool + Tri)`. But there is an
isomorphism between the two types. For instance `inj₂ (inj₁ true)`,
which is a member of the former, corresponds to `inj₁ (inj₂ true)`,
which is a member of the latter.

Here we have used lambda-expressions with pattern matching
and multiple cases. For instance, the term

    λ { (inj₁ x) → (inj₂ x)
      ; (inj₂ y) → (inj₁ y)
      }

corresponds to the function `k`, where `k` is defined by
\begin{code}
k : ∀ {A B : Set} → A ⊎ B → B ⊎ A
k (inj₁ x) = inj₂ x
k (inj₂ y) = inj₁ y
\end{code}


## Distribution

Distribution of `×` over `⊎` is an isomorphism.
\begin{code}
×-distributes-⊎ : ∀ {A B C : Set} → ((A ⊎ B) × C) ≃ ((A × C) ⊎ (B × C))
×-distributes-⊎ =
  record {
    to   = λ { ((inj₁ x) , z) → (inj₁ (x , z)) ;
               ((inj₂ y) , z) → (inj₂ (y , z)) } ;
    fro  = λ { (inj₁ (x , z)) → ((inj₁ x) , z) ;
               (inj₂ (y , z)) → ((inj₂ y) , z) } ;
    invˡ = λ { ((inj₁ x) , z) → refl ;
               ((inj₂ y) , z) → refl } ;
    invʳ = λ { (inj₁ (x , z)) → refl ;
               (inj₂ (y , z)) → refl }               
  }
\end{code}

Distribution of `⊎` over `×` is half an isomorphism.
\begin{code}
{-
data _≲_ : Set → Set → Set where
  mk-≲ : ∀ {A B : Set} → (f : A → B) → (g : B → A) →
          (∀ (x : A) → g (f x) ≡ x) → A ≲ B

+-distributes-× : ∀ {A B C : Set} → ((A × B) ⊎ C) ≲ ((A ⊎ C) × (B ⊎ C))
+-distributes-× =  mk-≲ f g gf
  where

  f : ∀ {A B C : Set} → (A × B) ⊎ C → (A ⊎ C) × (B ⊎ C)
  f (inj₁ (a , b)) = (inj₁ a , inj₁ b)
  f (inj₂ c) = (inj₂ c , inj₂ c)

  g : ∀ {A B C : Set} → (A ⊎ C) × (B ⊎ C) → (A × B) ⊎ C
  g (inj₁ a , inj₁ b) = inj₁ (a , b)
  g (inj₁ a , inj₂ c) = inj₂ c
  g (inj₂ c , inj₁ b) = inj₂ c
  g (inj₂ c , inj₂ c′) = inj₂ c  -- or inj₂ c′

  gf : ∀ {A B C : Set} → (x : (A × B) ⊎ C) → g (f x) ≡ x
  gf (inj₁ (a , b)) = refl
  gf (inj₂ c) = refl
-}
\end{code}

## True

\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}

## False

\begin{code}
data ⊥ : Set where
  -- no clauses!  

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
\end{code}

## Implication

## Negation

\begin{code}
¬_ : Set → Set
¬ A = A → ⊥

infix 3 ¬_

data Dec : Set → Set where
  yes : ∀ {A : Set} → A → Dec A
  no  : ∀ {A : Set} → (¬ A) → Dec A

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬b a = ¬b (f a)
\end{code}



## Intuitive and Classical logic

## Universals

## Existentials

## Equivalence

## Unicode

This chapter introduces the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    
