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
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
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

Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `fro` to be the identity function.
\begin{code}
≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =
  record { to = λ x → x ; fro = λ y → y ; invˡ = λ x → refl ; invʳ = λ y → refl }
\end{code}
To show isomorphism is symmetric, we simply swap the roles of `to`
and `fro`, and `invˡ` and `invʳ`.
\begin{code}
≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B =
  record { to = fro A≃B ; fro = to A≃B ; invˡ = invʳ A≃B ; invʳ = invˡ A≃B }
\end{code}
To show isomorphism is symmetric, we compose the `to` and `fro` functions, and use
equational reasoning to combine the inverses.
\begin{code}
≃-tran : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-tran A≃B B≃C =
  record {
    to = λ x → to B≃C (to A≃B x);
    fro = λ y → fro A≃B (fro B≃C y);
    invˡ = λ x →
      begin
        fro A≃B (fro B≃C (to B≃C (to A≃B x)))
      ≡⟨ cong (fro A≃B) (invˡ B≃C (to A≃B x)) ⟩
        fro A≃B (to A≃B x)
      ≡⟨ invˡ A≃B x ⟩
        x
      ∎ ;
    invʳ = λ y →
      begin
        to B≃C (to A≃B (fro A≃B (fro B≃C y)))
      ≡⟨ cong (to B≃C) (invʳ A≃B (fro B≃C y)) ⟩
        to B≃C (fro B≃C y)
      ≡⟨ invʳ B≃C y ⟩
        y
      ∎
  }
\end{code}

## Conjunction

Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type.
\begin{code}
data _×_ : Set → Set → Set where
  _,_ : ∀ {A B : Set} → A → B → A × B
\end{code}
If `A` and `B` are propositions then `A × B` is
also a proposition.  Evidence that `A × B` holds is of the form
`a , b`, where `a` is evidence that `A` holds and
`b` is evidence that `B` holds.

We set the precedence of conjunction so that it binds less
tightly than anything save disjunction, and of the pairing
operator so that it binds less tightly than any arithmetic
operator.
\begin{code}
infixr 2 _×_
infixr 4 _,_
\end{code}

Product is associative and commutative up to isomorphism.
\begin{code}
×-assoc : ∀ {A B C : Set} → ((A × B) × C) ≃ (A × (B × C))
×-assoc =
  record {
    to = λ { ((x , y) , z) → (x , (y , z)) };
    fro = λ { (x , (y , z)) → ((x , y) , z) };
    invˡ = λ { ((x , y) , z) → refl } ;
    invʳ = λ { (x , (y , z)) → refl }
  }
\end{code}


## Disjunction

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
`inj₁ a`, where `a` is evidence that `A` holds, or `inj₂ b`, where
`b` is evidence that `B` holds.

We set the precedence of disjunction so that it binds less tightly
than any other operator.
\begin{code}
infix 1 _⊎_
\end{code}
Thus, `m ≤ n ⊎ n ≤ m` parses as `(m ≤ n) ⊎ (n ≤ m)`,
and `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.

## Distribution

Distribution of `×` over `⊎` is an isomorphism.
\begin{code}
{-
data _≃_ : Set → Set → Set where
  mk-≃ : ∀ {A B : Set} → (f : A → B) → (g : B → A) →
          (∀ (x : A) → g (f x) ≡ x) → (∀ (y : B) → f (g y) ≡ y) → A ≃ B

×-distributes-+ : ∀ {A B C : Set} → ((A ⊎ B) × C) ≃ ((A × C) ⊎ (B × C))
×-distributes-+ = mk-≃ f g gf fg
  where

  f : ∀ {A B C : Set} → (A ⊎ B) × C → (A × C) ⊎ (B × C)
  f (inj₁ a , c) = inj₁ (a , c)
  f (inj₂ b , c) = inj₂ (b , c)

  g : ∀ {A B C : Set} → (A × C) ⊎ (B × C) → (A ⊎ B) × C
  g (inj₁ (a , c)) = (inj₁ a , c)
  g (inj₂ (b , c)) = (inj₂ b , c)

  gf : ∀ {A B C : Set} → (x : (A ⊎ B) × C) → g (f x) ≡ x
  gf (inj₁ a , c) = refl
  gf (inj₂ b , c) = refl

  fg : ∀ {A B C : Set} → (y : (A × C) ⊎ (B × C)) → f (g y) ≡ y
  fg (inj₁ (a , c)) = refl
  fg (inj₂ (b , c)) = refl
-}
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
    
