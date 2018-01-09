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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
\end{code}

Distribution of `⊎` over `×` is half an isomorphism.
\begin{code}
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
    
