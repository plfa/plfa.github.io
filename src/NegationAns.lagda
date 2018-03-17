---
title     : "Logic Answers"
layout    : page
permalink : /LogicAns
---

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Isomorphism using (_≃_)
open import Negation using
  (¬_; id; EM; em-irrefutable; ¬¬-Elim; Peirce; Implication; ×-Implies-⊎)
\end{code}

In what follows, we occasionally require [extensionality][extensionality].
\begin{code}
postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
\end{code}

[extensionality]: Equality/index.html#extensionality



*Equivalences for classical logic*

\begin{code}
ex1 : ¬¬-Elim → EM
ex1 h = h em-irrefutable

ex2 : EM → Implication
ex2 em f with em
... | inj₁ a = inj₂ (f a)
... | inj₂ ¬a = inj₁ ¬a

ex3 : EM → Peirce
ex3 em k with em
... | inj₁ a = a
... | inj₂ ¬a = k (λ a → ⊥-elim (¬a a))

ex4 : EM → ×-Implies-⊎
ex4 em ¬a×b with em | em
... | inj₁ a | inj₁ b = ⊥-elim (¬a×b (a , b))
... | inj₁ a | inj₂ ¬b = inj₂ ¬b
... | inj₂ ¬a | _ = inj₁ ¬a

⊤⊥-iso : (¬ ⊥) ≃ ⊤
⊤⊥-iso =
  record
    { to      =  λ{ _ → tt }
    ; from    =  λ{ _ → id }
    ; from∘to =  λ{ _ → extensionality (λ ()) }
    ; to∘from =  λ{ tt → refl }
    }
\end{code}  

*Existentials and Universals*

\begin{code}
{-
∃¬¬∀ : ∀ {A : Set} {B : A → Set} → ∃ (λ (x : A) → ¬ B x) → ¬ (∀ (x : A) → B x)
∃¬¬∀ (x , ¬bx) ∀bx = ¬bx (∀bx x)
-}
\end{code}
