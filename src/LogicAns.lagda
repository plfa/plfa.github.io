---
title     : "Logic Answers"
layout    : page
permalink : /LogicAns
---

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Logic
\end{code}


*Equivalences for classical logic*

\begin{code}
ex1 : ¬¬-elim → excluded-middle
ex1 h = h excluded-middle-irrefutable

ex2 : excluded-middle → implication
ex2 em f with em
... | inj₁ a = inj₂ (f a)
... | inj₂ ¬a = inj₁ ¬a

ex3 : excluded-middle → peirce
ex3 em k with em
... | inj₁ a = a
... | inj₂ ¬a = k (λ a → ⊥-elim (¬a a))

ex4 : de-morgan′ → ¬¬-elim
ex4 dem ¬¬a = fst (dem (obvs ¬¬a))
  where
  obvs : ∀ {A : Set} → ¬ ¬ A → ¬ (¬ A ⊎ ¬ ⊤)
  obvs ¬¬a (inj₁ ¬a) = ¬¬a ¬a
  obvs ¬¬a (inj₂ ¬⊤) = ¬⊤ tt

help′ : excluded-middle → ∀ {A B : Set} → ¬ (A × B) → ¬ A ⊎ ¬ B
help′ em ¬a×b with em | em
... | inj₁ a | inj₁ b = ⊥-elim (¬a×b (a , b))
... | inj₁ a | inj₂ ¬b = inj₂ ¬b
... | inj₂ ¬a | inj₁ b = inj₁ ¬a
... | inj₂ ¬a | inj₂ ¬b = inj₁ ¬a

⊤⊥-iso : (¬ ⊥) ≃ ⊤
⊤⊥-iso =
  record
    { to   =  λ _ → tt
    ; fro  =  λ _ ff → ff
    ; invˡ =  λ _ → extensionality (λ ())
    ; invʳ =  λ { tt → refl }
    }
\end{code}  

*Existentials and Universals*

\begin{code}
∃¬¬∀ : ∀ {A : Set} {B : A → Set} → ∃ (λ (x : A) → ¬ B x) → ¬ (∀ (x : A) → B x)
∃¬¬∀ (x , ¬bx) ∀bx = ¬bx (∀bx x)
\end{code}
