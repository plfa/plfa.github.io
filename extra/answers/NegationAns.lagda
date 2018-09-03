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
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_)
-- open import Isomorphism using (_≃_)
-- open import Negation using
--   (¬_; id; EM; em-irrefutable; ¬¬-Elim; Peirce; Implication; ×-Implies-⊎)
\end{code}

In what follows, we occasionally require [extensionality][extensionality].
\begin{code}
postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
\end{code}

[extensionality]: Equality/index.html#extensionality



*Equivalences for classical logic*

\begin{code}
em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

EM : Set₁
EM = ∀ {A : Set} → A ⊎ ¬ A

¬¬-Elim : Set₁
¬¬-Elim = ∀ {A : Set} → ¬ ¬ A → A

Implication : Set₁
Implication = ∀ {A B : Set} → (A → B) → ¬ A ⊎ B

Peirce : Set₁
Peirce = ∀ {A B : Set} → ((A → B) → A) → A

DeMorgan : Set₁
DeMorgan = ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B

ex1 : ¬¬-Elim → EM
ex1 ¬¬-elim = ¬¬-elim em-irrefutable

ex2 : EM → ¬¬-Elim
ex2 em ¬¬a with em
... | inj₁ a = a
... | inj₂ ¬a = ⊥-elim (¬¬a ¬a)

ex3 : EM → Implication
ex3 em f with em
... | inj₁ a = inj₂ (f a)
... | inj₂ ¬a = inj₁ ¬a

ex4 : Implication → EM
ex4 imp = swap (imp (λ a → a))
  where
  swap : ∀ {A B} → A ⊎ B → B ⊎ A
  swap (inj₁ a) = inj₂ a
  swap (inj₂ b) = inj₁ b

ex5 : EM → Peirce
ex5 em k with em
... | inj₁ a = a
... | inj₂ ¬a = k (λ a → ⊥-elim (¬a a))

ex6 : Peirce → EM
ex6 peirce = peirce (λ ¬em → ⊥-elim (em-irrefutable ¬em))

ex7 : EM → DeMorgan
ex7 em ¬[¬a×¬b] with em | em
... | inj₁ a | _ = inj₁ a
... | inj₂ ¬a | inj₁ b = inj₂ b
... | inj₂ ¬a | inj₂ ¬b = ⊥-elim (¬[¬a×¬b] ⟨ ¬a , ¬b ⟩)

ex8 : DeMorgan → EM
ex8 deMorgan {A} = deMorgan ¬[¬a×¬¬a]
  where
  ¬[¬a×¬¬a] : ¬ (¬ A × ¬ ¬ A)
  ¬[¬a×¬¬a] ⟨ ¬a , ¬¬a ⟩ = ¬¬a ¬a


{-
⊤⊥-iso : (¬ ⊥) ≃ ⊤
⊤⊥-iso =
  record
    { to      =  λ{ _ → tt }
    ; from    =  λ{ _ → id }
    ; from∘to =  λ{ _ → extensionality (λ ()) }
    ; to∘from =  λ{ tt → refl }
    }
-}
\end{code}  

*Existentials and Universals*

\begin{code}
{-
∃¬¬∀ : ∀ {A : Set} {B : A → Set} → ∃ (λ (x : A) → ¬ B x) → ¬ (∀ (x : A) → B x)
∃¬¬∀ (x , ¬bx) ∀bx = ¬bx (∀bx x)
-}
\end{code}
