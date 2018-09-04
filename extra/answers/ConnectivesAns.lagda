---
title     : "Connectives Answers"
layout    : page
permalink : /ConnectivesAns
---

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Equivalence using (_⇔_)
\end{code}

#### Exercise (`⊎-weak-×`)

\begin{code}
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , z ⟩  =  inj₁ x
⊎-weak-× ⟨ inj₂ y , z ⟩  =  inj₂ ⟨ y , z ⟩
\end{code}

The corresponding full laws is:

    (A ⊎ B) × C ⇔ (A × C) ⊎ (B × C)

The weak version replaces `A × C` by `A`, and the equivalence by a
left-to-right implication.
