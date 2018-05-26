\begin{code}
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)
\end{code}

Two halves of de Morgan's laws hold intuitionistically.  The other two
halves are each equivalent to the law of double negation.

\begin{code}
dem1 : ∀ {A B : Set} → A × B → ¬ (¬ A ⊎ ¬ B)
dem1 (a , b) (inj₁ ¬a) = ¬a a
dem1 (a , b) (inj₂ ¬b) = ¬b b

dem2 : ∀ {A B : Set} → A ⊎ B → ¬ (¬ A × ¬ B)
dem2 (inj₁ a) (¬a , ¬b) = ¬a a
dem2 (inj₂ b) (¬a , ¬b) = ¬b b
\end{code}

For the other variant of De Morgan's law, one way is an isomorphism.
\begin{code}
-- dem-≃ : ∀ {A B : Set} → (¬ (A ⊎ B)) ≃ (¬ A × ¬ B)
-- dem-≃ = →-distributes-⊎
\end{code}

The other holds in only one direction.
\begin{code}
dem-half : ∀ {A B : Set} → ¬ A ⊎ ¬ B → ¬ (A × B)
dem-half (inj₁ ¬a) (a , b) = ¬a a
dem-half (inj₂ ¬b) (a , b) = ¬b b
\end{code}

The other variant does not appear to be equivalent to classical logic.
So that undermines my idea that basic propositions are either true
intuitionistically or equivalent to classical logic.

For several of the laws equivalent to classical logic, the reverse
direction holds in intuitionistic long.
\begin{code}
implication-inv : ∀ {A B : Set} → (¬ A ⊎ B) → A → B
implication-inv (inj₁ ¬a) a = ⊥-elim (¬a a)
implication-inv (inj₂ b)  a = b

demorgan-inv : ∀ {A B : Set} → A ⊎ B → ¬ (¬ A × ¬ B)
demorgan-inv (inj₁ a) (¬a , ¬b) =  ¬a a
demorgan-inv (inj₂ b) (¬a , ¬b) =  ¬b b
\end{code}

