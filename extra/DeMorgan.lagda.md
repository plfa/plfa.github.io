```
module DeMorgan where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

postulate
  dne : ∀ {A : Set} → ¬ ¬ A → A

dm : ∀ {A B : Set} → ¬ (A × B) → (¬ A) ⊎ (¬ B)
dm ¬xy = dne (λ k → k (inj₁ (λ x → k (inj₂ (λ y → ¬xy ⟨ x , y ⟩)))))
```
