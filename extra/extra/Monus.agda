open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≥_; _≤_; z≤n; s≤s)
open import Function.Equivalence using (_⇔_)
open import Relation.Binary.PropositionalEquality using (→-to-⟶)

postulate
  adjoint : ∀ {x y z} → x + y ≥ z ⇔ x ≥ z ∸ y
  unit : ∀ {x y} → x ≥ (x + y) ∸ y
  apply : ∀ {x y} → (x ∸ y) + y ≥ x

