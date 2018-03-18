import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple using (+-suc)
open import Data.Product using (∃; ∃-syntax; _,_)

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc   : ∀ {n : ℕ} → even n → odd (suc n)

∃-even : ∀ {n : ℕ} → even n → ∃[ m ] (n ≡ 2 * m)
∃-odd  : ∀ {n : ℕ} →  odd n → ∃[ m ] (n ≡ 1 + 2 * m)

∃-even even-zero =  zero , refl
∃-even (even-suc o) with ∃-odd o
...                    | m , eqn rewrite eqn | sym (+-suc m (m + 0)) = suc m , refl

∃-odd  (odd-suc e)  with ∃-even e
...                    | m , eqn rewrite eqn = m , refl

∃-even′ : ∀ {n : ℕ} → even n → ∃[ m ] (n ≡ 2 * m)
∃-odd′  : ∀ {n : ℕ} →  odd n → ∃[ m ] (n ≡ 1 + 2 * m)

∃-even′ even-zero =  zero , refl
∃-even′ (even-suc o) with ∃-odd′ o
...                     | m , eqn rewrite eqn | +-suc m (m + 0) = suc m , ?

∃-odd′  (odd-suc e)  with ∃-even′ e
...                     | m , eqn rewrite eqn = m , refl

