-- Nils' suggestion

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple using (+-suc)
open import Relation.Nullary using (¬_)
open import Function using (_∘_; id)
open import Data.Product using (_×_; _,_; proj₁; proj₂; map; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc   : ∀ {n : ℕ} → even n → odd (suc n)

∃-even : ∀ {n : ℕ} → even n → ∃[ m ] (n ≡ m * 2)
∃-odd  : ∀ {n : ℕ} →  odd n → ∃[ m ] (n ≡ 1 + m * 2)

∃-even even-zero    = zero , refl
∃-even (even-suc o) with ∃-odd o
...                    | m , refl = suc m , refl

∃-odd  (odd-suc  e) with ∃-even e
...                    | m , refl = m , refl
