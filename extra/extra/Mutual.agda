open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)
data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)

mutual
  data even′ : ℕ → Set where
    zero : even′ zero
    suc : ∀ {n : ℕ} → odd′ n → even′ (suc n)
  data odd′ : ℕ → Set where
    suc : ∀ {n : ℕ} → even′ n → odd′ (suc n)

{-
/Users/wadler/sf/src/extra/Mutual.agda:3,6-10
Missing definition for even
-}

