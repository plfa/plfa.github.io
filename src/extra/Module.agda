module Module where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = zero
suc m + n = suc (m + n)

import Data.Nat using (ℕ; zero; suc; _+_)

