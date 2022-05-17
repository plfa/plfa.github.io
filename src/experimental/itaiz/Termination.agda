module experimental.itaiz.Termination where

open import Data.Nat

record _⇒_ (A B : Set) : Set where
  field
    to : A → B

open _⇒_

{- Fails termination checker.

abc : ℕ ⇒ ℕ
abc = record
  { to = λ{ zero → zero ; (suc x) → to abc x }
  }

-}

test₁ : ℕ → ℕ
test₁ zero = zero
test₁ (suc n) = test₁ n

test₂ : ℕ → ℕ
test₂ = λ{ zero → zero ; (suc x) → test₂ x }

test₃ : ℕ → ℕ → ℕ
test₃ n zero = zero
test₃ n (suc m) = test₃ n m

test₄ : ℕ → ℕ → ℕ
test₄ n = λ{ zero → zero ; (suc m) → test₄ n m }

test₅ : ℕ → ℕ → ℕ
test₅ = λ{ n zero → zero ; n (suc m) → test₅ n m }
