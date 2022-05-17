module experimental.itaiz.Modulo where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

_mod_ : ℕ → ℕ → ℕ
m mod zero = zero
m mod suc n = go zero m n
  where
    go : ℕ → ℕ → ℕ → ℕ
    go acc zero n' = acc
    go acc (suc m') zero = go zero m' n
    go acc (suc m') (suc n') = go (suc acc) m' n'

_ : 7 mod 3 ≡ 1
_ = refl
