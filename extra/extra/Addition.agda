import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc)


_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

+-assoc′ : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


{-
Goal: ℕ
————————————————————————————————————————————————————————————
n : ℕ
-}

{-
Goal: ℕ
————————————————————————————————————————————————————————————
n : ℕ
m : ℕ
-}
