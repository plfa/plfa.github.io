open import Relation.Binary.PropositionalEquality using (_≡_)

data Unit : Set where
  unit : Unit

data Bool : Set where
  false : Bool
  true : Bool

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

ℕ→Bool : ℕ → Bool
ℕ→Bool zero = false
ℕ→Bool (suc _) = true

with-confusion : (m : ℕ) → ℕ→Bool (suc m) ≡ true → Unit
with-confusion m p-<= with ℕ→Bool (suc m)
... | true = unit
... | false = unit -- Without this case, we get "Incomplete pattern matching".
  where
    -- (ℕ→Bool (suc m) ≡ true) was unified with (false ≡ false):
    p-<=′ : false ≡ false
    p-<=′ = p-<=

with-confusion-fixed : (m : ℕ) → ℕ→Bool (suc m) ≡ true → Unit
with-confusion-fixed m p-<= = unit -- This is the true case.

with-confusion-simpler : (m : ℕ) → Unit
with-confusion-simpler m with true
... | true = unit
... | false = unit -- Without this case, we get "Incomplete pattern matching".
