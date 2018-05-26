import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
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

lemma : ∀ (m : ℕ) → 2 * suc m ≡ suc (suc (2 * m))
lemma m =
  begin
    2 * suc m
  ≡⟨⟩
    suc m + (suc m + zero)
  ≡⟨⟩
    suc (m + (suc (m + zero)))
  ≡⟨ cong suc (+-suc m (m + zero)) ⟩
    suc (suc (m + (m + zero)))
  ≡⟨⟩
    suc (suc (2 * m))
  ∎

∃-even : ∀ {n : ℕ} → even n → ∃[ m ] (2 * m ≡ n)
∃-odd  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + 2 * m ≡ n)

∃-even even-zero =  zero , refl
∃-even (even-suc o) with ∃-odd o
...                    | m , refl = suc m , lemma m

∃-odd  (odd-suc e)  with ∃-even e
...                    | m , refl = m , refl

∃-even′ : ∀ {n : ℕ} → even n → ∃[ m ] (n ≡ 2 * m)
∃-odd′  : ∀ {n : ℕ} →  odd n → ∃[ m ] (n ≡ 1 + 2 * m)

∃-even′ even-zero =  zero , refl
∃-even′ (even-suc o) with ∃-odd′ o
...                     | m , eqn rewrite eqn | +-suc m (m + 0) = suc m , {!!}

∃-odd′  (odd-suc e)  with ∃-even′ e
...                     | m , eqn rewrite eqn = m , refl

data Even : ℕ → Set where
  ev0 : Even zero
  ev2 : ∀ {n} → Even n → Even (suc (suc n))

ev-ex : ∀ {n : ℕ} → Even n → ∃[ m ] (2 * m ≡ n)
ev-ex ev0 =  (zero , refl)
ev-ex (ev2 ev) with ev-ex ev
... | (m , refl) = (suc m , lemma m)

