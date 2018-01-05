open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

+-identity : ∀ (n : ℕ) → n + zero ≡ n
+-identity zero = refl
+-identity (suc n) rewrite +-identity n = refl

+-suc : ∀ (m n : ℕ) → n + suc m ≡ suc (n + m)
+-suc m zero = refl
+-suc m (suc n) rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n rewrite +-identity n = refl
+-comm (suc m) n rewrite +-suc m n | +-comm m n = refl

mutual
  data even : ℕ → Set where
    zero : even zero
    suc : ∀ {n : ℕ} → odd n → even (suc n)
  data odd : ℕ → Set where
    suc : ∀ {n : ℕ} → even n → odd (suc n)

+-lemma : ∀ (m : ℕ) → suc (suc (m + (m + 0))) ≡ suc m + (suc m + 0)
+-lemma m rewrite +-identity m | +-suc m m = refl

+-lemma′ : ∀ (m : ℕ) → suc (suc (m + (m + 0))) ≡ suc m + (suc m + 0)
+-lemma′ m rewrite +-suc m (m + 0) = {!!}

mutual
  is-even : ∀ (n : ℕ) → even n → ∃(λ (m : ℕ) → n ≡ 2 * m)
  is-even zero zero =  zero , refl
  is-even (suc n) (suc oddn) with is-odd n oddn
  ... | m , n≡1+2*m rewrite n≡1+2*m | +-lemma m = suc m , refl

  is-odd : ∀ (n : ℕ) → odd n → ∃(λ (m : ℕ) → n ≡ 1 + 2 * m)
  is-odd (suc n) (suc evenn) with is-even n evenn
  ... | m , n≡2*m rewrite n≡2*m = m , refl
