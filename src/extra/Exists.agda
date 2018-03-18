import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple using (+-suc; +-right-identity)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data ∃ {A : Set} (B : A → Set) : Set where
  _,_ : (x : A) → B x → ∃ B

syntax ∃ {A} (λ x → B) = ∃[ x ∈ A ] B


data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc   : ∀ {n : ℕ} → even n → odd (suc n)

lemma : ∀ (m : ℕ) →  2 * suc m ≡ suc (suc (2 * m))
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

∃-even : ∀ {n : ℕ} → even n → ∃[ m ∈ ℕ ] (n ≡ 2 * m)
∃-odd  : ∀ {n : ℕ} →  odd n → ∃[ m ∈ ℕ ] (n ≡ 1 + 2 * m)

∃-even even-zero =  zero , refl
∃-even (even-suc o) with ∃-odd o
...                    | m , eqn rewrite eqn = suc m , sym (lemma m)

∃-odd  (odd-suc e)  with ∃-even e
...                    | m , eqn rewrite eqn = m , refl

∃-even′ : ∀ {n : ℕ} → even n → ∃[ m ∈ ℕ ] (n ≡ 2 * m)
∃-even′ even-zero =  zero , refl
∃-even′ (even-suc o) with ∃-odd o
...                    | m , eqn rewrite eqn | cong suc (+-right-identity m) = suc m , {!!}
