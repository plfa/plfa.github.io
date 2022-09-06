module experimental.itaiz.Isomorphism.Cantor where

open import Data.Bool using (Bool; false; true; not)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (¬_)

open import experimental.itaiz.Isomorphism using (_≲_)

nb≢b : {b : Bool} → not b ≢ b
nb≢b {false} ()
nb≢b {true} ()

ℙ : Set → Set
ℙ A = A → Bool

cantor : (A : Set) → ¬ (ℙ A ≲ A)
cantor A ℙA≲A = missing-α (to α , refl)
  where
    open _≲_ ℙA≲A
    α : ℙ A
    α n = not (from n n)
    missing-α : ¬ (∃[ n ] to α ≡ n)
    missing-α (n , toα≡n) = nb≢b (
      begin
        not (from n n)
      ≡⟨⟩
        α n
      ≡⟨ cong (λ x → x n) (sym (from∘to α)) ⟩
        from (to α) n
      ≡⟨ cong (λ x → from x n) toα≡n ⟩
        from n n
      ∎)
