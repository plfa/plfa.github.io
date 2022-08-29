module experimental.itaiz.Isomorphism.Fin where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s; _+_; _*_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import experimental.itaiz.Isomorphism

Fn≃∃<n : (n : ℕ) → Fin n ≃ ∃[ i ] i < n
Fn≃∃<n n = record { to = to n; from = from n; from∘to = from∘to n; to∘from = to∘from n }
  where
    to : (n : ℕ) → Fin n → ∃[ i ] i < n
    to (suc n) zero = zero , s≤s z≤n
    to (suc n) (suc j) with to n j
    ... | i , i<n = suc i , s≤s i<n

    from : (n : ℕ) → ∃[ i ] i < n → Fin n
    from (suc n) (zero , s≤s z≤n) = zero
    from (suc n) (suc i , s≤s i<n) = suc (from n (i , i<n))

    from∘to : (n : ℕ) → (j : Fin n) → from n (to n j) ≡ j
    from∘to (suc n) zero = refl
    from∘to (suc n) (suc j) = cong suc (from∘to n j)

    to∘from : (n : ℕ) → (z : ∃[ i ] i < n) → to n (from n z) ≡ z
    to∘from (suc n) (zero , s≤s z≤n) = refl
    to∘from (suc n) (suc i , s≤s i<n) = cong (λ{ (j , j<n) → suc j , s≤s j<n }) (to∘from n (i , i<n))

Fm⊎Fn≃Fm+n : (m n : ℕ) → Fin m ⊎ Fin n ≃ Fin (m + n)
Fm⊎Fn≃Fm+n m n = record { to = to m n ; from = from m n ; from∘to = from∘to m n ; to∘from = to∘from m n }
  where
    to : (m n : ℕ) → Fin m ⊎ Fin n → Fin (m + n)
    to zero n (inj₂ y) = y
    to (suc m) n (inj₁ zero) = zero
    to (suc m) n (inj₁ (suc i)) = suc (to m n (inj₁ i))
    to (suc m) n (inj₂ j) = suc (to m n (inj₂ j))
    
    from : (m n : ℕ) → Fin (m + n) → Fin m ⊎ Fin n
    from zero n x = inj₂ x
    from (suc m) n zero = inj₁ zero
    from (suc m) n (suc x) with from m n x
    ... | inj₁ i = inj₁ (suc i)
    ... | inj₂ j = inj₂ j

    from∘to : (m n : ℕ) → (x : Fin m ⊎ Fin n) → from m n (to m n x) ≡ x
    from∘to zero n (inj₂ j) = refl
    from∘to (suc m) n (inj₁ zero) = refl
    from∘to (suc m) n (inj₁ (suc i)) rewrite from∘to m n (inj₁ i) = refl
    from∘to (suc m) n (inj₂ j) rewrite from∘to m n (inj₂ j) = refl

    to∘from : (m n : ℕ) → (x : Fin (m + n)) → to m n (from m n x) ≡ x
    to∘from zero n x = refl
    to∘from (suc m) n zero = refl
    to∘from (suc m) n (suc x) with from m n x in eq
    ... | inj₁ i rewrite sym eq = cong suc (to∘from m n x)
    ... | inj₂ j rewrite sym eq = cong suc (to∘from m n x)

A⊎Fn≃Fsn×A : {n : ℕ} {A : Set} → A ⊎ (Fin n × A) ≃ Fin (suc n) × A
A⊎Fn≃Fsn×A {n} {A} = record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
  where
    to : A ⊎ (Fin n × A) → Fin (suc n) × A
    to (inj₁ a) = zero , a
    to (inj₂ (n , a)) = (suc n) , a
    
    from : Fin (suc n) × A → A ⊎ (Fin n × A)
    from (zero , a) = inj₁ a
    from (suc n , a) = inj₂ (n , a)
    
    from∘to : (x : A ⊎ (Fin n × A)) → from (to x) ≡ x
    from∘to (inj₁ a) = refl
    from∘to (inj₂ (n , a)) = refl
    
    to∘from : (y : Fin (suc n) × A) → to (from y) ≡ y
    to∘from (zero , a) = refl
    to∘from (suc n , a) = refl

open ≃-Reasoning

Fm×Fn≃Fm*n : (m n : ℕ) → Fin m × Fin n ≃ Fin (m * n)
Fm×Fn≃Fm*n zero n = record { to = λ{ () } ; from = λ{ () } ; from∘to = λ{ () }; to∘from = λ{ () }}
Fm×Fn≃Fm*n (suc m) n =
  ≃-begin
    (Fin (suc m) × Fin n)
  ≃⟨ ≃-sym A⊎Fn≃Fsn×A ⟩
    (Fin n ⊎ (Fin m × Fin n))
  ≃⟨ ≃-⊎ˡ (Fm×Fn≃Fm*n m n) ⟩
    (Fin n ⊎ (Fin (m * n)))
  ≃⟨ Fm⊎Fn≃Fm+n n (m * n) ⟩
    Fin (n + m * n)
  ≃⟨ ≃-refl ⟩
    Fin ((suc m) * n)
  ≃-∎
