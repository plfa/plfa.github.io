import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (∃; _,_)

+-assoc : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
+-assoc zero n p =
  begin
    zero + (n + p)
  ≡⟨⟩
    n + p
  ≡⟨⟩
    (zero + n) + p
  ∎
+-assoc (suc m) n p =
  begin
    suc m + (n + p)
  ≡⟨⟩
    suc (m + (n + p))
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc ((m + n) + p)
  ≡⟨⟩
    (suc m + n) + p
  ∎

+-identity : ∀ (m : ℕ) → m + zero ≡ m
+-identity zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identity (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identity m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
    n * p
  ≡⟨⟩
    zero * p + n * p
  ∎
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (_+_ p) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ +-assoc p (m * p) (n * p) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎
  



data even : ℕ → Set where
  ev0 : even zero
  ev+2 : ∀ {n : ℕ} → even n → even (suc (suc n))

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
  
ev-ex : ∀ {n : ℕ} → even n → ∃(λ (m : ℕ) → 2 * m ≡ n)
ev-ex ev0 =  (0 , refl)
ev-ex (ev+2 ev) with ev-ex ev
... | (m , refl) = (suc m , lemma m)

ex-ev : ∀ {n : ℕ} → ∃(λ (m : ℕ) → 2 * m ≡ n) → even n
ex-ev (zero , refl) = ev0
ex-ev (suc m , refl) rewrite lemma m = ev+2 (ex-ev (m , refl))


-- I can't see how to avoid using rewrite in the second proof,
-- or how to use rewrite in the first proof!


