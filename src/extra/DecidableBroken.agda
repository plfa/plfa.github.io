import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (Dec; yes; no)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no λ()
suc m ≤? suc n with m ≤? n
... | yes m≤n = yes (s≤s m≤n)
... | no ¬m≤n = no λ{ (s≤s m≤n) → ¬m≤n m≤n }

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no {!!}
_ = refl

{-
Using ^C ^N, the term 
  4 ≤? 2
evaluates to
  no (λ { (s≤s m≤n) → (λ { (s≤s m≤n) → (λ ()) 1 m≤n }) m≤n })
The 1 is spurious.
-}
