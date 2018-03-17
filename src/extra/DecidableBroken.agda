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

_ : Dec (2 ≤ 4)
_ = 2 ≤? 4   -- yes (s≤s (s≤s z≤n))

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : Dec (4 ≤ 2)
_ = 4 ≤? 2   -- no λ{(s≤s (s≤s ()))}

_ : 4 ≤? 2 ≡ no (λ { (s≤s m≤n) → (λ { (s≤s m≤n) → (λ ()) m≤n }) m≤n })
_ = refl

{-
/Users/wadler/sf/src/extra/DecidableBroken.agda:27,5-9
(λ { (s≤s m≤n) → (λ { (s≤s m≤n) → (λ ()) 1 m≤n }) m≤n }) x !=
(λ { (s≤s m≤n) → _34 m≤n }) x of type .Data.Empty.⊥
when checking that the expression refl has type
(4 ≤? 2) ≡ no (λ { (s≤s m≤n) → _34 m≤n })
-}
