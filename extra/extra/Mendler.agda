module Mendler (F : Set → Set) where
open import Data.Product using (_×_)

Alg : Set → Set₁
Alg X = ∀ (R : Set) → (R → X) → F R → X

test : Set → Set
test A = A × A

test′ : ∀ (R : Set) → Set
test′ A = A × A
