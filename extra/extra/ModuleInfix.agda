module ModuleInfix where

open import Data.List using (List; _∷_; [])
open import Data.Bool using (Bool; true; false)

module Sort(A : Set)(_≤_ : A → A → Bool)(_⊝_ : A → A → A)(zero : A) where

  infix 1 _≤_
  infix 2 _⊝_

  insert : A → List A → List A
  insert x [] = x ∷ []
  insert x (y ∷ ys) with zero ≤ (y ⊝ x)
  insert x (y ∷ ys)    | true  = x ∷ y ∷ ys
  insert x (y ∷ ys)    | false = y ∷ insert x ys

  sort : List A → List A
  sort []       = []
  sort (x ∷ xs) = insert x (sort xs)
