module experimental.iharbury.NatNatIso where

open import Data.Empty
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties
open import Relation.Nullary

suc-× : ℕ × ℕ → ℕ × ℕ
suc-× (x , zero) = 0 , suc x
suc-× (x , suc y) = suc x , y

to : ℕ → ℕ × ℕ
to zero = 0 , 0
to (suc x) = suc-× (to x)

from₁ : ℕ → ℕ → ℕ
from₁ zero zero = 0
from₁ zero (suc d) = suc (from₁ d d)
from₁ (suc x) d = suc (from₁ x d)

from : ℕ × ℕ → ℕ
from (x , y) = from₁ x (x + y)

from∘to : (x : ℕ) → from (to x) ≡ x
from∘to zero = refl
from∘to (suc x) with to x | from∘to x
... | y , zero | from∘to-x
    rewrite +-identityʳ y
          | from∘to-x
    = refl
... | y , suc z | from∘to-x
    rewrite +-suc y z
          | from∘to-x
    = refl

to∘from₁ : (x y d : ℕ) → x + y ≡ d →
    to (from (x , y)) ≡ (x , y)
to∘from₁ zero y zero x+y-eq
    rewrite x+y-eq
    = refl
to∘from₁ zero y (suc d) x+y-eq
    with to∘from₁ d 0 d (+-identityʳ d)
... | to∘from-d-0
    rewrite x+y-eq
          | +-identityʳ d
          | to∘from-d-0
    = refl
to∘from₁ (suc x) y d x+y-eq
    rewrite sym (+-suc x y)
          | to∘from₁ x (suc y) d x+y-eq
    = refl

to∘from : (x : ℕ × ℕ) → to (from x) ≡ x
to∘from (x , y) = to∘from₁ x y (x + y) refl

theorem : ℕ ↔ (ℕ × ℕ)
theorem = record
    { f = to
    ; f⁻¹ = from
    ; cong₁ = cong to
    ; cong₂ = cong from
    ; inverse = to∘from , from∘to
    }
 