module _ where

-- Ulf's example of why removing abstract may
-- cause a proof that used to work to now fail

-- Agda mailing list, 16 May 2018

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

module WithAbstract where

  abstract
    f : Nat → Nat
    f zero    = zero
    f (suc n) = suc (f n)

    lem : ∀ n → f n ≡ n
    lem zero    = refl
    lem (suc n) rewrite lem n = refl

  thm : ∀ m n → f (suc m) + n ≡ suc (m + n)
  thm m n rewrite lem (suc m) = refl
  -- Works.

  thm′ : ∀ m n → f (suc m) + n ≡ suc (m + n)
  thm′ m n = {!!}

{- Hole 0
Goal: f (suc m) + n ≡ suc (m + n)
————————————————————————————————————————————————————————————
n : Nat
m : Nat
-}

module WithoutAbstract where

  f : Nat → Nat
  f zero    = zero
  f (suc n) = suc (f n)

  lem : ∀ n → f n ≡ n
  lem zero    = refl
  lem (suc n) rewrite lem n = refl

  thm : ∀ m n → f (suc m) + n ≡ suc (m + n)
  thm m n rewrite lem (suc m) = {! refl!}
  -- Fails since rewrite doesn't trigger:
  --   lem (suc m)  : suc (f m)     ≡ suc m
  --   goal         : suc (f m + n) ≡ suc (m + n)

  -- NB: The problem is with the expansion of `f`,
  -- not with the expansion of the lemma

  thm′ : ∀ m n → f (suc m) + n ≡ suc (m + n)
  thm′ m n = {!!}

{- Holes 1 and 2
Goal: suc (f m + n) ≡ suc (m + n)
————————————————————————————————————————————————————————————
n : Nat
m : Nat
-}
