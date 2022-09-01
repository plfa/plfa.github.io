module experimental.itaiz.Isomorphism where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x -- from∘to ≡ id
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

≃-refl : {A : Set} → A ≃ A
≃-refl = record
  { to = id
  ; from = id
  ; from∘to = λ _ → refl
  ; to∘from = λ _ → refl
  }

≃-trans : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C = record
  { to = to B≃C ∘ to A≃B
  ; from = from A≃B ∘ from B≃C
  ; from∘to = λ a → (begin
    from A≃B (from B≃C (to B≃C (to A≃B a)))
    ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B a)) ⟩
    from A≃B (to A≃B a)
    ≡⟨ from∘to A≃B a ⟩
    a
    ∎)
  ; to∘from = λ c → (begin
    to B≃C (to A≃B (from A≃B (from B≃C c)))
    ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C c)) ⟩
    to B≃C (from B≃C c)
    ≡⟨ to∘from B≃C c ⟩
    c
    ∎)
  }

≃-sym : {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B = record
  { to = from A≃B
  ; from = to A≃B
  ; from∘to = to∘from A≃B
  ; to∘from = from∘to A≃B
  }

≃-⊎ˡ : {X A B : Set} → A ≃ B → X ⊎ A ≃ X ⊎ B
≃-⊎ˡ A≃B = record
  { to = λ{ (inj₁ x) → inj₁ x ; (inj₂ a) → inj₂ (to A≃B a) }
  ; from = λ{ (inj₁ x) → inj₁ x ; (inj₂ b) → inj₂ (from A≃B b) }
  ; from∘to = λ{ (inj₁ x) → refl ; (inj₂ a) → cong inj₂ (from∘to A≃B a) }
  ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ b) → cong inj₂ (to∘from A≃B b) }
  }

≃-×ˡ : {X A B : Set} → A ≃ B → X × A ≃ X × B
≃-×ˡ A≃B = record
  { to = λ{ (x , a) → x , to A≃B a }
  ; from = λ{ (x , b) → x , from A≃B b }
  ; from∘to = λ{ (x , a) → cong (x ,_) (from∘to A≃B a) }
  ; to∘from = λ{ (x , b) → cong (x ,_) (to∘from A≃B b) }
  }

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : {A : Set} → A ≲ A
≲-refl = record
  { to = id
  ; from = id
  ; from∘to = λ _ → refl
  }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C = record
  { to = to B≲C ∘ to A≲B
  ; from = from A≲B ∘ from B≲C
  ; from∘to = λ a → (begin
    from A≲B (from B≲C (to B≲C (to A≲B a)))
    ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B a)) ⟩
    from A≲B (to A≲B a)
    ≡⟨ from∘to A≲B a ⟩
    a
    ∎)
  }

-- Levels are tricky here.
open import Agda.Primitive using (_⊔_)

record Preorder {ℓ₁ ℓ₂} {𝕏 : Set ℓ₁} (_≤_ : 𝕏 → 𝕏 → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    *-refl : {x : 𝕏} → x ≤ x
    *-trans : {x y z : 𝕏} → x ≤ y → y ≤ z → x ≤ z

open Preorder

module *-Reasoning {ℓ₁ ℓ₂} {𝕏 : Set ℓ₁} (_≤_ : 𝕏 → 𝕏 → Set ℓ₂) (R : Preorder _≤_) where
  infix  1 *-begin_
  infixr 2 _*⟨_⟩_
  infixr 2 _*⟨⟩_
  infix  3 _*-∎

  *-begin_ : {x y : 𝕏} → x ≤ y → x ≤ y
  *-begin_ x≤y = x≤y

  _*⟨_⟩_ : (x : 𝕏) {y z : 𝕏} → x ≤ y → y ≤ z → x ≤ z
  x *⟨ x≤y ⟩ y≤z = *-trans R x≤y y≤z

  _*⟨⟩_ : (x : 𝕏) {y : 𝕏} → x ≤ y → x ≤ y
  x *⟨⟩ x≤y = x≤y

  _*-∎ : (x : 𝕏) → x ≤ x
  x *-∎ = *-refl R

module ≃-Reasoning where
  open *-Reasoning
    (_≃_)
    (record { *-refl = ≃-refl ; *-trans = ≃-trans })
    renaming (*-begin_ to ≃-begin_ ; _*⟨_⟩_ to _≃⟨_⟩_; _*-∎ to _≃-∎)
    public

module ≲-Reasoning where
  open *-Reasoning
    (_≲_)
    (record { *-refl = ≲-refl ; *-trans = ≲-trans })
    renaming (*-begin_ to ≲-begin_ ; _*⟨_⟩_ to _≲⟨_⟩_; _*-∎ to _≲-∎)
    public
