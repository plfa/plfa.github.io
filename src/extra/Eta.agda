import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Function using (_∘_)
open import Data.Product using (_×_) using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)


postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

β-×₁ : ∀ {A B : Set} (x : A) (y : B) → proj₁ (x , y) ≡ x
β-×₁ x y = refl

β-×₂ : ∀ {A B : Set} (x : A) (y : B) → proj₂ (x , y) ≡ y
β-×₂ x y = refl

η-× : ∀ {A B : Set} (w : A × B) → (proj₁ w , proj₂ w) ≡ w
η-× (x , y) = refl

uniq-× : ∀ {A B C : Set} (h : C → A × B) (v : C) → (proj₁ (h v) , proj₂ (h v)) ≡ h v
uniq-× h v = η-× (h v)

⊎-elim : ∀ {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
⊎-elim f g (inj₁ x) = f x
⊎-elim f g (inj₂ y) = g y

β-⊎₁ : ∀ {A B C : Set} (f : A → C) (g : B → C) (x : A) → ⊎-elim f g (inj₁ x) ≡ f x
β-⊎₁ f g x = refl

β-⊎₂ : ∀ {A B C : Set} (f : A → C) (g : B → C) (y : B) → ⊎-elim f g (inj₂ y) ≡ g y
β-⊎₂ f g x = refl

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → ⊎-elim inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

natural-⊎ : ∀ {A B C D : Set} (f : A → C) (g : B → C) (h : C → D) (w : A ⊎ B) → ⊎-elim (h ∘ f) (h ∘ g) w ≡ (h ∘ ⊎-elim f g) w
natural-⊎ f g h (inj₁ x) = refl
natural-⊎ f g h (inj₂ y) = refl

uniq-⊎ : ∀ {A B C  : Set} (h : A ⊎ B → C) (w : A ⊎ B) → ⊎-elim (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h w rewrite natural-⊎ inj₁ inj₂ h w | η-⊎ w = refl

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

uniq-⊤ : ∀ {C : Set} (h : C → ⊤) (v : C) → tt ≡ h v
uniq-⊤ h v = η-⊤ (h v)

η-⊥ : ∀ (w : ⊥) → ⊥-elim w ≡ w
η-⊥ ()

natural-⊥ : ∀ {C D : Set} (h : C → D) (w : ⊥) → ⊥-elim w ≡ (h ∘ ⊥-elim) w
natural-⊥ h ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h w rewrite natural-⊥ h w | η-⊥ w = refl

η-→ : ∀ {A B : Set} (f : A → B) → (λ{x → f x}) ≡ f
η-→ {A} {B} f = extensionality η-helper
  where
  η-lhs : A → B
  η-lhs = λ{x → f x}

  η-helper : (x : A) → η-lhs x ≡ f x
  η-helper x = refl

