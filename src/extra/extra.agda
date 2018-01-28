postulate
  extensionality : ∀ {A B : Set} → {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

extensionality2 : ∀ {A B C : Set} → {f g : A → B → C} → (∀ (x : A) (y : B) → f x y ≡ g x y) → f ≡ g
extensionality2 fxy≡gxy = extensionality (λ x → extensionality (λ y → fxy≡gxy x y))

