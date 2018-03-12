module DaraisPhoas where

open import Agda.Primitive using (_⊔_)

module Prelude where

  infixr 3 ∃𝑠𝑡
  infixl 5 _∨_
  infixr 20 _∷_
  
  data 𝔹 : Set where
    T : 𝔹
    F : 𝔹

  data _∨_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    Inl : A → A ∨ B
    Inr : B → A ∨ B

  syntax ∃𝑠𝑡 A (λ x → B) = ∃ x ⦂ A 𝑠𝑡 B
  data ∃𝑠𝑡 {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    ⟨∃_,_⟩ : ∀ (x : A) → B x → ∃ x ⦂ A 𝑠𝑡 B x

  data ⟬_⟭ {ℓ} (A : Set ℓ) : Set ℓ where
    [] : ⟬ A ⟭
    _∷_ : A → ⟬ A ⟭ → ⟬ A ⟭

open Prelude

infixr 15 _⟨→⟩_
data type : Set where
  ⟨ℕ⟩   : type
  _⟨→⟩_ : type → type → type

infixl 15 _⟨∙⟩_
data exp-phoas (var : type → ⟬ type ⟭ → Set) : ∀ (Γ : ⟬ type ⟭) (τ : type) → Set where
  Var : ∀ {Γ τ}
    (x : var τ Γ)
    → exp-phoas var Γ τ
  ⟨λ⟩ : ∀ {Γ τ₁ τ₂}
    (e : var τ₁ (τ₁ ∷ Γ) → exp-phoas var (τ₁ ∷ Γ) τ₂)
    → exp-phoas var Γ (τ₁ ⟨→⟩ τ₂)
  _⟨∙⟩_ : ∀ {Γ τ₁ τ₂}
    (e₁ : exp-phoas var Γ (τ₁ ⟨→⟩ τ₂))
    (e₂ : exp-phoas var Γ τ₁)
    → exp-phoas var Γ τ₂

infix 10 _∈_
data _∈_ {ℓ} {A : Set ℓ} (x : A) : ∀ (xs : ⟬ A ⟭) → Set ℓ where
  Z : ∀ {xs} → x ∈ x ∷ xs
  S : ∀ {x′ xs} → x ∈ xs → x ∈ x′ ∷ xs

infix 10 _⊢_
data _⊢_ : ∀ (Γ : ⟬ type ⟭) (τ : type) → Set where
  Var : ∀ {Γ τ}
    (x : τ ∈ Γ)
    → Γ ⊢ τ
  ⟨λ⟩ : ∀ {Γ τ₁ τ₂}
    (e : τ₁ ∷ Γ ⊢ τ₂)
    → Γ ⊢ τ₁ ⟨→⟩ τ₂
  _⟨∙⟩_ : ∀ {Γ τ₁ τ₂}
    (e₁ : Γ ⊢ τ₁ ⟨→⟩ τ₂)
    (e₂ : Γ ⊢ τ₁)
    → Γ ⊢ τ₂

⟦_⟧₁ : ∀ {Γ τ} (e : exp-phoas _∈_ Γ τ) → Γ ⊢ τ
⟦ Var x ⟧₁ = Var x
⟦ ⟨λ⟩ e ⟧₁ = ⟨λ⟩ ⟦ e Z ⟧₁
⟦ e₁ ⟨∙⟩ e₂ ⟧₁ = ⟦ e₁ ⟧₁ ⟨∙⟩ ⟦ e₂ ⟧₁

⟦_⟧₂ : ∀ {Γ τ} (e : Γ ⊢ τ) → exp-phoas _∈_ Γ τ
⟦ Var x ⟧₂ = Var x
⟦ ⟨λ⟩ e ⟧₂ = ⟨λ⟩ (λ _ → ⟦ e ⟧₂)
⟦ e₁ ⟨∙⟩ e₂ ⟧₂ = ⟦ e₁ ⟧₂ ⟨∙⟩ ⟦ e₂ ⟧₂

Ch : type
Ch =  (⟨ℕ⟩ ⟨→⟩ ⟨ℕ⟩) ⟨→⟩ ⟨ℕ⟩ ⟨→⟩ ⟨ℕ⟩

twoDB : [] ⊢ Ch
twoDB = ⟨λ⟩ (⟨λ⟩ (Var (S Z) ⟨∙⟩ (Var (S Z) ⟨∙⟩ Var Z)))

twoPH : exp-phoas _∈_ [] Ch
twoPH = ⟨λ⟩ (λ f → ⟨λ⟩ (λ x → Var f ⟨∙⟩ (Var f ⟨∙⟩ Var x)))

{-
/Users/wadler/sf/src/extra/DaraisPhoas.agda:82,9-60
⟨ℕ⟩ ⟨→⟩ ⟨ℕ⟩ != ⟨ℕ⟩ of type type
when checking that the expression
⟨λ⟩ (λ f → ⟨λ⟩ (λ x → Var f ⟨∙⟩ (Var f ⟨∙⟩ Var x))) has type
exp-phoas _∈_ [] Ch
-}
