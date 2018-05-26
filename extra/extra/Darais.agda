-- Author: David Darais
--
-- This is a dependent de Bruijn encoding of STLC with proofs for
-- progress and preservation. This file has zero dependencies and is
-- 100% self-contained.
--
-- Because there is only a notion of well-typed terms (non-well-typed
-- terms do not exist), preservation is merely by observation that
-- substitution (i.e., cut) can be defined.
--
-- A small-step evaluation semantics is defined after the definition of cut.
--
-- Progress is proved w.r.t. the evaluation semantics.
--
-- Some ideas for extensions or homeworks are given at the end.
--
-- A few helper definitions are required.
-- * Basic Agda constructions (like booleans, products, dependent sums,
--   and lists) are defined first in a Prelude module which is
--   immediately opened.
-- * Binders (x : τ ∈ Γ) are proofs that the element τ is contained in
--   the list of types Γ. Helper functions for weakening and
--   introducing variables into contexts which are reusable are
--   defined in the Prelude. Helpers for weakening terms are defined
--   below. Some of the non-general helpers (like cut[∈]) could be
--   defined in a generic way to be reusable, but I decided against
--   this to keep things simple.

module Darais where

open import Agda.Primitive using (_⊔_)

module Prelude where

  infixr 3 ∃𝑠𝑡
  infixl 5 _∨_
  infix 10 _∈_
  infixl 15 _⧺_
  infixl 15 _⊟_
  infixl 15 _∾_
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

  _⧺_ : ∀ {ℓ} {A : Set ℓ} → ⟬ A ⟭ → ⟬ A ⟭ → ⟬ A ⟭
  [] ⧺ ys = ys
  x ∷ xs ⧺ ys = x ∷ (xs ⧺ ys)

  _∾_ : ∀ {ℓ} {A : Set ℓ} → ⟬ A ⟭ → ⟬ A ⟭ → ⟬ A ⟭
  [] ∾ ys = ys
  (x ∷ xs) ∾ ys = xs ∾ x ∷ ys

  data _∈_ {ℓ} {A : Set ℓ} (x : A) : ∀ (xs : ⟬ A ⟭) → Set ℓ where
    Z : ∀ {xs} → x ∈ x ∷ xs
    S : ∀ {x′ xs} → x ∈ xs → x ∈ x′ ∷ xs

  _⊟_ : ∀ {ℓ} {A : Set ℓ} (xs : ⟬ A ⟭) {x} → x ∈ xs → ⟬ A ⟭
  x ∷ xs ⊟ Z = xs
  x ∷ xs ⊟ S ε = x ∷ (xs ⊟ ε)

  wk[∈] : ∀ {ℓ} {A : Set ℓ} {xs : ⟬ A ⟭} {x : A} xs′ → x ∈ xs → x ∈ xs′ ∾ xs
  wk[∈] [] x = x
  wk[∈] (x′ ∷ xs) x = wk[∈] xs (S x)

  i[∈][_] : ∀ {ℓ} {A : Set ℓ} {xs : ⟬ A ⟭} {x x′ : A} (ε′ : x′ ∈ xs) → x ∈ xs ⊟ ε′ → x ∈ xs
  i[∈][ Z ] x = S x 
  i[∈][ S ε′ ] Z = Z
  i[∈][ S ε′ ] (S x) = S (i[∈][ ε′ ] x)

open Prelude

-- ============================ --
-- Simply Typed Lambda Calculus --
-- ============================ --

-- A dependent de Bruijn encoding
-- Or, the dynamic semantics of natural deduction as seen through Curry-Howard

-- types --

data type : Set where
  ⟨𝔹⟩ : type
  _⟨→⟩_ : type → type → type

-- terms --

infix 10 _⊢_
data _⊢_ : ∀ (Γ : ⟬ type ⟭) (τ : type) → Set where
  ⟨𝔹⟩ : ∀ {Γ}
    (b : 𝔹)
    → Γ ⊢ ⟨𝔹⟩
  ⟨if⟩_❴_❵❴_❵ : ∀ {Γ τ} 
    (e₁ : Γ ⊢ ⟨𝔹⟩)
    (e₂ : Γ ⊢ τ)
    (e₃ : Γ ⊢ τ)
    → Γ ⊢ τ
  Var : ∀ {Γ τ}
    (x : τ ∈ Γ)
    → Γ ⊢ τ
  ⟨λ⟩ : ∀ {Γ τ₁ τ₂}
    (e : τ₁ ∷ Γ ⊢ τ₂)
    → Γ ⊢ τ₁ ⟨→⟩ τ₂
  _⟨⋅⟩_ : ∀ {Γ τ₁ τ₂}
    (e₁ : Γ ⊢ τ₁ ⟨→⟩ τ₂)
    (e₂ : Γ ⊢ τ₁)
    → Γ ⊢ τ₂

-- introducing a new variable to the context --

i[⊢][_] : ∀ {Γ τ τ′} (x′ : τ′ ∈ Γ) → Γ ⊟ x′ ⊢ τ → Γ ⊢ τ
i[⊢][ x′ ] (⟨𝔹⟩ b) = ⟨𝔹⟩ b
i[⊢][ x′ ] ⟨if⟩ e₁ ❴ e₂ ❵❴ e₃ ❵ = ⟨if⟩ i[⊢][ x′ ] e₁ ❴ i[⊢][ x′ ] e₂ ❵❴ i[⊢][ x′ ] e₃ ❵
i[⊢][ x′ ] (Var x) = Var (i[∈][ x′ ] x)
i[⊢][ x′ ] (⟨λ⟩ e) = ⟨λ⟩ (i[⊢][ S x′ ] e)
i[⊢][ x′ ] (e₁ ⟨⋅⟩ e₂) = i[⊢][ x′ ] e₁ ⟨⋅⟩ i[⊢][ x′ ] e₂

i[⊢] : ∀ {Γ τ τ′} → Γ ⊢ τ → τ′ ∷ Γ ⊢ τ
i[⊢] = i[⊢][ Z ]

-- substitution for variables --

cut[∈]<_>[_] : ∀ {Γ τ₁ τ₂} (x : τ₁ ∈ Γ) Γ′ → Γ′ ∾ (Γ ⊟ x) ⊢ τ₁ → τ₂ ∈ Γ → Γ′ ∾ (Γ ⊟ x) ⊢ τ₂
cut[∈]< Z >[ Γ′ ] e Z = e
cut[∈]< Z >[ Γ′ ] e (S y) = Var (wk[∈] Γ′ y)
cut[∈]< S x′ >[ Γ′ ] e Z = Var (wk[∈] Γ′ Z)
cut[∈]< S x′ >[ Γ′ ] e (S x) = cut[∈]< x′ >[ _ ∷ Γ′ ] e x

cut[∈]<_> : ∀ {Γ τ₁ τ₂} (x : τ₁ ∈ Γ) → Γ ⊟ x ⊢ τ₁ → τ₂ ∈ Γ → Γ ⊟ x ⊢ τ₂
cut[∈]< x′ > = cut[∈]< x′ >[ [] ]

-- substitution for terms --

cut[⊢][_] : ∀ {Γ τ₁ τ₂} (x : τ₁ ∈ Γ) → Γ ⊟ x ⊢ τ₁ → Γ ⊢ τ₂ → Γ ⊟ x ⊢ τ₂
cut[⊢][ x′ ] e′ (⟨𝔹⟩ b) = ⟨𝔹⟩ b
cut[⊢][ x′ ] e′ ⟨if⟩ e₁ ❴ e₂ ❵❴ e₃ ❵ = ⟨if⟩ cut[⊢][ x′ ] e′ e₁ ❴ cut[⊢][ x′ ] e′ e₂ ❵❴ cut[⊢][ x′ ] e′ e₃ ❵
cut[⊢][ x′ ] e′ (Var x) = cut[∈]< x′ > e′ x
cut[⊢][ x′ ] e′ (⟨λ⟩ e) = ⟨λ⟩ (cut[⊢][ S x′ ] (i[⊢] e′) e)
cut[⊢][ x′ ] e′ (e₁ ⟨⋅⟩ e₂) = cut[⊢][ x′ ] e′ e₁ ⟨⋅⟩ cut[⊢][ x′ ] e′ e₂

cut[⊢] : ∀ {Γ τ₁ τ₂} → Γ ⊢ τ₁ → τ₁ ∷ Γ ⊢ τ₂ → Γ ⊢ τ₂
cut[⊢] = cut[⊢][ Z ]

-- values --

data value {Γ} : ∀ {τ} → Γ ⊢ τ → Set where
  ⟨𝔹⟩ : ∀ b → value (⟨𝔹⟩ b)
  ⟨λ⟩ : ∀ {τ τ′} (e : τ′ ∷ Γ ⊢ τ) → value (⟨λ⟩ e)

-- CBV evaluation for terms --
-- (borrowing some notation and style from Wadler: https://wenkokke.github.io/sf/Stlc)

infix 10 _↝_
data _↝_ {Γ τ} : Γ ⊢ τ → Γ ⊢ τ → Set where
  ξ⋅₁ : ∀ {τ′} {e₁ e₁′ : Γ ⊢ τ′ ⟨→⟩ τ} {e₂ : Γ ⊢ τ′}
    → e₁ ↝ e₁′
    → e₁ ⟨⋅⟩ e₂ ↝ e₁′ ⟨⋅⟩ e₂
  ξ⋅₂ : ∀ {τ′} {e₁ : Γ ⊢ τ′ ⟨→⟩ τ} {e₂ e₂′ : Γ ⊢ τ′}
    → value e₁
    → e₂ ↝ e₂′
    → e₁ ⟨⋅⟩ e₂ ↝ e₁ ⟨⋅⟩ e₂′
  βλ : ∀ {τ′} {e₁ : τ′ ∷ Γ ⊢ τ} {e₂ : Γ ⊢ τ′}
    → value e₂
    → ⟨λ⟩ e₁ ⟨⋅⟩ e₂ ↝ cut[⊢] e₂ e₁
  ξif : ∀ {e₁ e₁′ : Γ ⊢ ⟨𝔹⟩} {e₂ e₃ : Γ ⊢ τ}
    → e₁ ↝ e₁′
    → ⟨if⟩ e₁ ❴ e₂ ❵❴ e₃ ❵ ↝ ⟨if⟩ e₁′ ❴ e₂ ❵❴ e₃ ❵
  ξif-T : ∀ {e₂ e₃ : Γ ⊢ τ}
    → ⟨if⟩ ⟨𝔹⟩ T ❴ e₂ ❵❴ e₃ ❵ ↝ e₂
  ξif-F : ∀ {e₂ e₃ : Γ ⊢ τ}
    → ⟨if⟩ ⟨𝔹⟩ F ❴ e₂ ❵❴ e₃ ❵ ↝ e₃

-- progress --

progress : ∀ {τ} (e : [] ⊢ τ) → value e ∨ (∃ e′ ⦂ [] ⊢ τ 𝑠𝑡 e ↝ e′)
progress (⟨𝔹⟩ b) = Inl (⟨𝔹⟩ b)
progress ⟨if⟩ e ❴ e₁ ❵❴ e₂ ❵ with progress e
… | Inl (⟨𝔹⟩ T) = Inr ⟨∃ e₁ , ξif-T ⟩
… | Inl (⟨𝔹⟩ F) = Inr ⟨∃ e₂ , ξif-F ⟩
… | Inr ⟨∃ e′ , ε ⟩ = Inr ⟨∃ ⟨if⟩ e′ ❴ e₁ ❵❴ e₂ ❵ , ξif ε ⟩
progress (Var ())
progress (⟨λ⟩ e) = Inl (⟨λ⟩ e)
progress (e₁ ⟨⋅⟩ e₂) with progress e₁ 
… | Inr ⟨∃ e₁′ , ε ⟩ = Inr ⟨∃ e₁′ ⟨⋅⟩ e₂ , ξ⋅₁ ε ⟩
… | Inl (⟨λ⟩ e) with progress e₂
… | Inl x = Inr ⟨∃ cut[⊢] e₂ e , βλ x ⟩
… | Inr ⟨∃ e₂′ , ε ⟩ = Inr ⟨∃ e₁ ⟨⋅⟩ e₂′ , ξ⋅₂ (⟨λ⟩ e) ε ⟩ 

-- Some ideas for possible extensions or homework assignments
-- 1. A. Write a conversion from the dependent de Bruijn encoding (e : Γ ⊢ τ)
--       to the untyped lambda calculus (e : term).
--    B. Prove that the image of this conversion is well typed.
--    C. Write a conversion from well-typed untyped lambda calculus
--       terms ([e : term] and [ε : (Γ ⊢ e ⦂ τ)] into the dependent de
--       Bruijn encoding (e : Γ ⊢ τ)
-- 2. A. Write a predicate analogous to 'value' for strongly reduced
--       terms (reduction under lambda)
--    B. Prove "strong" progress: A term is either fully beta-reduced
--       (including under lambda) or it can take a step
-- 3. Relate this semantics to a big-step semantics.
-- 4. Prove strong normalization.
-- 5. Relate this semantics to a definitional interpreter into Agda's Set.
