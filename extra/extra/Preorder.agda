open import Stlc hiding (⟹*-Preorder; _⟹*⟪_⟫_; example₀; example₁)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl)
open import Relation.Binary using (Preorder)
import Relation.Binary.PreorderReasoning as PreorderReasoning

⟹*-Preorder : Preorder _ _ _
⟹*-Preorder = record
  { Carrier    = Term
  ; _≈_        = _≡_
  ; _∼_        = _⟹*_
  ; isPreorder = record
    { isEquivalence = P.isEquivalence
    ; reflexive     = λ {refl → ⟨⟩}
    ; trans         = _>>_
    }
  }

open PreorderReasoning ⟹*-Preorder
     using (_IsRelatedTo_; begin_; _∎) renaming (_≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _⟹*⟨_⟩_)

infixr 2 _⟹*⟪_⟫_

_⟹*⟪_⟫_ : ∀ x {y z} → x ⟹ y → y IsRelatedTo z → x IsRelatedTo z
x ⟹*⟪ x⟹y ⟫ yz  =  x ⟹*⟨ ⟨ x⟹y ⟩ ⟩ yz

example₀ : not · true ⟹* false
example₀ =
  begin
    not · true
  ⟹*⟪ β⇒ value-true ⟫
    if true then false else true
  ⟹*⟪ β𝔹₁ ⟫
    false
  ∎

example₁ : I² · I · (not · false) ⟹* true
example₁ =
  begin
    I² · I · (not · false)
  ⟹*⟪ γ⇒₁ (β⇒ value-λ) ⟫
    (λ[ x ∶ 𝔹 ] I · var x) · (not · false)                  
  ⟹*⟪ γ⇒₂ value-λ (β⇒ value-false) ⟫
    (λ[ x ∶ 𝔹 ] I · var x) · (if false then false else true)
  ⟹*⟪ γ⇒₂ value-λ β𝔹₂ ⟫
    (λ[ x ∶ 𝔹 ] I · var x) · true
  ⟹*⟪ β⇒ value-true ⟫
    I · true
  ⟹*⟪ β⇒ value-true ⟫
    true
  ∎  
