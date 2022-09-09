module experimental.iharbury.ListIsomorphism where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (∃-syntax; _,_; uncurry; proj₁; proj₂)
open import Data.Product.Properties using (Σ-≡,≡↔≡)
open import Function.Bundles using (_↔_; Inverse)
open import Level using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

module _ {ℓ} {A : Set ℓ} where

    to : List A → ∃[ n ] (Fin n → A)
    to xs = length xs , lookup xs

    from : ∀ n → (Fin n → A) → List A
    from zero _ = []
    from (suc n) f = f Fin.zero ∷ from n (λ i → f (Fin.suc i))

    from∘to : ∀ xs → (uncurry from) (to xs) ≡ xs
    from∘to [] = refl
    from∘to (x ∷ xs) rewrite from∘to xs = refl

    to∘from₁ : ∀ n f → length (from n f) ≡ n
    to∘from₁ zero _ = refl
    to∘from₁ (suc n) f rewrite to∘from₁ n (λ i → f (Fin.suc i)) = refl

    substZero : ∀ {n₁ n₂} (suc-n₁≡suc-n₂ : ℕ.suc n₁ ≡ ℕ.suc n₂)
        → subst Fin suc-n₁≡suc-n₂ (Fin.zero {n₁}) ≡ Fin.zero {n₂}
    substZero refl = refl

    substSuc : ∀ {n₁ n₂} (suc-n₁≡suc-n₂ : ℕ.suc n₁ ≡ ℕ.suc n₂) (i : Fin n₁)
        → subst Fin suc-n₁≡suc-n₂ (Fin.suc i) ≡
            Fin.suc (subst Fin (suc-injective suc-n₁≡suc-n₂) i)
    substSuc refl _ = refl

    to∘from₂ : ∀ n f (nEq : n ≡ length (from n f))
        (i₁ : Fin (length (from n f))) (i₂ : Fin n)
        → i₁ ≡ subst Fin nEq i₂
        → lookup (from n f) i₁ ≡ f i₂
    to∘from₂ (suc n) f nEq _ zero refl rewrite substZero nEq = refl
    to∘from₂ (suc n) f nEq _ (suc i) refl
        rewrite substSuc nEq i
              | to∘from₂ n (λ i₁ → f (Fin.suc i₁)) (suc-injective nEq) _ i refl
        = refl

    pair≡ : Extensionality Level.zero ℓ
        → ∀ n₁ n₂ (f₁ : Fin n₁ → A) (f₂ : Fin n₂ → A) (n₁≡n₂ : n₁ ≡ n₂)
        → (∀ i₁ i₂ → i₁ ≡ subst Fin (sym n₁≡n₂) i₂ → f₁ i₁ ≡ f₂ i₂)
        → (n₁ , f₁) ≡ (n₂ , f₂)
    pair≡ ext n _ f₁ f₂ refl eq = cong (n ,_) (ext (λ i → eq i i refl))

    to∘from : Extensionality Level.zero ℓ → ∀ n (f : Fin n → A)
        → to (from n f) ≡ (n , f)
    to∘from ext n f = pair≡ ext (length (from n f)) n (lookup (from n f)) f
        (to∘from₁ n f)
        (λ i₁ i₂ eq → to∘from₂ n f (sym (to∘from₁ n f)) i₁ i₂ eq)
    
    ListIso : Extensionality Level.zero ℓ → (List A) ↔ (∃[ n ] (Fin n → A))
    ListIso ext = record
        { f = to
        ; f⁻¹ = uncurry from
        ; cong₁ = cong to
        ; cong₂ = cong (uncurry from)
        ; inverse = uncurry (to∘from ext) , from∘to
        } 
