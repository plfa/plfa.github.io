open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- open import Data.List.Any.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)

Id = ℕ

_⊆_ : List Id → List Id → Set
xs ⊆ ys = ∀ {w} → w ∈ xs → w ∈ ys

lemma : ∀ {x : Id} → x ∈ [ x ]
lemma = here refl
