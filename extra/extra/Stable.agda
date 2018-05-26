import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; foldr; map)
open import Function using (_∘_)

double-negation : ∀ {A : Set} → A → ¬ ¬ A
double-negation x ¬x = ¬x x

triple-negation : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
triple-negation ¬¬¬x x = ¬¬¬x (double-negation x)

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable = triple-negation

×-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-stable ¬¬x→x ¬¬y→y ¬¬xy =
  ⟨ ¬¬x→x (contraposition (contraposition proj₁) ¬¬xy)
  , ¬¬y→y (contraposition (contraposition proj₂) ¬¬xy)
  ⟩

∀-stable : ∀ {A : Set} {B : A → Set} → (∀ (x : A) → Stable (B x)) → Stable (∀ (x : A) → B x)
∀-stable ∀x→¬¬y→y ¬¬∀x→y x =
  ∀x→¬¬y→y x (contraposition (contraposition λ{∀x→y → ∀x→y x}) ¬¬∀x→y)

-- Gödel-Gentzen translation

{--
data Var : ℕ → Set where
  zero : ∀ (n : ℕ) → Var (suc n)
  suc : ∀ (n : ℕ) → Var n → Var (suc n)

data Formula : ℕ → Set where
  _`≡_ : ∀ (n : ℕ) → Var n → Var n → Formula n
  _`×_ : ∀ (n : ℕ) → Formula n → Formula n → Formula n
  _`⊎_ : ∀ (n : ℕ) → Formula n → Formula n → Formula n
  `¬_ : ∀ (n : ℕ) → Formula n → Formula n
--}

data Formula : Set₁ where
  atomic : ∀ (A : Set) → Formula
  _`×_ : Formula → Formula → Formula
  _`⊎_ : Formula → Formula → Formula
  `¬_ : Formula → Formula

interp : Formula → Set
interp (atomic A) =  A
interp (`A `× `B) = interp `A × interp `B
interp (`A `⊎ `B) = interp `A ⊎ interp `B
interp (`¬ `A) = ¬ interp `A

g : Formula → Formula
g (atomic A) =  `¬ `¬ (atomic A)
g (`A `× `B) = g `A `× g `B
g (`A `⊎ `B) = `¬ ((`¬ g `A) `× (`¬ g `B))
g (`¬ `A) = `¬ g `A

stable-g : ∀ (`A : Formula) → Stable (interp (g `A))
stable-g (atomic A) =  ¬-stable 
stable-g (`A `× `B) =  ×-stable (stable-g `A) (stable-g `B)
stable-g (`A `⊎ `B) =  ¬-stable
stable-g (`¬ `A) = ¬-stable


