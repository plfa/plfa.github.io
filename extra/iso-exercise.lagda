\begin{code}
module iso-exercise where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong₂)
open Eq.≡-Reasoning
open import plfa.Isomorphism using (_≃_)
open import Data.List using (List; []; _∷_)
open import Data.List.All using (All; []; _∷_)
open import Data.List.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Function using (_∘_)

postulate
  extensionality : ∀ {A : Set} {B : A → Set} {C : A → Set} {f g : {x : A} → B x → C x}
                → (∀ {x : A} (bx : B x) → f {x} bx ≡ g {x} bx)
                  --------------------------------------------
                → (λ {x} → f {x}) ≡ (λ {x} → g {x})

f : ∀ {A : Set} {P : A → Set} {xs : List A} → All P xs → (∀ {x} -> x ∈ xs -> P x)
f [] ()
f (px ∷ pxs) (here refl) = px
f (px ∷ pxs) (there x∈xs) = f pxs x∈xs

g : ∀ {A : Set} {P : A → Set} {xs : List A} → (∀ {x} -> x ∈ xs -> P x) → All P xs
g {xs = []} h = []
g {xs = x ∷ xs} h = h {x} (here refl) ∷ g (h ∘ there)

gf : ∀ {A : Set} {P : A → Set} {xs : List A} → ∀ (pxs : All P xs) → g (f pxs) ≡ pxs
gf [] = refl
gf (px ∷ pxs) = Eq.cong₂ _∷_ refl (gf pxs)

fg : ∀ {A : Set} {P : A → Set} {xs : List A}
      → ∀ (h : ∀ {x} -> x ∈ xs -> P x) → ∀ {x} (x∈ : x ∈ xs) → f (g h) {x} x∈ ≡ h {x} x∈
fg {xs = []} h ()
fg {xs = x ∷ xs} h (here refl) = refl
fg {xs = x ∷ xs} h (there x∈xs) = fg (h ∘ there) x∈xs

lemma : ∀ {A : Set} {P : A → Set} {xs : List A} → All P xs ≃ (∀ {x} -> x ∈ xs -> P x)
lemma =
  record
    { to = f
    ; from = g
    ; from∘to = gf
    ; to∘from = extensionality ∘ fg
    }

\end{code}
