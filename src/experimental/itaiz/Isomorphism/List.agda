module experimental.itaiz.Isomorphism.List where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; +-comm; suc-injective; +-identityʳ; +-suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst; cong-app)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

open import experimental.itaiz.Isomorphism

infixr 5 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

pattern [_] x = x ∷ []

data _∈_ {A : Set} : A → List A → Set where
  zero : {x : A} → {l : List A} → x ∈ (x ∷ l)
  suc : {x y : A} → {l : List A} → x ∈ l → x ∈ (y ∷ l)

variable
  A : Set

_++_ : List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

∈-++ˡ : {x : A} {xs ys : List A} → x ∈ xs → x ∈ (xs ++ ys)
∈-++ˡ zero = zero
∈-++ˡ (suc x∈xs) = suc (∈-++ˡ x∈xs)

∈-++ʳ : {x : A} {xs ys : List A} → x ∈ ys → x ∈ (xs ++ ys)
∈-++ʳ {xs = []} x∈ys = x∈ys
∈-++ʳ {xs = x ∷ xs} x∈ys = suc (∈-++ʳ x∈ys)

∈-++-⊎ : {x : A} {xs ys : List A} → x ∈ (xs ++ ys) → x ∈ xs ⊎ x ∈ ys
∈-++-⊎ {xs = []} x∈ = inj₂ x∈
∈-++-⊎ {xs = x ∷ xs} zero = inj₁ zero
∈-++-⊎ {xs = x ∷ xs} (suc x∈) with ∈-++-⊎ x∈
... | inj₁ x∈xs = inj₁ (suc x∈xs)
... | inj₂ x∈ys = inj₂ x∈ys

length : List A → ℕ
length [] = zero
length (_ ∷ l) = suc (length l)

reverse : List A → List A
reverse [] = []
reverse (x ∷ l) = reverse l ++ [ x ]

postulate extensionality : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

LA-expand : List A ≃ ∃[ n ] Σ[ xs ∈ List A ] length xs ≡ n
LA-expand = record
  { to = λ xs → length xs , xs , refl
  ; from = λ { (_ , xs , refl) → xs }
  ; from∘to = λ xs → refl
  ; to∘from = λ { (_ , xs , refl) → refl }
  }

∀n-LA≃Fn→A : (n : ℕ) → Σ[ xs ∈ List A ] length xs ≡ n ≃ (Fin n → A)
∀n-LA≃Fn→A n = record { to = to n ; from = from n ; from∘to = from∘to n ; to∘from = to∘from n }
  where
    to : (n : ℕ) → Σ[ xs ∈ List A ] length xs ≡ n → (Fin n → A)
    to zero _ ()
    to (suc n) (x ∷ xs , slxs≡sn) zero = x
    to (suc n) (x ∷ xs , slxs≡sn) (suc i) = to n (xs , suc-injective slxs≡sn) i
    from : (n : ℕ) → (Fin n → A) → Σ[ xs ∈ List A ] length xs ≡ n
    from zero _ = [] , refl
    from (suc n) f with from n (f ∘ suc)
    ... | xs , lxs≡n = (f zero ∷ xs) , (cong suc lxs≡n)
    from∘to : (n : ℕ) → (ex : Σ[ xs ∈ List A ] length xs ≡ n) → from n (to n ex) ≡ ex
    from∘to zero ([] , refl) = refl
    from∘to (suc n) (x ∷ xs , refl) rewrite from∘to n (xs , refl) = refl
    to∘from' : (n : ℕ) → (f : Fin n → A) → (i : Fin n) → to n (from n f) i ≡ f i
    to∘from' (suc n) f zero = refl
    to∘from' (suc n) f (suc i) with from n (f ∘ suc) in eq
    ... | xs , refl rewrite sym eq = to∘from' n (f ∘ suc) i
    to∘from : (n : ℕ) → (f : Fin n → A) → to n (from n f) ≡ f
    to∘from n f = extensionality (to∘from' n f)

LA≃Fn→A : List A ≃ ∃[ n ] (Fin n → A)
LA≃Fn→A = ≃-trans LA-expand (∀≃→≃Σ ∀n-LA≃Fn→A)

∃x∈l≃Fl : (l : List A) → ∃[ x ] x ∈ l ≃ Fin (length l)
∃x∈l≃Fl l = record { to = to l ; from = from l ; from∘to = from∘to l ; to∘from = to∘from l }
  where
    to : (l : List A) → ∃[ x ] x ∈ l → Fin (length l)
    to l (x , zero) = zero
    to (_ ∷ l) (x , suc x∈l) = suc (to l (x , x∈l))
    from : (l : List A) → Fin (length l) → ∃[ x ] x ∈ l
    from (x ∷ l) zero = x , zero
    from (x ∷ l) (suc i) with from l i
    ... | y , y∈l = y , suc y∈l
    from∘to : (l : List A) → (ex : ∃[ x ] x ∈ l) → from l (to l ex) ≡ ex
    from∘to (.x ∷ _) (x , zero) = refl
    from∘to (_ ∷ l) (x , suc x∈l) rewrite from∘to l (x , x∈l) = refl
    to∘from : (l : List A) → (i : Fin (length l)) → to l (from l i) ≡ i
    to∘from (x ∷ l) zero = refl
    to∘from (x ∷ l) (suc i) rewrite to∘from l i = refl
