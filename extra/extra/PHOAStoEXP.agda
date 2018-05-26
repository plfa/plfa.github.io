open import Algebra
open import Data.Product
open import Data.Bool
open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable

module LM {A : Set} = Monoid (Data.List.Properties.++-monoid A)

infixr 4 _⇒_

data Type : Set where
  o : Type
  _⇒_ : Type → Type → Type

Env = List Type

Type≡? : (A B : Type) → Dec (A ≡ B)
Type≡? o o = yes refl
Type≡? o (B ⇒ B₁) = no (λ ())
Type≡? (A ⇒ A₁) o = no (λ ())
Type≡? (A ⇒ B) (A' ⇒ B') with Type≡? A A'
Type≡? (A ⇒ B) (.A ⇒ B') | yes refl with Type≡? B B'
Type≡? (A ⇒ B) (.A ⇒ .B) | yes refl | yes refl = yes refl
Type≡? (A ⇒ B) (.A ⇒ B') | yes refl | no ¬p = no (λ {refl → ¬p refl})
Type≡? (A ⇒ B) (A' ⇒ B') | no ¬p = no (λ {refl → ¬p refl})

Env≡? : (Γ Δ : Env) → Dec (Γ ≡ Δ)
Env≡? [] [] = yes refl
Env≡? [] (x ∷ Δ) = no (λ ())
Env≡? (x ∷ Γ) [] = no (λ ())
Env≡? (A ∷ Γ) (A' ∷ Δ) with Type≡? A A'
Env≡? (A ∷ Γ) (A' ∷ Δ) | yes p with Env≡? Γ Δ
Env≡? (A ∷ Γ) (.A ∷ .Γ) | yes refl | yes refl = yes refl
Env≡? (A ∷ Γ) (A' ∷ Δ) | yes p | no ¬q = no (λ {refl → ¬q refl})
Env≡? (A ∷ Γ) (A' ∷ Δ) | no ¬p = no (λ {refl → ¬p refl})

data Var : Env → Type → Set where
  Z : ∀ {Γ : Env} {A : Type} → Var (A ∷ Γ) A
  S : ∀ {Γ : Env} {A B : Type} → Var Γ B → Var (A ∷ Γ) B

data Exp : Env → Type → Set where
  var : ∀ {Γ : Env} {A : Type} → Var Γ A → Exp Γ A
  abs : ∀ {Γ : Env} {A B : Type} → Exp (A ∷ Γ) B → Exp Γ (A ⇒ B)
  app : ∀ {Γ : Env} {A B : Type} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B

data PH (X : Type → Set) : Type → Set where
  var : ∀ {A : Type} → X A → PH X A
  abs : ∀ {A B : Type} → (X A → PH X B) → PH X (A ⇒ B)
  app : ∀ {A B : Type} → PH X (A ⇒ B) → PH X A → PH X B

-- logical prediacte on PH
PHᴾ : ∀ {X}(Xᴾ : ∀ {A} → X A → Set) → ∀ {A} → PH X A → Set
PHᴾ Xᴾ (var a)   = Xᴾ a
PHᴾ Xᴾ (abs t)   = ∀ a → Xᴾ a → PHᴾ Xᴾ (t a)
PHᴾ Xᴾ (app t u) = PHᴾ Xᴾ t × PHᴾ Xᴾ u

postulate
  free-thm :
    ∀ {A}(t : ∀ {X} → PH X A) → ∀ X (Xᴾ : ∀ {A} → X A → Set) → PHᴾ {X} Xᴾ t

PH' : Type → Set
PH' = PH (λ _ → Env)

VarOK? : ∀ Γ A Δ → Dec (∃ λ Ξ → (Ξ ++ A ∷ Δ) ≡ Γ)
VarOK? []       A Δ = no (λ {([] , ()) ; (_ ∷ _ , ())})
VarOK? (A' ∷ Γ) A Δ with Env≡? (A' ∷ Γ) (A ∷ Δ)
VarOK? (A' ∷ Γ) .A' .Γ | yes refl = yes ([] , refl)
VarOK? (A' ∷ Γ) A Δ | no ¬p with VarOK? Γ A Δ
VarOK? (A' ∷ Γ) A Δ | no ¬p | yes (Σ , refl) =
  yes (A' ∷ Σ , refl)
VarOK? (A' ∷ Γ) A Δ | no ¬p | no ¬q
  = no λ { ([] , refl) → ¬p refl ; (x ∷ Σ , s) → ¬q (Σ , proj₂ (∷-injective s))}

OK : ∀ {A} → Env → PH' A → Set
OK {A} Γ t = ∀ Δ → PHᴾ (λ {B} Σ → True (VarOK? (Δ ++ Γ) B Σ)) t

toVar : ∀ {Γ Σ A} → (∃ λ Ξ → (Ξ ++ A ∷ Σ) ≡ Γ) → Var Γ A
toVar ([]    , refl) = Z
toVar (x ∷ Ξ , refl) = S (toVar (Ξ , refl))

toExp' : ∀ {Γ A} (t : PH' A) → OK {A} Γ t → Exp Γ A
toExp' (var x) p = var (toVar (toWitness (p [])))
toExp' {Γ} (abs {A} {B} t) p =
  abs (toExp' (t Γ)
      λ Δ → subst (λ z → PHᴾ (λ {B₁} Σ₁ → True (VarOK? z B₁ Σ₁)) (t Γ))
                   (LM.assoc Δ (A ∷ []) Γ)
                   (p (Δ ++ A ∷ []) Γ (fromWitness (Δ , sym (LM.assoc Δ (A ∷ []) Γ)))))
toExp' (app t u) p =
  app (toExp' t (proj₁ ∘ p)) (toExp' u (proj₂ ∘ p))

toExp : ∀ {A} → (∀ {X} → PH X A) → Exp [] A
toExp {A} t = toExp' t λ Δ → free-thm t _ _

-- examples
------------------------------------------------------------

t0 : ∀ {X} → PH X ((o ⇒ o) ⇒ o ⇒ o)
t0 = abs var

t1 : ∀ {X} → PH X ((o ⇒ o) ⇒ o ⇒ o)
t1 = abs λ f → abs λ x → app (var f) (app (var f) (var x))

test1 : toExp t0 ≡ abs (var Z)
test1 = refl

test2 : toExp t1 ≡ abs (abs (app (var (S Z)) (app (var (S Z)) (var Z))))
test2 = refl
