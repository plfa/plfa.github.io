---
title     : "Reflection: Proof by Reflection"
layout    : page
prev      : /Decidable/
permalink : /Reflection/
next      : /Lists/
---

```
module plfa.Reflection where

open import plfa.Lambda hiding (ƛ′_⇒_; _≠_; Ch; ⊢twoᶜ)
open import Function using (flip; _$_; const)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.String using (_≟_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_)

T : Bool → Set
T true  = ⊤
T false = ⊥

⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

True : {P : Set} → Dec P → Set
True Q = T ⌊ Q ⌋

not : Bool → Bool
not false = true
not true  = false

False : {P : Set} → Dec P → Set
False Q = T (not ⌊ Q ⌋)

toWitnessFalse : {P : Set} {Q : Dec P} → False Q → ¬ P
toWitnessFalse {Q = yes _}  ()
toWitnessFalse {Q = no  ¬p} _  = ¬p

data is-` : Term → Set where
  `_ : (x : Id) → is-` (` x)

is-`? : (M : Term) → Dec (is-` M)
is-`? (` x)                        = yes (` x)
is-`? (ƛ x ⇒ N)                    = no (λ ())
is-`? (L · M)                      = no (λ ())
is-`? `zero                        = no (λ ())
is-`? (`suc M)                     = no (λ ())
is-`? case L [zero⇒ M |suc x ⇒ N ] = no (λ ())
is-`? (μ x ⇒ N)                    = no (λ ())

ƛ′_⇒_ : (x : Term) {{p : True (is-`? x)}} (N : Term) → Term
ƛ′ (` x) ⇒ N = ƛ x ⇒ N

S′ : ∀ {Γ x y A B}
   → {{p : False (x ≟ y)}}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A
S′ {{p}} Γ∋x⦂A = S (toWitnessFalse p) Γ∋x⦂A

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where
    ∋s = S′ Z
    ∋z = Z
```
