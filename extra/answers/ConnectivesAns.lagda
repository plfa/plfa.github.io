---
title     : "Connectives Answers"
layout    : page
permalink : /ConnectivesAns
---

\begin{code}
module ConnectivesAns where
\end{code}

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Equivalence using (_⇔_)
\end{code}

#### Exercise `⊎-comm`

For commutativity, the `to` function swaps the two constructors,
taking `inj₁ x` to `inj₂ x`, and `inj₂ y` to `inj₁ y`; and the `from`
function does the same (up to renaming). Replacing the definition of
`from∘to` by `λ w → refl` will not work; and similarly for `to∘from`.
\begin{code}
⊎-comm : ∀ {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
⊎-comm = record
  { to       =  λ{ (inj₁ x) → (inj₂ x)
                 ; (inj₂ y) → (inj₁ y)
                 }
  ; from     =  λ{ (inj₁ y) → (inj₂ y)
                 ; (inj₂ x) → (inj₁ x)
                 }
  ; from∘to  =  λ{ (inj₁ x) → refl
                 ; (inj₂ y) → refl
                 }
  ; to∘from  =  λ{ (inj₁ y) → refl
                 ; (inj₂ x) → refl
                 }
  }
\end{code}
Being _commutative_ is different from being _commutative up to
isomorphism_.  Compare the two statements:

    m + n ≡ n + m
    A ⊎ B ≃ B ⊎ A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m + n` and `n + m` are equal to `5`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool ⊎ Tri` is
*not* the same as `Tri ⊎ Bool`.  But there is an isomorphism between
the two types.  For instance, `inj₁ true`, which is a member of the
former, corresponds to `inj₂ true`, which is a member of the latter.

#### Exercise `⊎-assoc`

For associativity, the `to` function reassociates, and the `from` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplification.
\begin{code}
⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record
  { to       =  λ{ (inj₁ (inj₁ x)) → (inj₁ x)
                 ; (inj₁ (inj₂ y)) → (inj₂ (inj₁ y))
                 ; (inj₂ z)        → (inj₂ (inj₂ z))
                 }
  ; from     =  λ{ (inj₁ x)        → (inj₁ (inj₁ x))
                 ; (inj₂ (inj₁ y)) → (inj₁ (inj₂ y))
                 ; (inj₂ (inj₂ z)) → (inj₂ z)
                 }
  ; from∘to  =  λ{ (inj₁ (inj₁ x)) → refl
                 ; (inj₁ (inj₂ y)) → refl
                 ; (inj₂ z)        → refl
                 }
  ; to∘from  =  λ{ (inj₁ x)        → refl
                 ; (inj₂ (inj₁ y)) → refl
                 ; (inj₂ (inj₂ z)) → refl
                 }
  }
\end{code}

Again, being _associative_ is not the same as being _associative
up to isomorphism_.  For example, the type `(ℕ + Bool) + Tri`
is _not_ the same as `ℕ + (Bool + Tri)`. But there is an
isomorphism between the two types. For instance `inj₂ (inj₁ true)`,
which is a member of the former, corresponds to `inj₁ (inj₂ true)`,
which is a member of the latter.

#### Exercise `⊥-identityˡ`

For left identity, the
`to` function observes that `inj₁ ()` can never arise, and takes `inj₂
x` to `x`, and the `from` function does the inverse.  The evidence of
left inverse requires matching against a suitable pattern to enable
simplification.
\begin{code}
⊥-identityˡ : ∀ {A : Set} → (⊥ ⊎ A) ≃ A
⊥-identityˡ =
  record
    { to       =  λ{ (inj₁ ())
                   ; (inj₂ x) → x
                   }
    ; from     =  λ{ x → inj₂ x }
    ; from∘to  =  λ{ (inj₁ ())
                   ; (inj₂ x) → refl
                   }
    ; to∘from  =  λ{ x → refl }
    }
\end{code}

Having an _identity_ is different from having an identity
_up to isomorphism_.  Compare the two statements:

    0 + m ≡ m
    ⊥ ⊎ A ≃ A

In the first case, we might have that `m` is `2`, and both `0 + m` and
`m` are equal to `2`.  In the second case, we might have that `A` is
`Bool`, and `⊥ ⊎ Bool` is _not_ the same as `Bool`.  But there is an
isomorphism between the two types.  For instance, `inj₂ true`, which is
a member of the former, corresponds to `true`, which is a member of
the latter.

#### Exercise `⊥-identityʳ`

Right identity follows from commutativity of sum and left identity.
\begin{code}
⊥-identityʳ : ∀ {A : Set} → (A ⊎ ⊥) ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎
\end{code}

#### Exercise `⊎-weak-×`

\begin{code}
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , z ⟩  =  inj₁ x
⊎-weak-× ⟨ inj₂ y , z ⟩  =  inj₂ ⟨ y , z ⟩
\end{code}

The corresponding full laws is:

    (A ⊎ B) × C ⇔ (A × C) ⊎ (B × C)

The weak version replaces `A × C` by `A`, and the equivalence by a
left-to-right implication.

#### Exercise `⊎×-implies-×⊎`

\begin{code}
⊎×⊎-implies-×⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
⊎×⊎-implies-×⊎× u v = ?
\end{code}
Does the converse hold? If so, prove; if not, give a counterexample.
