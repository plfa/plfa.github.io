---
title     : "Typed: Typed Lambda term representation"
layout    : page
permalink : /Typed
---

## Imports

\begin{code}
module Typed where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≟_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
-- open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map; From-no; from-no)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)
\end{code}


## Syntax

\begin{code}
infixr 6 _⇒_
infixl 5 _,_∈_
infix  4 _⊧_∈_
infix  4 _⊢_∈_
infix  5 ƛ_∈_⇒_
infixl 6 _·_

data Id : Set where
  id : ℕ → Id

data Type : Set where
  o   : Type
  _⇒_ : Type → Type → Type

data Env : Set where
  ε     : Env
  _,_∈_ : Env → Id → Type → Env

data Term : Set where
  ⌊_⌋      : Id → Term
  ƛ_∈_⇒_  : Id → Type → Term → Term
  _·_     : Term → Term → Term  

data _⊧_∈_ : Env → Id → Type → Set where

  Z : ∀ {Γ A x} →
    -----------------
    Γ , x ∈ A ⊧ x ∈ A

  S : ∀ {Γ A B x y} →
    x ≢ y →
    Γ ⊧ x ∈ A →
    -----------------
    Γ , y ∈ B ⊧ x ∈ A

data _⊢_∈_ : Env → Term → Type → Set where

  Ax : ∀ {Γ A x} →
    Γ ⊧ x ∈ A →
    ---------------------
    Γ ⊢ ⌊ x ⌋ ∈ A

  ⇒-I  :  ∀ {Γ A B x N} →
    Γ , x ∈ A ⊢ N ∈ B →
    --------------------------
    Γ ⊢ (ƛ x ∈ A ⇒ N) ∈ A ⇒ B

  ⇒-E : ∀ {Γ A B L M} →
    Γ ⊢ L ∈ A ⇒ B →
    Γ ⊢ M ∈ A →
    --------------
    Γ ⊢ L · M ∈ B
\end{code}

## Decide whether environments and types are equal

\begin{code}
_≟I_ : ∀ (x y : Id) → Dec (x ≡ y)
(id s) ≟I (id t) with s ≟ t
...                 | yes refl = yes refl
...                 | no s≢t = no (f s≢t)
  where
  f : ∀ {s t : ℕ} → s ≢ t → id s ≢ id t
  f s≢t refl = s≢t refl

_≟T_ : ∀ (A B : Type) → Dec (A ≡ B)
o ≟T o = yes refl
o ≟T (A′ ⇒ B′) = no (λ())
(A ⇒ B) ≟T o = no (λ())
(A ⇒ B) ≟T (A′ ⇒ B′) = map (equivalence obv1 obv2) ((A ≟T A′) ×-dec (B ≟T B′))
  where
  obv1 : ∀ {A B A′ B′ : Type} → (A ≡ A′) × (B ≡ B′) → A ⇒ B ≡ A′ ⇒ B′
  obv1 ⟨ refl , refl ⟩ = refl
  obv2 : ∀ {A B A′ B′ : Type} → A ⇒ B ≡ A′ ⇒ B′ → (A ≡ A′) × (B ≡ B′)
  obv2 refl = ⟨ refl , refl ⟩

_≟E_ : ∀ (Γ Δ : Env) → Dec (Γ ≡ Δ)
ε ≟E ε = yes refl
ε ≟E (Γ , x ∈ A) = no (λ())
(Γ , x ∈ A) ≟E ε = no (λ())
(Γ , x ∈ A) ≟E (Δ , y ∈ B) = map (equivalence obv1 obv2) ((Γ ≟E Δ) ×-dec ((x ≟I y) ×-dec (A ≟T B)))
  where
  obv1 : ∀ {Γ Δ A B x y} → (Γ ≡ Δ) × ((x ≡ y) × (A ≡ B)) → (Γ , x ∈ A) ≡ (Δ , y ∈ B)
  obv1 ⟨ refl , ⟨ refl , refl ⟩ ⟩ = refl
  obv2 : ∀ {Γ Δ A B} → (Γ , x ∈ A) ≡ (Δ , y ∈ B) → (Γ ≡ Δ) × ((x ≡ y) × (A ≡ B))
  obv2 refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩
\end{code}


## Test examples

\begin{code}
m n s z : Id
m = id 0
n = id 1
s = id 2
z = id 3

Ch : Type
Ch = (o ⇒ o) ⇒ o ⇒ o

two : Term
two = ƛ s ∈ (o ⇒ o) ⇒ ƛ z ∈ o ⇒ (⌊ s ⌋ · (⌊ s ⌋ · ⌊ z ⌋))

two⊢ : ε ⊢ two ∈ Ch
two⊢ = ⇒-I (⇒-I (⇒-E (Ax (S (λ()) Z)) (⇒-E (Ax (S (λ()) Z)) (Ax Z))))

four : Term
four = ƛ s ∈ (o ⇒ o) ⇒ ƛ z ∈ o ⇒ (⌊ s ⌋ · (⌊ s ⌋ · (⌊ s ⌋ · (⌊ s ⌋ · ⌊ z ⌋))))

four⊢ : ε ⊢ four ∈ Ch
four⊢ = ⇒-I (⇒-I (⇒-E (Ax (S (λ()) Z)) (⇒-E (Ax (S (λ()) Z))
          (⇒-E (Ax (S (λ()) Z)) (⇒-E (Ax (S (λ ()) Z)) (Ax Z))))))

plus : Term
plus = ƛ m ∈ Ch ⇒ ƛ n ∈ Ch ⇒ ƛ s ∈ (o ⇒ o) ⇒ ƛ z ∈ o ⇒ ⌊ m ⌋ · ⌊ s ⌋ · (⌊ n ⌋ · ⌊ s ⌋ · ⌊ z ⌋)

plus⊢ : ε ⊢ plus ∈ Ch ⇒ Ch ⇒ Ch
plus⊢ = ⇒-I (⇒-I (⇒-I (⇒-I
          (⇒-E (⇒-E (Ax (S (λ ()) (S (λ ()) (S (λ ()) Z)))) (Ax (S (λ ()) Z)))
            (⇒-E (⇒-E (Ax (S (λ ()) (S (λ ()) Z))) (Ax (S (λ ()) Z))) (Ax Z))))))

four′ : Term
four′ = plus · two · two

four′⊢ : ε ⊢ four′ ∈ Ch
four′⊢ = ⇒-E (⇒-E plus⊢ two⊢) two⊢
\end{code}

# Denotational semantics

\begin{code}
⟦_⟧ᵀ : Type → Set
⟦ o ⟧ᵀ      =  ℕ
⟦ A ⇒ B ⟧ᵀ  =  ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ

⟦_⟧ᴱ : Env → Set
⟦ ε ⟧ᴱ          =  ⊤
⟦ Γ , x ∈ A ⟧ᴱ  =  ⟦ Γ ⟧ᴱ × ⟦ A ⟧ᵀ

⟦_⟧ⱽ : ∀ {Γ x A} → Γ ⊧ x ∈ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ Z ⟧ⱽ     ⟨ ρ , v ⟩ = v
⟦ S _ n ⟧ⱽ ⟨ ρ , v ⟩ = ⟦ n ⟧ⱽ ρ

⟦_⟧ : ∀ {Γ M A} → Γ ⊢ M ∈ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ Ax n ⟧      ρ  =  ⟦ n ⟧ⱽ ρ
⟦ ⇒-I N⊢ ⟧    ρ  =  λ{ v → ⟦ N⊢ ⟧ ⟨ ρ , v ⟩ }
⟦ ⇒-E L⊢ M⊢ ⟧ ρ  =  (⟦ L⊢ ⟧ ρ) (⟦ M⊢ ⟧ ρ)

_ : ⟦ four⊢ ⟧ tt ≡ ⟦ four′⊢ ⟧ tt
_ = refl

_ : ⟦ four⊢ ⟧ tt suc zero ≡ 4
_ = refl
\end{code}

## Operational semantics - with simultaneous substitution, a la McBride

## Renaming

\begin{code}
ext⊧ : ∀ {Γ Δ x A} → (∀ {y B} → Γ ⊧ y ∈ B → Δ ⊧ y ∈ B) → Δ ⊧ x ∈ A → (∀ {y B} → Γ , x ∈ A ⊧ y ∈ B → Δ ⊧ y ∈ B)
ext⊧ ρ j Z        =  j
ext⊧ ρ j (S _ k)  =  ρ k

rename⊢ : ∀ {Γ Δ} → (∀ {y B} → Γ ⊧ y ∈ B → Δ ⊧ y ∈ B) → (∀ {M A} → Γ ⊢ M ∈ A → Δ ⊢ M ∈ A)
rename⊢ ρ (Ax n)       =  Ax (ρ n)
rename⊢ ρ (⇒-I N⊢)     =  ⇒-I (rename⊢ (ext⊧ (S ? ∘ ρ) Z) N⊢)
rename⊢ ρ (⇒-E L⊢ M⊢)  =  ⇒-E (rename⊢ ρ L⊢) (rename⊢ ρ M⊢)
\end{code}

