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
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _⊔_; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; 1+n≰n)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
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
infixl 5 _,_⦂_
infix  4 _∋_⦂_
infix  4 _⊢_⦂_
infix  5 ƛ_⦂_⇒_
infix  5 ƛ_
infixl 6 _·_

Id : Set
Id = ℕ

data Type : Set where
  o   : Type
  _⇒_ : Type → Type → Type

data Env : Set where
  ε     : Env
  _,_⦂_ : Env → Id → Type → Env

data Term : Set where
  ⌊_⌋      : Id → Term
  ƛ_⦂_⇒_  : Id → Type → Term → Term
  _·_     : Term → Term → Term  

data _∋_⦂_ : Env → Id → Type → Set where

  Z : ∀ {Γ A x} →
    -----------------
    Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ A B x y} →
    x ≢ y →
    Γ ∋ y ⦂ B →
    -----------------
    Γ , x ⦂ A ∋ y ⦂ B

data _⊢_⦂_ : Env → Term → Type → Set where

  ⌊_⌋ : ∀ {Γ A x} →
    Γ ∋ x ⦂ A →
    ---------------------
    Γ ⊢ ⌊ x ⌋ ⦂ A

  ƛ_ :  ∀ {Γ x A N B} →
    Γ , x ⦂ A ⊢ N ⦂ B →
    --------------------------
    Γ ⊢ (ƛ x ⦂ A ⇒ N) ⦂ A ⇒ B

  _·_ : ∀ {Γ L M A B} →
    Γ ⊢ L ⦂ A ⇒ B →
    Γ ⊢ M ⦂ A →
    --------------
    Γ ⊢ L · M ⦂ B
\end{code}

## Decide whether environments and types are equal

\begin{code}
_≟I_ : ∀ (x y : Id) → Dec (x ≡ y)
_≟I_ = _≟_

{-
_≟I_ : ∀ (x y : Id) → Dec (x ≡ y)
(id m) ≟I (id n) with m ≟ n
...                 | yes refl  =  yes refl
...                 | no  m≢n   =  no (f m≢n)
  where
  f : ∀ {m n : ℕ} → m ≢ n → id m ≢ id n
  f m≢n refl = m≢n refl
-}

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
ε ≟E (Γ , x ⦂ A) = no (λ())
(Γ , x ⦂ A) ≟E ε = no (λ())
(Γ , x ⦂ A) ≟E (Δ , y ⦂ B) = map (equivalence obv1 obv2) ((Γ ≟E Δ) ×-dec ((x ≟I y) ×-dec (A ≟T B)))
  where
  obv1 : ∀ {Γ Δ A B x y} → (Γ ≡ Δ) × ((x ≡ y) × (A ≡ B)) → (Γ , x ⦂ A) ≡ (Δ , y ⦂ B)
  obv1 ⟨ refl , ⟨ refl , refl ⟩ ⟩ = refl
  obv2 : ∀ {Γ Δ A B} → (Γ , x ⦂ A) ≡ (Δ , y ⦂ B) → (Γ ≡ Δ) × ((x ≡ y) × (A ≡ B))
  obv2 refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩
\end{code}


## Test examples

\begin{code}
m n s z : Id
m = 0
n = 1
s = 2
z = 3

Ch : Type
Ch = (o ⇒ o) ⇒ o ⇒ o

two : Term
two = ƛ s ⦂ (o ⇒ o) ⇒ ƛ z ⦂ o ⇒ (⌊ s ⌋ · (⌊ s ⌋ · ⌊ z ⌋))

⊢two : ε ⊢ two ⦂ Ch
⊢two = ƛ ƛ (⌊ S (λ()) Z ⌋ · (⌊ S (λ()) Z ⌋ · ⌊ Z ⌋))

four : Term
four = ƛ s ⦂ (o ⇒ o) ⇒ ƛ z ⦂ o ⇒ (⌊ s ⌋ · (⌊ s ⌋ · (⌊ s ⌋ · (⌊ s ⌋ · ⌊ z ⌋))))

⊢four : ε ⊢ four ⦂ Ch
⊢four = ƛ ƛ (⌊ S (λ()) Z ⌋ · (⌊ S (λ()) Z ⌋ ·
              (⌊ S (λ()) Z ⌋ · (⌊ S (λ()) Z ⌋ · ⌊ Z ⌋))))

plus : Term
plus = ƛ m ⦂ Ch ⇒ ƛ n ⦂ Ch ⇒ ƛ s ⦂ (o ⇒ o) ⇒ ƛ z ⦂ o ⇒
         ⌊ m ⌋ · ⌊ s ⌋ · (⌊ n ⌋ · ⌊ s ⌋ · ⌊ z ⌋)

⊢plus : ε ⊢ plus ⦂ Ch ⇒ Ch ⇒ Ch
⊢plus = ƛ (ƛ (ƛ (ƛ ((⌊ (S (λ ()) (S (λ ()) (S (λ ()) Z))) ⌋ · ⌊ S (λ ()) Z ⌋) ·
          (⌊ S (λ ()) (S (λ ()) Z) ⌋ · ⌊ S (λ ()) Z ⌋ · ⌊ Z ⌋)))))

four′ : Term
four′ = plus · two · two

⊢four′ : ε ⊢ four′ ⦂ Ch
⊢four′ = ⊢plus · ⊢two · ⊢two
\end{code}

# Denotational semantics

\begin{code}
⟦_⟧ᵀ : Type → Set
⟦ o ⟧ᵀ      =  ℕ
⟦ A ⇒ B ⟧ᵀ  =  ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ

⟦_⟧ᴱ : Env → Set
⟦ ε ⟧ᴱ          =  ⊤
⟦ Γ , x ⦂ A ⟧ᴱ  =  ⟦ Γ ⟧ᴱ × ⟦ A ⟧ᵀ

⟦_⟧ⱽ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ Z ⟧ⱽ     ⟨ ρ , v ⟩ = v
⟦ S _ x ⟧ⱽ ⟨ ρ , v ⟩ = ⟦ x ⟧ⱽ ρ

⟦_⟧ : ∀ {Γ M A} → Γ ⊢ M ⦂ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ ⌊ x ⌋ ⟧   ρ  =  ⟦ x ⟧ⱽ ρ
⟦ ƛ ⊢N ⟧    ρ  =  λ{ v → ⟦ ⊢N ⟧ ⟨ ρ , v ⟩ }
⟦ ⊢L · ⊢M ⟧ ρ  =  (⟦ ⊢L ⟧ ρ) (⟦ ⊢M ⟧ ρ)

_ : ⟦ ⊢four′ ⟧ tt ≡ ⟦ ⊢four ⟧ tt
_ = refl

_ : ⟦ ⊢four ⟧ tt suc zero ≡ 4
_ = refl
\end{code}

## Operational semantics - with simultaneous substitution, a la McBride

## Biggest identifier

\begin{code}
lemma : ∀ {y z} → y ≤ z → y ≢ 1 + z
lemma {y} {z} y≤z y≡1+z = 1+n≰n (≤-trans 1+z≤y y≤z)
  where
  1+z≤y : 1 + z ≤ y
  1+z≤y rewrite y≡1+z = ≤-refl

emp≤ : ∀ {y B z} → ε ∋ y ⦂ B → y ≤ z
emp≤ ()

ext≤ : ∀ {Γ x z A} → (∀ {y B} → Γ ∋ y ⦂ B → y ≤ z) → x ≤ z → (∀ {y B} → Γ , x ⦂ A ∋ y ⦂ B → y ≤ z)
ext≤ ρ x≤z Z        =  x≤z
ext≤ ρ x≤z (S _ k)  =  ρ k

fresh : ∀ (Γ : Env) → ∃[ z ] (∀ {y B} → Γ ∋ y ⦂ B → y ≤ z)
fresh ε                           = ⟨ 0 , emp≤ ⟩
fresh (Γ , x ⦂ A) with fresh Γ
...                  | ⟨ z , ρ ⟩  = ⟨ w , ext≤ ((λ y≤z → ≤-trans y≤z z≤w) ∘ ρ) x≤w ⟩
  where
  w   = x ⊔ z
  z≤w = n≤m⊔n x z
  x≤w = m≤m⊔n x z
\end{code}

## Erasure

\begin{code}
lookup : ∀ {Γ x A} → Γ ∋ x ⦂ A → Id
lookup {Γ , x ⦂ A} Z        =  x
lookup {Γ , x ⦂ A} (S _ k)  =  lookup {Γ} k

erase : ∀ {Γ M A} → Γ ⊢ M ⦂ A → Term
erase ⌊ k ⌋                     =  ⌊ lookup k ⌋
erase (ƛ_ {x = x} {A = A} ⊢N)   =  ƛ x ⦂ A ⇒ erase ⊢N
erase (⊢L · ⊢M)                 =  erase ⊢L · erase ⊢M

lookup-lemma : ∀ {Γ x A} → (k : Γ ∋ x ⦂ A) → lookup k ≡ x
lookup-lemma Z        =  refl
lookup-lemma (S _ k)  =  lookup-lemma k

erase-lemma : ∀ {Γ M A} → (⊢M : Γ ⊢ M ⦂ A) → erase ⊢M ≡ M
erase-lemma ⌊ k ⌋                    =  cong ⌊_⌋ (lookup-lemma k)
erase-lemma (ƛ_ {x = x} {A = A} ⊢N)  =  cong (ƛ x ⦂ A ⇒_) (erase-lemma ⊢N)
erase-lemma (⊢L · ⊢M)                =  cong₂ _·_ (erase-lemma ⊢L) (erase-lemma ⊢M)
\end{code}

## Renaming

\begin{code}
rename : ∀ {Γ} → (∀ {y B} → Γ ∋ y ⦂ B → Id) → (∀ {M A} → Γ ⊢ M ⦂ A → Term)
rename ρ (⌊ k ⌋)                       =  ⌊ ρ k ⌋
rename ρ (⊢L · ⊢M)                     =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename {Γ} ρ (ƛ_ {x = x} {A = A} ⊢N)   =  ƛ x′ ⦂ A ⇒ (rename ρ′ ⊢N)
  where
  x′    : Id
  x′    = 1 + proj₁ (fresh Γ)
  ρ′ : ∀ {y B} → Γ , x ⦂ A ∋ y ⦂ B → Id
  ρ′ Z        =  x′
  ρ′ (S _ j)  =  ρ j

{-
⊢rename : ∀ {Γ Δ} → (ρ : ∀ {y B} → Γ ∋ y ⦂ B → ∃[ y′ ] (Δ ∋ y′ ⦂ B)) →
                       (∀ {M A} → (⊢M : Γ ⊢ M ⦂ A) → Δ ⊢ rename (proj₁ ∘ ρ) ⊢M ⦂ A)
⊢rename ρ (⌊ k ⌋)                       =  ⌊ proj₂ (ρ k) ⌋
⊢rename ρ (⊢L · ⊢M)                     =  (⊢rename ρ ⊢L) · (⊢rename ρ ⊢M)
⊢rename {Γ} ρ (ƛ_ {x = x} {A = A} ⊢N)
  with fresh Γ
  ... | ⟨ w , σ ⟩                       =  ƛ x′ ⦂ A ⇒ (rename ρ′ ⊢N)
  where
  x′    : Id
  x′    = 1 + w
  ρ′ : ∀ {y B} → Γ , x ⦂ A ∋ y ⦂ B → ∃[ y′ ] (Δ ∋ y′ ⦂ B)
  ρ′ Z        =  x′
  ρ′ (S _ j)  =  ρ j
-}


ext∋ : ∀ {Γ Δ x A} → (∀ {y B} → Γ ∋ y ⦂ B → Δ ∋ y ⦂ B) → Δ ∋ x ⦂ A → (∀ {y B} → Γ , x ⦂ A ∋ y ⦂ B → Δ ∋ y ⦂ B)
ext∋ ρ j Z        =  j
ext∋ ρ j (S _ k)  =  ρ k


{-
⊢rename : ∀ {Γ Δ} → (ρ : ∀ {y B} → Γ ∋ y ⦂ B → Δ ∋ y ⦂ B) → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ rename ρ M ⦂ A)
⊢rename ρ (⌊ x ⌋)    =  ⌊ ρ x ⌋
⊢rename ρ (ƛ ⊢N)     =  ƛ (⊢rename (ext∋ (S {!!} ∘ ρ) Z) ⊢N)
⊢rename ρ (⊢L · ⊢M)  =  (⊢rename ρ ⊢L) · (⊢rename ρ ⊢M)
-}
\end{code}

