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
open import Data.List using (List; []; _∷_; [_]; _++_; foldr; filter)
open import Data.List.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _⊔_; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; 1+n≰n)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equality using (≡-setoid)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map; From-no; from-no)
open import Relation.Nullary.Negation using (contraposition; ¬?)
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

## Decide whether types and environments are equal

\begin{code}
_≟I_ : ∀ (x y : Id) → Dec (x ≡ y)
_≟I_ = _≟_

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

z≢s : z ≢ s
z≢s ()

z≢n : z ≢ n
z≢n ()

s≢n : s ≢ n
s≢n ()

z≢m : z ≢ m
z≢m ()

s≢m : s ≢ m
s≢m ()

n≢m : n ≢ m
n≢m ()

Ch : Type
Ch = (o ⇒ o) ⇒ o ⇒ o

two : Term
two = ƛ s ⦂ (o ⇒ o) ⇒ ƛ z ⦂ o ⇒ (⌊ s ⌋ · (⌊ s ⌋ · ⌊ z ⌋))

⊢two : ε ⊢ two ⦂ Ch
⊢two = ƛ ƛ ⌊ ⊢s ⌋ · (⌊ ⊢s ⌋ · ⌊ ⊢z ⌋)
  where
  ⊢s = S z≢s Z
  ⊢z = Z

four : Term
four = ƛ s ⦂ (o ⇒ o) ⇒ ƛ z ⦂ o ⇒ ⌊ s ⌋ · (⌊ s ⌋ · (⌊ s ⌋ · (⌊ s ⌋ · ⌊ z ⌋)))

⊢four : ε ⊢ four ⦂ Ch
⊢four = ƛ ƛ ⌊ ⊢s ⌋ · (⌊ ⊢s ⌋ · (⌊ ⊢s ⌋ · (⌊ ⊢s ⌋ · ⌊ ⊢z ⌋)))
  where
  ⊢s = S z≢s Z
  ⊢z = Z

plus : Term
plus = ƛ m ⦂ Ch ⇒ ƛ n ⦂ Ch ⇒ ƛ s ⦂ (o ⇒ o) ⇒ ƛ z ⦂ o ⇒
         ⌊ m ⌋ · ⌊ s ⌋ · (⌊ n ⌋ · ⌊ s ⌋ · ⌊ z ⌋)

⊢plus : ε ⊢ plus ⦂ Ch ⇒ Ch ⇒ Ch
⊢plus = ƛ ƛ ƛ ƛ  ⌊ ⊢m ⌋ ·  ⌊ ⊢s ⌋ · (⌊ ⊢n ⌋ · ⌊ ⊢s ⌋ · ⌊ ⊢z ⌋)
  where
  ⊢z = Z
  ⊢s = S z≢s Z
  ⊢n = S z≢n (S s≢n Z)
  ⊢m = S z≢m (S s≢m (S n≢m Z))

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

## Substitution

### Lists as sets

\begin{code}
_∈_ : Id → List Id → Set
x ∈ xs  =  Any (x ≡_) xs

_⊆_ : List Id → List Id → Set
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

∷⊆ : ∀ {x xs ys} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
∷⊆ xs⊆ (here refl)   =  here refl
∷⊆ xs⊆ (there ∈xs)   =  there (xs⊆ ∈xs)
\end{code}

### Free variables

\begin{code}
_\\_ : List Id → Id → List Id
xs \\ x  =  filter (¬? ∘ (x ≟_)) xs

free : Term → List Id
free ⌊ x ⌋          =  [ x ]
free (ƛ x ⦂ A ⇒ N)  =  free N \\ x
free (L · M)        =  free L ++ free M
\end{code}

### Fresh identifier

\begin{code}
fresh : List Id → Id
fresh = suc ∘ foldr _⊔_ 0

⊔-lemma : ∀ {x xs} → x ∈ xs → x ≤ foldr _⊔_ 0 xs
⊔-lemma (here refl)  =  m≤m⊔n _ _
⊔-lemma (there x∈)   =  ≤-trans (⊔-lemma x∈) (n≤m⊔n _ _)

fresh-lemma : ∀ {x xs} → x ∈ xs → fresh xs ≢ x
fresh-lemma x∈ refl =  1+n≰n (⊔-lemma x∈)
\end{code}

### Identifier maps

\begin{code}
∅ : Id → Term
∅ x = ⌊ x ⌋

_,_↦_ : (Id → Term) → Id → Term → (Id → Term)
(ρ , x ↦ M) y with x ≟ y
...               | yes _   =  M
...               | no  _   =  ρ y
\end{code}

### Substitution

\begin{code}
subst : List Id → (Id → Term) → Term → Term
subst xs ρ ⌊ x ⌋          = ρ x
subst xs ρ (ƛ x ⦂ A ⇒ N)  = ƛ y ⦂ A ⇒ subst (y ∷ xs) (ρ , x ↦ ⌊ y ⌋) N
  where
  y = fresh xs
subst xs ρ (L · M)        = subst xs ρ L · subst xs ρ M

_[_:=_] : Term → Id → Term → Term
N [ x := M ]  =  subst (free M) (∅ , x ↦ M) N
\end{code}


## Substitution preserves types

### Domain of an environment

\begin{code}
dom : Env → List Id
dom ε            =  []
dom (Γ , x ⦂ A)  =  x ∷ dom Γ

dom-lemma : ∀ {Γ y B} → Γ ∋ y ⦂ B → y ∈ dom Γ
dom-lemma Z           =  here refl
dom-lemma (S x≢y ⊢y)  =  there (dom-lemma ⊢y)
\end{code}

### Renaming

\begin{code}

⊢rename : ∀ {Γ Δ} → (∀ {z C} → Γ ∋ z ⦂ C → Δ ∋ z ⦂ C) →
                    (∀ {M C} → Γ ⊢ M ⦂ C → Δ ⊢ M ⦂ C)
⊢rename ⊢ρ (⌊ ⊢x ⌋)    =  ⌊ ⊢ρ ⊢x ⌋
⊢rename {Γ} {Δ} ⊢ρ (ƛ_ {x = x} {A = A} N)
                       =  ƛ (⊢rename {Γ , x ⦂ A} {Δ , x ⦂ A} ⊢ρ′ N)
  where
  ⊢ρ′ : ∀ {z C} → Γ , x ⦂ A ∋ z ⦂ C → Δ , x ⦂ A ∋ z ⦂ C
  ⊢ρ′ Z                =  Z
  ⊢ρ′ (S x≢y k)        =  S x≢y (⊢ρ k)
⊢rename ⊢ρ (L · M)     =  ⊢rename ⊢ρ L · ⊢rename ⊢ρ M
\end{code}

### Extending environment

The following can be used to shorten the definition that substitution preserves types,
but it actually makes the proof longer and more complex, so is probably not worth it.
\begin{code}
extend : ∀ {Γ Δ ρ x y A M} → (∀ {z C} → Δ ∋ z ⦂ C → y ≢ z) → (Δ , y ⦂ A ⊢ M ⦂ A) →
  (∀ {z C} → Γ         ∋ z ⦂ C → Δ         ⊢ ρ z           ⦂ C) →
  (∀ {z C} → Γ , x ⦂ A ∋ z ⦂ C → Δ , y ⦂ A ⊢ (ρ , x ↦ M) z ⦂ C)
extend {x = x} y≢ ⊢M ⊢ρ Z  with x ≟ x
...       | yes _             =  ⊢M
...       | no  x≢x           =  ⊥-elim (x≢x refl)
extend {Δ = Δ} {x = x} {y = y} {A = A} y≢ ⊢M ⊢ρ {z} (S x≢z ⊢z) with x ≟ z
...       | yes x≡z           =  ⊥-elim (x≢z x≡z)
...       | no  _             =  ⊢rename {Δ} {Δ , y ⦂ A} ⊢weaken (⊢ρ ⊢z)
  where
  ⊢weaken : ∀ {z C} → Δ ∋ z ⦂ C → Δ , y ⦂ A ∋ z ⦂ C
  ⊢weaken ⊢z  =  S (y≢ ⊢z) ⊢z
\end{code}

### Substitution preserves types

\begin{code}
⊢subst : ∀ {Γ Δ xs ρ} → (dom Δ ⊆ xs) → (∀ {x A} → Γ ∋ x ⦂ A → Δ ⊢ ρ x ⦂ A) →
                                       (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ subst xs ρ M ⦂ A)
⊢subst ⊆xs ⊢ρ ⌊ ⊢x ⌋            =  ⊢ρ ⊢x
⊢subst {Γ} {Δ} {xs} {ρ} ⊆xs ⊢ρ (ƛ_ {x = x} {A = A} ⊢N)
                                = ƛ ⊢subst {Γ′} {Δ′} {xs′} {ρ′} ⊆xs′ ⊢ρ′ ⊢N
  where
  y   =  fresh xs
  Γ′  =  Γ , x ⦂ A
  Δ′  =  Δ , y ⦂ A
  xs′ =  y ∷ xs
  ρ′  =  ρ , x ↦ ⌊ y ⌋

  ⊆xs′ :  dom Δ′ ⊆ xs′
  ⊆xs′ =  ∷⊆ ⊆xs

  y-lemma : ∀ {z C} → Δ ∋ z ⦂ C → y ≢ z
  y-lemma ⊢z                    =   fresh-lemma (⊆xs (dom-lemma ⊢z))

  ⊢weaken : ∀ {z C} → Δ ∋ z ⦂ C → Δ′ ∋ z ⦂ C
  ⊢weaken ⊢z                    =  S (y-lemma ⊢z) ⊢z

  ⊢ρ′ : ∀ {z C} → Γ′ ∋ z ⦂ C → Δ′ ⊢ ρ′ z ⦂ C
  ⊢ρ′  =  extend y-lemma ⌊ Z ⌋ ⊢ρ
{-
  ⊢ρ′ : ∀ {z C} → Γ′ ∋ z ⦂ C → Δ′ ⊢ ρ′ z ⦂ C
  ⊢ρ′ Z  with x ≟ x
  ...       | yes _             =  ⌊ Z ⌋
  ...       | no  x≢x           =  ⊥-elim (x≢x refl)
  ⊢ρ′ {z} (S x≢z ⊢z) with x ≟ z
  ...       | yes x≡z           =  ⊥-elim (x≢z x≡z)
  ...       | no  _             =  ⊢rename {Δ} {Δ′} ⊢weaken (⊢ρ ⊢z) 
-}
⊢subst ⊆xs ⊢ρ (⊢L · ⊢M)         =  ⊢subst ⊆xs ⊢ρ ⊢L · ⊢subst ⊆xs ⊢ρ ⊢M
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


## Biggest identifier

\begin{code}
fresh′ : ∀ (Γ : Env) → ∃[ w ] (∀ {z C} → Γ ∋ z ⦂ C → z ≤ w)
fresh′ ε                           = ⟨ 0 , σ ⟩
  where
  σ : ∀ {z C} → ε ∋ z ⦂ C → z ≤ 0
  σ ()
fresh′ (Γ , x ⦂ A) with fresh′ Γ
...                  | ⟨ w , σ ⟩  = ⟨ w′ , σ′ ⟩
  where
  w′  = x ⊔ w
  σ′ : ∀ {z C} → Γ , x ⦂ A ∋ z ⦂ C → z ≤ w′
  σ′ Z        =  m≤m⊔n x w
  σ′ (S _ k)  =  ≤-trans (σ k) (n≤m⊔n x w)

fresh′-lemma : ∀ {z w} → z ≤ w → 1 + w ≢ z
fresh′-lemma {z} {w} z≤w 1+w≡z = 1+n≰n (≤-trans 1+w≤z z≤w)
  where
  1+w≤z : 1 + w ≤ z
  1+w≤z rewrite 1+w≡z = ≤-refl
\end{code}

## Renaming

\begin{code}
rename′ : ∀ {Γ} → (∀ {z C} → Γ ∋ z ⦂ C → Id) → (∀ {M A} → Γ ⊢ M ⦂ A → Term)
rename′ ρ (⌊ k ⌋)                       =  ⌊ ρ k ⌋
rename′ ρ (⊢L · ⊢M)                     =  (rename′ ρ ⊢L) · (rename′ ρ ⊢M)
rename′ {Γ} ρ (ƛ_ {x = x} {A = A} ⊢N)   =  ƛ x′ ⦂ A ⇒ (rename′ ρ′ ⊢N)
  where
  x′    : Id
  x′    = 1 + proj₁ (fresh′ Γ)
  ρ′ : ∀ {z C} → Γ , x ⦂ A ∋ z ⦂ C → Id
  ρ′ Z        =  x′
  ρ′ (S _ j)  =  ρ j
\end{code}

CONTINUE FROM HERE

\begin{code}
{-
⊢rename′ : ∀ {Γ Δ} → (ρ : ∀ {z C} → Γ ∋ z ⦂ C → ∃[ z′ ] (Δ ∋ z′ ⦂ C)) →
                       (∀ {M A} → (⊢M : Γ ⊢ M ⦂ A) → Δ ⊢ rename′ (proj₁ ∘ ρ) ⊢M ⦂ A)
⊢rename′ ρ (⌊ k ⌋)             =  ⌊ proj₂ (ρ k) ⌋
⊢rename′ ρ (⊢L · ⊢M)           =  (⊢rename′ ρ ⊢L) · (⊢rename′ ρ ⊢M)
⊢rename′ {Γ} {Δ} ρ (ƛ_ {x = x} {A = A} ⊢N) with fresh′ Γ
... | ⟨ w , σ ⟩               =  {!!}  -- ƛ (⊢rename′ {Γ , x ⦂ A} {Δ , x′ ⦂ A} ρ′ ⊢N)
  where
  x′    : Id
  x′    = 1 + w
  ρ′ : ∀ {z C} → Γ , x ⦂ A ∋ z ⦂ C → ∃[ z′ ] (Δ , x′ ⦂ A ∋ z′ ⦂ C)
  ρ′ Z                         =  ⟨ x′ , Z ⟩
  ρ′ (S _ j) with ρ j
  ...           | ⟨ z′ , j′ ⟩  =  ⟨ z′ , S (fresh′-lemma (σ j)) j′ ⟩
-}
\end{code}

