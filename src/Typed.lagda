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
open import Data.List using (List; []; _∷_; _++_; map; foldr; filter)
open import Data.List.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _⊔_; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; 1+n≰n)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax)
              renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equality using (≡-setoid)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contraposition; ¬?)
open import Relation.Nullary.Product using (_×-dec_)
open import Collections using (_↔_)
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


## Erasure

\begin{code}
lookup : ∀ {Γ x A} → Γ ∋ x ⦂ A → Id
lookup {Γ , x ⦂ A} Z        =  x
lookup {Γ , x ⦂ A} (S _ k)  =  lookup {Γ} k

erase : ∀ {Γ M A} → Γ ⊢ M ⦂ A → Term
erase ⌊ k ⌋                     =  ⌊ lookup k ⌋
erase (ƛ_ {x = x} {A = A} ⊢N)   =  ƛ x ⦂ A ⇒ erase ⊢N
erase (⊢L · ⊢M)                 =  erase ⊢L · erase ⊢M
\end{code}

### Properties of erasure

\begin{code}
lookup-lemma : ∀ {Γ x A} → (k : Γ ∋ x ⦂ A) → lookup k ≡ x
lookup-lemma Z        =  refl
lookup-lemma (S _ k)  =  lookup-lemma k

erase-lemma : ∀ {Γ M A} → (⊢M : Γ ⊢ M ⦂ A) → erase ⊢M ≡ M
erase-lemma ⌊ k ⌋                    =  cong ⌊_⌋ (lookup-lemma k)
erase-lemma (ƛ_ {x = x} {A = A} ⊢N)  =  cong (ƛ x ⦂ A ⇒_) (erase-lemma ⊢N)
erase-lemma (⊢L · ⊢M)                =  cong₂ _·_ (erase-lemma ⊢L) (erase-lemma ⊢M)
\end{code}


## Substitution

### Lists as sets

\begin{code}
open Collections.CollectionDec (Id) (_≟_)
\end{code}

### Properties of sets

\begin{code}
-- ⊆∷ : ∀ {y xs ys} → xs ⊆ ys → xs ⊆ y ∷ ys
-- ∷⊆∷ : ∀ {x xs ys} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
-- []⊆ : ∀ {x xs} → [ x ] ⊆ xs → x ∈ xs
-- ⊆[] : ∀ {x xs} → x ∈ xs → [ x ] ⊆ xs
-- bind : ∀ {x xs} → xs \\ x ⊆ xs
-- left : ∀ {xs ys} → xs ⊆ xs ∪ ys
-- right : ∀ {xs ys} → ys ⊆ xs ∪ ys
-- prev : ∀ {z y xs} → y ≢ z → z ∈ y ∷ xs → z ∈ xs
\end{code}

### Free variables

\begin{code}
free : Term → List Id
free ⌊ x ⌋          =  [ x ]
free (ƛ x ⦂ A ⇒ N)  =  free N \\ x
free (L · M)        =  free L ∪ free M
\end{code}


### Fresh identifier

\begin{code}
fresh : List Id → Id
fresh = foldr _⊔_ 0 ∘ map suc

⊔-lemma : ∀ {x xs} → x ∈ xs → suc x ≤ fresh xs
⊔-lemma {x} {.x ∷ xs} here         =  m≤m⊔n (suc x) (fresh xs)
⊔-lemma {x} {y  ∷ xs} (there x∈)   =  ≤-trans (⊔-lemma {x} {xs} x∈)
                                              (n≤m⊔n (suc y) (fresh xs))

fresh-lemma : ∀ {x xs} → x ∈ xs → fresh xs ≢ x
fresh-lemma x∈ refl =  1+n≰n (⊔-lemma x∈)
\end{code}

### Identifier maps

\begin{code}
∅ : Id → Term
∅ x = ⌊ x ⌋

_,_↦_ : (Id → Term) → Id → Term → (Id → Term)
(ρ , x ↦ M) w with w ≟ x
...               | yes _   =  M
...               | no  _   =  ρ w
\end{code}

### Substitution

\begin{code}
subst : List Id → (Id → Term) → Term → Term
subst ys ρ ⌊ x ⌋          =  ρ x
subst ys ρ (ƛ x ⦂ A ⇒ N)  =  ƛ y ⦂ A ⇒ subst (y ∷ ys) (ρ , x ↦ ⌊ y ⌋) N
  where
  y = fresh ys
subst ys ρ (L · M)        =  subst ys ρ L · subst ys ρ M

_[_:=_] : Term → Id → Term → Term
N [ x := M ]  =  subst (free M ∪ (free N \\ x)) (∅ , x ↦ M) N
\end{code}


## Values

\begin{code}
data Value : Term → Set where

  Fun : ∀ {x A N} →
    --------------------
    Value (ƛ x ⦂ A ⇒ N)
\end{code}

## Reduction

\begin{code}
infix 4 _⟹_

data _⟹_ : Term → Term → Set where

  β-⇒ : ∀ {x A N V} →
    Value V →
    ----------------------------------
    (ƛ x ⦂ A ⇒ N) · V ⟹ N [ x := V ]

  ξ-⇒₁ : ∀ {L L′ M} →
    L ⟹ L′ →
    ----------------
    L · M ⟹ L′ · M

  ξ-⇒₂ : ∀ {V M M′} →
    Value V →
    M ⟹ M′ →
    ----------------
    V · M ⟹ V · M′
\end{code}

## Reflexive and transitive closure

\begin{code}
infix  2 _⟹*_
infix 1 begin_
infixr 2 _⟹⟨_⟩_
infix 3 _∎

data _⟹*_ : Term → Term → Set where

  _∎ : ∀ {M} →
    -------------
    M ⟹* M

  _⟹⟨_⟩_ : ∀ (L : Term) {M N} →
    L ⟹ M →
    M ⟹* N →
    ---------
    L ⟹* N

begin_ : ∀ {M N} → (M ⟹* N) → (M ⟹* N)
begin M⟹*N = M⟹*N
\end{code}

## Progress

\begin{code}
data Progress (M : Term) : Set where
  step : ∀ {N} → M ⟹ N → Progress M
  done : Value M → Progress M

progress : ∀ {M A} → ε ⊢ M ⦂ A → Progress M
progress ⌊ () ⌋
progress (ƛ_ ⊢N)                                          =  done Fun
progress (⊢L · ⊢M) with progress ⊢L
...                   | step L⟹L′                       =  step (ξ-⇒₁ L⟹L′)
...                   | done Fun      with progress ⊢M
...                                      | step M⟹M′    =  step (ξ-⇒₂ Fun M⟹M′)
...                                      | done valM      =  step (β-⇒ valM)
\end{code}


## Preservation

### Domain of an environment

\begin{code}
dom : Env → List Id
dom ε            =  []
dom (Γ , x ⦂ A)  =  x ∷ dom Γ

dom-lemma : ∀ {Γ y B} → Γ ∋ y ⦂ B → y ∈ dom Γ
dom-lemma Z           =  here
dom-lemma (S x≢y ⊢y)  =  there (dom-lemma ⊢y)

free-lemma : ∀ {Γ M A} → Γ ⊢ M ⦂ A → free M ⊆ dom Γ
free-lemma ⌊ ⊢x ⌋ w∈ with w∈
...                     | here         =  dom-lemma ⊢x
...                     | there ()   
free-lemma {Γ} (ƛ_ {x = x} {N = N} ⊢N)  =  proj₂ lemma-\\-∷ (free-lemma ⊢N)
free-lemma (⊢L · ⊢M) w∈ with proj₂ lemma-⊎-∪ w∈
...                        | inj₁ ∈L    = free-lemma ⊢L ∈L
...                        | inj₂ ∈M    = free-lemma ⊢M ∈M


-- f : ∀ {x y} → y ∈ [ x ] → y ≡ x
-- g : ∀ {w xs ys} → w ∈ xs ∪ ys → w ∈ xs ⊎ w ∈ ys
-- k : ∀ {w x xs} → w ∈ xs \\ x → x ≢ w
-- h : ∀ {x xs ys} → xs ⊆ x ∷ ys → xs \\ x ⊆ ys

\end{code}

### Renaming

\begin{code}
-- ∷drop : ∀ {v vs ys} → v ∷ vs ⊆ ys → vs ⊆ ys
-- i : ∀ {w x xs} → w ∈ xs → x ≢ w → w ∈ xs \\ x
-- j : ∀ {x xs ys} → xs \\ x ⊆ ys → xs ⊆ x ∷ ys

⊢rename : ∀ {Γ Δ xs} → (∀ {x A} → x ∈ xs      →  Γ ∋ x ⦂ A  →  Δ ∋ x ⦂ A) →
                       (∀ {M A} → free M ⊆ xs →  Γ ⊢ M ⦂ A  →  Δ ⊢ M ⦂ A)
⊢rename ⊢σ ⊆xs (⌊ ⊢x ⌋)              =  ⌊ ⊢σ ∈xs ⊢x ⌋
  where
  ∈xs = proj₂ lemma-[_] ⊆xs
⊢rename {Γ} {Δ} {xs} ⊢σ ⊆xs (ƛ_ {x = x} {A = A} {N = N} ⊢N)
                                     =  ƛ (⊢rename {Γ′} {Δ′} {xs′} ⊢σ′ ⊆xs′ ⊢N)
  where
  Γ′   =  Γ , x ⦂ A
  Δ′   =  Δ , x ⦂ A
  xs′  =  x ∷ xs

  ⊢σ′ : ∀ {y B} → y ∈ xs′ → Γ′ ∋ y ⦂ B → Δ′ ∋ y ⦂ B
  ⊢σ′ ∈xs′ Z                         =  Z
  ⊢σ′ ∈xs′ (S x≢y ⊢y) with ∈xs′
  ...                   | here       =  ⊥-elim (x≢y refl)
  ...                   | there ∈xs  =  S x≢y (⊢σ ∈xs ⊢y)

  ⊆xs′ : free N ⊆ xs′
  ⊆xs′  = proj₁ lemma-\\-∷ ⊆xs
⊢rename {xs = xs} ⊢σ {L · M} ⊆xs (⊢L · ⊢M)
                                     =  ⊢rename ⊢σ L⊆ ⊢L · ⊢rename ⊢σ M⊆ ⊢M
  where
  L⊆ = trans-⊆ (proj₁ lemma-⊎-∪ ∘ inj₁) ⊆xs
  M⊆ = trans-⊆ (proj₁ lemma-⊎-∪ ∘ inj₂) ⊆xs
\end{code}


### Substitution preserves types

\begin{code}
lemma₁ : ∀ {y ys} → [ y ] ⊆ y ∷ ys
lemma₁ = proj₁ lemma-[_] here

lemma₂ : ∀ {w x xs} → x ≢ w → w ∈ x ∷ xs → w ∈ xs
lemma₂ x≢  here        =  ⊥-elim (x≢ refl)
lemma₂ _   (there w∈)  =  w∈

⊢subst : ∀ {Γ Δ xs ys ρ} →
             (∀ {x}   → x ∈ xs      →  free (ρ x) ⊆ ys) →
             (∀ {x A} → x ∈ xs      →  Γ ∋ x ⦂ A  →  Δ ⊢ ρ x ⦂ A) →
             (∀ {M A} → free M ⊆ xs →  Γ ⊢ M ⦂ A  →  Δ ⊢ subst ys ρ M ⦂ A)
⊢subst Σ ⊢ρ ⊆xs ⌊ ⊢x ⌋
    =  ⊢ρ (⊆xs here) ⊢x
⊢subst {Γ} {Δ} {xs} {ys} {ρ} Σ ⊢ρ ⊆xs (ƛ_ {x = x} {A = A} {N = N} ⊢N)
    = ƛ_ {x = y} {A = A} (⊢subst {Γ′} {Δ′} {xs′} {ys′} {ρ′} Σ′ ⊢ρ′ ⊆xs′ ⊢N)
  where
  y   =  fresh ys
  Γ′  =  Γ , x ⦂ A
  Δ′  =  Δ , y ⦂ A
  xs′ =  x ∷ xs
  ys′ =  y ∷ ys
  ρ′  =  ρ , x ↦ ⌊ y ⌋

  Σ′ : ∀ {w} → w ∈ xs′ →  free (ρ′ w) ⊆ ys′
  Σ′ {w} here         with w ≟ x
  ...                    | yes refl  =  lemma₁
  ...                    | no  w≢    =  ⊥-elim (w≢ refl)
  Σ′ {w} (there w∈)   with w ≟ x
  ...                    | yes refl  =  lemma₁
  ...                    | no  _     =  there ∘ (Σ w∈)
  
  ⊆xs′ :  free N ⊆ xs′
  ⊆xs′ =  proj₁ lemma-\\-∷ ⊆xs

  ⊢σ : ∀ {w C} → w ∈ ys → Δ ∋ w ⦂ C → Δ′ ∋ w ⦂ C
  ⊢σ w∈ ⊢w  =  S (fresh-lemma w∈) ⊢w

  ⊢ρ′ : ∀ {w C} → w ∈ xs′ → Γ′ ∋ w ⦂ C → Δ′ ⊢ ρ′ w ⦂ C
  ⊢ρ′ _ Z  with x ≟ x
  ...         | yes _             =  ⌊ Z ⌋
  ...         | no  x≢x           =  ⊥-elim (x≢x refl)
  ⊢ρ′ {w} w∈′ (S x≢w ⊢w) with w ≟ x
  ...         | yes refl          =  ⊥-elim (x≢w refl)
  ...         | no  _             =  ⊢rename {Δ} {Δ′} {ys} ⊢σ (Σ w∈) (⊢ρ w∈ ⊢w)
              where
              w∈  =  lemma₂ x≢w w∈′ 

⊢subst {xs = xs} Σ ⊢ρ {L · M} ⊆xs (⊢L · ⊢M)
    =  ⊢subst Σ ⊢ρ L⊆ ⊢L · ⊢subst Σ ⊢ρ M⊆ ⊢M
  where
  L⊆ = trans-⊆ (proj₁ lemma-⊎-∪ ∘ inj₁) ⊆xs
  M⊆ = trans-⊆ (proj₁ lemma-⊎-∪ ∘ inj₂) ⊆xs

⊢substitution : ∀ {Γ x A N B M} →
  Γ , x ⦂ A ⊢ N ⦂ B →
  Γ ⊢ M ⦂ A →
  --------------------
  Γ ⊢ N [ x := M ] ⦂ B
⊢substitution {Γ} {x} {A} {N} {B} {M} ⊢N ⊢M =
  ⊢subst {Γ′} {Γ} {xs} {ys} {ρ} Σ ⊢ρ {N} {B} ⊆xs ⊢N
  where
  Γ′     =  Γ , x ⦂ A
  xs     =  free N
  ys     =  free M ∪ (free N \\ x)
  ρ      =  ∅ , x ↦ M

  Σ : ∀ {w} → w ∈ xs → free (ρ w) ⊆ ys
  Σ {w} w∈ y∈ with w ≟ x
  ...            | yes _                  =  lemma-∪₁ y∈
  ...            | no w≢  with y∈
  ...                        | here       =  lemma-∪₂
                                 (proj₂ (lemma-\\-∈-≢ {w} {x} {free N}) ⟨ w∈ , w≢ ⟩)
  ...                        | there ()   
  
  ⊢ρ : ∀ {z C} → z ∈ xs → Γ′ ∋ z ⦂ C → Γ ⊢ ρ z ⦂ C
  ⊢ρ {.x} z∈ Z         with x ≟ x
  ...                     | yes _     =  ⊢M
  ...                     | no  x≢x   =  ⊥-elim (x≢x refl)
  ⊢ρ {z} z∈ (S x≢z ⊢z) with z ≟ x
  ...                     | yes refl  =  ⊥-elim (x≢z refl)
  ...                     | no  _     =  ⌊ ⊢z ⌋

  ⊆xs : free N ⊆ xs
  ⊆xs x∈ = x∈
\end{code}

### Preservation

\begin{code}
preservation : ∀ {Γ M N A} →  Γ ⊢ M ⦂ A  →  M ⟹ N  →  Γ ⊢ N ⦂ A
preservation ⌊ ⊢x ⌋ ()
preservation (ƛ ⊢N) ()
preservation (⊢L · ⊢M) (ξ-⇒₁ L⟹L′)        =  preservation ⊢L L⟹L′ · ⊢M
preservation (⊢V · ⊢M) (ξ-⇒₂ valV M⟹M′)   =  ⊢V · preservation ⊢M M⟹M′
preservation ((ƛ ⊢N) · ⊢W) (β-⇒ valW)      =  ⊢substitution ⊢N ⊢W
\end{code}



