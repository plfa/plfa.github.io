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
subst xs ρ ⌊ x ⌋          =  ρ x
subst xs ρ (ƛ x ⦂ A ⇒ N)  =  ƛ y ⦂ A ⇒ subst (y ∷ xs) (ρ , x ↦ ⌊ y ⌋) N
  where
  y = fresh xs
subst xs ρ (L · M)        =  subst xs ρ L · subst xs ρ M

_[_:=_] : Term → Id → Term → Term
N [ x := M ]  =  subst (free M) (∅ , x ↦ M) N
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
progress (ƛ_ ⊢N)                                        =  done Fun
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
dom-lemma Z           =  here refl
dom-lemma (S x≢y ⊢y)  =  there (dom-lemma ⊢y)

free-lemma : ∀ {Γ M A} → Γ ⊢ M ⦂ A → free M ⊆ dom Γ
free-lemma = {!!}
\end{code}

### Weakening

\begin{code}

⊢weaken : ∀ {Γ Δ} → (∀ {z C} → Γ ∋ z ⦂ C  →  Δ ∋ z ⦂ C) →
                    (∀ {M C} → Γ ⊢ M ⦂ C  →  Δ ⊢ M ⦂ C)
⊢weaken ⊢σ (⌊ ⊢x ⌋)    =  ⌊ ⊢σ ⊢x ⌋
⊢weaken {Γ} {Δ} ⊢σ (ƛ_ {x = x} {A = A} N)
                       =  ƛ (⊢weaken {Γ , x ⦂ A} {Δ , x ⦂ A} ⊢σ′ N)
  where
  ⊢σ′ : ∀ {z C} → Γ , x ⦂ A ∋ z ⦂ C → Δ , x ⦂ A ∋ z ⦂ C
  ⊢σ′ Z                =  Z
  ⊢σ′ (S x≢y k)        =  S x≢y (⊢σ k)
⊢weaken ⊢σ (L · M)     =  ⊢weaken ⊢σ L · ⊢weaken ⊢σ M
\end{code}


### Substitution preserves types

\begin{code}
⊢subst : ∀ {Γ Δ xs ρ} → (dom Δ ⊆ xs) →
             (∀ {x A} → Γ ∋ x ⦂ A  →  Δ ⊢ ρ x ⦂ A) →
             (∀ {M A} → Γ ⊢ M ⦂ A  →  Δ ⊢ subst xs ρ M ⦂ A)
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

  y≢ : ∀ {z C} → Δ ∋ z ⦂ C → y ≢ z
  y≢ ⊢z  =  fresh-lemma (⊆xs (dom-lemma ⊢z))

  ⊢σ : ∀ {z C} → Δ ∋ z ⦂ C → Δ′ ∋ z ⦂ C
  ⊢σ ⊢z  =  S (y≢ ⊢z) ⊢z

  ⊢ρ′ : ∀ {z C} → Γ′ ∋ z ⦂ C → Δ′ ⊢ ρ′ z ⦂ C
  ⊢ρ′ Z  with x ≟ x
  ...       | yes _             =  ⌊ Z ⌋
  ...       | no  x≢x           =  ⊥-elim (x≢x refl)
  ⊢ρ′ {z} (S x≢z ⊢z) with x ≟ z
  ...       | yes x≡z           =  ⊥-elim (x≢z x≡z)
  ...       | no  _             =  ⊢weaken {Δ} {Δ′} ⊢σ (⊢ρ ⊢z) 

⊢subst ⊆xs ⊢ρ (⊢L · ⊢M)         =  ⊢subst ⊆xs ⊢ρ ⊢L · ⊢subst ⊆xs ⊢ρ ⊢M

⊢substitution : ∀ {Γ x A M B N} →
  Γ , x ⦂ A ⊢ N ⦂ B →
  Γ ⊢ M ⦂ A →
  --------------------
  Γ ⊢ N [ x := M ] ⦂ B
⊢substitution {Γ} {x} {A} {M} ⊢N ⊢M =
  {!!} -- ⊢subst {Γ , x ⦂ A} {Γ} {xs} {ρ}  ⊢ρ ⊢N
  where
  xs     =  dom Γ
  ρ      =  ∅ , x ↦ M
  ⊢ρ : ∀ {z C} → Γ , x ⦂ A ∋ z ⦂ C → Γ ⊢ ρ z ⦂ C
  ⊢ρ {.x} Z         with x ≟ x
  ...                  | yes _     =  ⊢M
  ...                  | no  x≢x   =  ⊥-elim (x≢x refl)
  ⊢ρ {z} (S x≢z ⊢x) with x ≟ z
  ...                  | yes x≡z   =  ⊥-elim (x≢z x≡z)
  ...                  | no  _     =  {!!}
\end{code}

Can I falsify the theorem? Consider the case where the renamed variable
already exists in the environment.

    (ƛ f ⦂ o ⇒ g) [ f := (ƛ z ⦂ o ⇒ z)]

Since I only rename to variables guaranteed not to be free in M and M is closed,
I could accidentally rename f to g. So I must instead pick all the variables
free in M and N.

In that case, could I still falsify preservation of typing? Let's say we have:

   ε , g ⦂ A , h ⦂ B ⊢ (ƛ f ⦂ o ⇒ o ⇒ g) ⦂ (o ⇒ o) ⇒ A
   ε , g ⦂ A , h ⦂ B ⊢ (ƛ z ⦂ o ⇒ z) ⦂ o ⇒ o

And let's say I rename f to h.  Then the result is:

   ε , g ⦂ A , h ⦂ B ⊢ λ h ⦂ o ⇒ g

Then `y≢` in the body of `⊢subst` is falsified, which could be an issue!

### Preservation

\begin{code}
preservation : ∀ {Γ M N A} →  Γ ⊢ M ⦂ A  →  M ⟹ N  →  Γ ⊢ N ⦂ A
preservation ⌊ ⊢x ⌋ ()
preservation (ƛ ⊢N) ()
preservation (⊢L · ⊢M) (ξ-⇒₁ L⟹L′)        =  preservation ⊢L L⟹L′ · ⊢M
preservation (⊢V · ⊢M) (ξ-⇒₂ valV M⟹M′)   =  ⊢V · preservation ⊢M M⟹M′
preservation ((ƛ ⊢N) · ⊢W) (β-⇒ valW)      =  ⊢substitution ⊢N ⊢W
\end{code}



