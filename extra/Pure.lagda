---
title     : "Pure: Pure Type Systems"
permalink : /Pure/
---

Barendregt, H. (1991). Introduction to generalized type
systems. Journal of Functional Programming, 1(2),
125-154. doi:10.1017/S0956796800020025

Fri 8 June

Tried to add weakening directly as a rule.  Doing so broke the
definition of renaming, and I could not figure out how to fix it.
Also, need to have variables as a separate construct in order to
define substitution a la Conor.  Tried to prove weakening as a derived
rule, but it is tricky.  In

  Π[_]_⇒_ : ∀ {n} {Γ : Context n} {A : Term n} {B : Term (suc n)} {s t : Sort}
    → Permitted s t
    → Γ ⊢ A ⦂ ⟪ s ⟫
    → Γ , A ⊢ B ⦂ ⟪ t ⟫
      -------------------
    → Γ ⊢ Π A ⇒ B ⦂ ⟪ t ⟫

weakening on the middle hypothesis take Γ to Γ , C but weakening on
the last hypothesis takes Γ , A to Γ , C , A, so permutation is required
before one can apply the induction hypothesis.  I presume this could
be done similarly to LambdaProp.





## Imports

\begin{code}
module Pure where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)
\end{code}

## Syntax

Scoped, but not inherently typed.

\begin{code}
infix   6  ƛ_⇒_
infix   7  Π_⇒_
infixr  8  _⇒_
infixl  9  _·_

data Sort : Set where
  * : Sort
  ▢ : Sort

data Var : ℕ → Set where

  Z : ∀ {n}
      -----------
    → Var (suc n)

  S_ : ∀ {n}
    → Var n
      -----------
    → Var (suc n)

data Term : ℕ → Set where

  ⟪_⟫ : ∀ {n}
    → Sort
      ------
    → Term n

  ⌊_⌋ : ∀ {n}
    → Var n
      ------
    → Term n

  Π_⇒_ : ∀ {n}
    → Term n
    → Term (suc n)
      ------------
    → Term n

  ƛ_⇒_ :  ∀ {n}
    → Term n
    → Term (suc n)
      ------------
    → Term n

  _·_ : ∀ {n}
    → Term n
    → Term n
      ------
    → Term n
\end{code}

## Renaming

\begin{code}
extr : ∀ {m n} → (Var m → Var n) → (Var (suc m) → Var (suc n))
extr ρ Z      =  Z
extr ρ (S k)  =  S (ρ k)

rename : ∀ {m n} → (Var m → Var n) → (Term m → Term n)
rename ρ ⟪ s ⟫      =  ⟪ s ⟫
rename ρ ⌊ k ⌋      =  ⌊ ρ k ⌋
rename ρ (Π A ⇒ B)  =  Π rename ρ A ⇒ rename (extr ρ) B
rename ρ (ƛ A ⇒ N)  =  ƛ rename ρ A ⇒ rename (extr ρ) N
rename ρ (L · M)    =  rename ρ L · rename ρ M
\end{code}

## Substitution

\begin{code}
exts : ∀ {m n} → (Var m → Term n) → (Var (suc m) → Term (suc n))
exts ρ Z      =  ⌊ Z ⌋
exts ρ (S k)  =  rename S_ (ρ k)

subst : ∀ {m n} → (Var m → Term n) → (Term m → Term n)
subst σ ⟪ s ⟫      =  ⟪ s ⟫
subst σ ⌊ k ⌋      =  σ k
subst σ (Π A ⇒ B)  =  Π subst σ A ⇒ subst (exts σ) B
subst σ (ƛ A ⇒ N)  =  ƛ subst σ A ⇒ subst (exts σ) N
subst σ (L · M)    =  subst σ L · subst σ M

_[_] : ∀ {n} → Term (suc n) → Term n → Term n
_[_] {n} N M  =  subst {suc n} {n} σ N
  where
  σ : Var (suc n) → Term n
  σ Z      =  M
  σ (S k)  =  ⌊ k ⌋
\end{code}

## Functions

\begin{code}
_⇒_ : ∀ {n} → Term n → Term n → Term n
A ⇒ B  = Π A ⇒ rename S_ B
\end{code}

## Writing variables as numerals

\begin{code}
var : ∀ n → ℕ → Var n
var zero    _        =  ⊥-elim impossible
  where postulate impossible : ⊥
var (suc n) 0        =  Z
var (suc n) (suc m)  =  S (var n m)

infix  10  #_

#_ : ∀ {n} → ℕ → Term n
#_ {n} m  =  ⌊ var n m ⌋
\end{code}

## Test examples

\begin{code}
Ch : ∀ {n} → Term n
Ch = Π ⟪ * ⟫ ⇒ ((# 0 ⇒ # 0) ⇒ # 0 ⇒ # 0)
-- Ch = Π X ⦂ * ⇒ (X ⇒ X) ⇒ X ⇒ X

two : ∀ {n} → Term n
two = ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒ # 1 · (# 1 · # 0)
-- two = ƛ X ⦂ * ⇒ ƛ s ⦂ (X ⇒ X) ⇒ ƛ z ⦂ X ⇒ s · (s · z)

four : ∀ {n} → Term n
four = ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒ # 1 · (# 1 · (# 1 · (# 1 · # 0)))
-- four = ƛ X ⦂ * ⇒ ƛ s ⦂ (X ⇒ X) ⇒ ƛ z ⦂ X ⇒ s · (s · (s · (s · z)))

plus : ∀ {n} → Term n
plus = ƛ Ch ⇒ ƛ Ch ⇒ ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒
         (# 4 · # 2 · # 1 · (# 3 · # 2 · # 1 · # 0))
-- plus = ƛ m ⦂ Ch ⇒ ƛ n ⦂ Ch ⇒ ƛ X ⦂ * ⇒ ƛ s ⦂ (X ⇒ X) ⇒ ƛ z ⦂ X ⇒
--          m X s (n X s z)
\end{code}

## Normal

\begin{code}
data Normal  : ∀ {n} → Term n → Set
data Neutral : ∀ {n} → Term n → Set

data Normal where

  ⟪_⟫ : ∀ {n} {s : Sort}
      ----------------
    → Normal {n} ⟪ s ⟫

  Π_⇒_ : ∀ {n} {A : Term n} {B : Term (suc n)}
    → Normal A
    → Normal B
      ----------------
    → Normal (Π A ⇒ B)

  ƛ_⇒_ : ∀ {n} {A : Term n} {N : Term (suc n)}
    → Normal A
    → Normal N
      ----------------
    → Normal (ƛ A ⇒ N)

  ⌈_⌉  : ∀ {n} {M : Term n}
    → Neutral M
      ---------
    → Normal M

data Neutral where

  ⌊_⌋ : ∀ {n}
    → (k : Var n)
      -------------
    → Neutral ⌊ k ⌋

  _·_ : ∀ {n} {L : Term n} {M : Term n}
    → Neutral L
    → Normal M
      ---------------
    → Neutral (L · M)
\end{code}

Convenient shorthand for neutral variables.

\begin{code}
infix  10  #ᵘ_

#ᵘ_ : ∀ {n} (m : ℕ) → Neutral ⌊ var n m ⌋
#ᵘ_ {n} m  =  ⌊ var n m ⌋
\end{code}


## Reduction step

\begin{code}
infix 2 _⟶_

Application : ∀ {n} → Term n → Set
Application ⟪ _ ⟫        =  ⊥
Application ⌊ _ ⌋        =  ⊥
Application (Π _ ⇒ _)    =  ⊥
Application (ƛ _ ⇒ _)    =  ⊥
Application (_ · _)      =  ⊤

data _⟶_ : ∀ {n} → Term n → Term n → Set where

  ξ₁ : ∀ {n} {L L′ M : Term n}
    → Application L
    → L ⟶ L′
      ----------------
    → L · M ⟶ L′ · M

  ξ₂ : ∀ {n} {L M M′ : Term n}
    → Neutral L
    → M ⟶ M′
      ----------------
    → L · M ⟶ L · M′

  β : ∀ {n} {A : Term n} {N : Term (suc n)} {M : Term n}
      --------------------------------------------------
    → (ƛ A ⇒ N) · M ⟶ N [ M ]

  ζΠ₁ : ∀ {n} {A A′ : Term n} {B : Term (suc n)}
    → A ⟶ A′
      --------------------
    → Π A ⇒ B ⟶ Π A′ ⇒ B

  ζΠ₂ : ∀ {n} {A : Term n} {B B′ : Term (suc n)}
    → B ⟶ B′
      --------------------
    → Π A ⇒ B ⟶ Π A ⇒ B′

  ζƛ₁ : ∀ {n} {A A′ : Term n} {B : Term (suc n)}
    → A ⟶ A′
      --------------------
    → ƛ A ⇒ B ⟶ ƛ A′ ⇒ B

  ζƛ₂ : ∀ {n} {A : Term n} {B B′ : Term (suc n)}
    → B ⟶ B′
      --------------------
    → ƛ A ⇒ B ⟶ ƛ A ⇒ B′
\end{code}

## Reflexive and transitive closure

\begin{code}
infix  2 _⟶*_
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3 _∎

data _⟶*_ : ∀ {n} → Term n → Term n → Set where

  _∎ : ∀ {n} (M : Term n)
      ---------------------
    → M ⟶* M

  _⟶⟨_⟩_ : ∀ {n} (L : Term n) {M N : Term n}
    → L ⟶ M
    → M ⟶* N
      ---------
    → L ⟶* N

  begin_ : ∀ {n} {M N : Term n}
    → M ⟶* N
      --------
    → M ⟶* N
\end{code}

## Reflexive, symmetric, and transitive closure

\begin{code}
data _=β_ : ∀ {n} → Term n → Term n → Set where

  _∎ : ∀ {n} (M : Term n)
      -------------------
    → M =β M

  _⟶⟨_⟩_ : ∀ {n} (L : Term n) {M N : Term n}
    → L ⟶ M
    → M =β N
      ---------
    → L =β N

  _⟵⟨_⟩_ : ∀ {n} (L : Term n) {M N : Term n}
    → M ⟶ L
    → M =β N
      ---------
    → L =β N

  begin_ : ∀ {n} {M N : Term n}
    → M =β N
      --------
    → M =β N
\end{code}


## Example reduction sequences

\begin{code}
Id : Term zero
Id = Π ⟪ * ⟫ ⇒ (# 0 ⇒ # 0)
-- Id = Π X ⦂ ⟪ * ⟫ ⇒ (X ⇒ X)

id : Term zero
id = ƛ ⟪ * ⟫ ⇒ ƛ # 0 ⇒ # 0
-- id = ƛ X ⦂ ⟪ * ⟫ ⇒ ƛ x ⦂ X ⇒ x

_ : id · Id · id  ⟶* id
_ =
  begin
    id · Id · id
  ⟶⟨ ξ₁ tt β ⟩
    (ƛ Id ⇒ # 0) · id
  ⟶⟨ β ⟩
    id
  ∎

_ : plus {zero} · two · two ⟶* four
_ =
  begin
    plus · two · two
  ⟶⟨ ξ₁ tt β ⟩
    (ƛ Ch ⇒ ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒
      two · # 2 · # 1 · (# 3 · # 2 · # 1 · # 0)) · two
  ⟶⟨ β ⟩
    ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒ two · # 2 · # 1 · (two · # 2 · # 1 · # 0)
  ⟶⟨ ζƛ₂ (ζƛ₂ (ζƛ₂ (ξ₁ tt (ξ₁ tt β)))) ⟩
    ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒
      (ƛ (# 2 ⇒ # 2) ⇒ ƛ # 3 ⇒ # 1 · (# 1 · # 0)) · # 1 · (two · # 2 · # 1 · # 0)
  ⟶⟨ ζƛ₂ (ζƛ₂ (ζƛ₂ (ξ₁ tt β))) ⟩
    ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒
      (ƛ # 2 ⇒ # 2 · (# 2 · # 0)) · (two · # 2 · # 1 · # 0)
  ⟶⟨ ζƛ₂ (ζƛ₂ (ζƛ₂ β)) ⟩
    ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒ # 1 · (# 1 · (two · # 2 · # 1 · # 0))
  ⟶⟨ ζƛ₂ (ζƛ₂ (ζƛ₂ (ξ₂ (#ᵘ 1) (ξ₂ (#ᵘ 1) (ξ₁ tt (ξ₁ tt β)))))) ⟩
    ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒ # 1 · (# 1 ·
      ((ƛ (# 2 ⇒ # 2) ⇒ ƛ # 3 ⇒ # 1 · (# 1 · # 0)) · # 1 · # 0))
  ⟶⟨ ζƛ₂ (ζƛ₂ (ζƛ₂ (ξ₂ (#ᵘ 1) (ξ₂ (#ᵘ 1) (ξ₁ tt β))))) ⟩
    ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒ # 1 · (# 1 ·
      ((ƛ # 2 ⇒ # 2 · (# 2 · # 0)) · # 0))
  ⟶⟨ ζƛ₂ (ζƛ₂ (ζƛ₂ (ξ₂ (#ᵘ 1) (ξ₂ (#ᵘ 1) β)))) ⟩
    ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒ # 1 · (# 1 · (# 1 · (# 1 · # 0)))
  ∎
\end{code}

## Type rules

\begin{code}
data Permitted : Sort → Sort → Set where
  ** : Permitted * *
  *▢ : Permitted * ▢
  ▢* : Permitted ▢ *
  ▢▢ : Permitted ▢ ▢

infix  4  _⊢_⦂_
infix  4  _∋_⦂_
infixl 5  _,_

data Context : ℕ → Set where
  ∅   : Context zero
  _,_ : ∀ {n} → Context n → Term n → Context (suc n)

data _∋_⦂_ : ∀ {n} → Context n →  Var n → Term n → Set
data _⊢_⦂_ : ∀ {n} → Context n → Term n → Term n → Set

data _∋_⦂_  where

  Z[_] : ∀ {n} {Γ : Context n} {A : Term n} {s : Sort}
    → Γ ⊢ A ⦂ ⟪ s ⟫
      -----------------------
    → Γ , A ∋ Z ⦂ rename S_ A

  S[_]_ : ∀ {n} {Γ : Context n} {x : Var n} {A B : Term n} {s : Sort}
    → Γ ⊢ A ⦂ ⟪ s ⟫
    → Γ ∋ x ⦂ B
      -------------------------
    → Γ , A ∋ S x ⦂ rename S_ B

data _⊢_⦂_ where

  ⟪*⟫ : ∀ {n} {Γ : Context n}
      -----------------
    → Γ ⊢ ⟪ * ⟫ ⦂ ⟪ ▢ ⟫

  ⌊_⌋ : ∀ {n} {Γ : Context n} {x : Var n} {A : Term n}
    → Γ ∋ x ⦂ A
      -------------
    → Γ ⊢ ⌊ x ⌋ ⦂ A

  Π[_]_⇒_ : ∀ {n} {Γ : Context n} {A : Term n} {B : Term (suc n)} {s t : Sort}
    → Permitted s t
    → Γ ⊢ A ⦂ ⟪ s ⟫
    → Γ , A ⊢ B ⦂ ⟪ t ⟫
      -------------------
    → Γ ⊢ Π A ⇒ B ⦂ ⟪ t ⟫

  ƛ[_]_⇒_⦂_ : ∀ {n} {Γ : Context n} {A : Term n} {N B : Term (suc n)} {s t : Sort}
    → Permitted s t
    → Γ ⊢ A ⦂ ⟪ s ⟫
    → Γ , A ⊢ N ⦂ B
    → Γ , A ⊢ B ⦂ ⟪ t ⟫
      ---------------------
    → Γ ⊢ ƛ A ⇒ N ⦂ Π A ⇒ B

  _·_ : ∀ {n} {Γ : Context n} {L M A : Term n} {B : Term (suc n)}
    → Γ ⊢ L ⦂ Π A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------------
    → Γ ⊢ L · M ⦂ B [ M ]

  Eq : ∀ {n} {Γ : Context n} {M A B : Term n}
    → Γ ⊢ M ⦂ A
    → A =β B
      ---------
    → Γ ⊢ M ⦂ B
\end{code}

## Rename

\begin{code}
⊢extr : ∀ {m n} {Γ : Context m} {Δ : Context n}
  → (ρ : Var m → Var n)
  → (∀ {w : Var m} {B : Term m} → Γ ∋ w ⦂ B → Δ ∋ ρ w ⦂ rename ρ B)
    ---------------------------------------------------------------
  → (∀ {w : Var (suc m)} {A : Term m} {B : Term (suc m)}
      → Γ , A ∋ w ⦂ B → Δ , rename ρ A ∋ extr ρ w ⦂ rename (extr ρ) B)

⊢rename : ∀ {m n} {Γ : Context m} {Δ : Context n}
  → (ρ : Var m → Var n)
  → (∀ {w : Var m} {B : Term m} → Γ ∋ w ⦂ B → Δ ∋ ρ w ⦂ rename ρ B)
    ------------------------------------------------------
  → (∀ {w : Var m} {M A : Term m}
      → Γ ⊢ M ⦂ A → Δ ⊢ rename ρ M ⦂ rename ρ A)

⊢extr ρ ⊢ρ Z[ ⊢A ]       =  Z[ ⊢rename ρ ⊢ρ ⊢A ]
⊢extr ρ ⊢ρ (S[ ⊢A ] ∋w)  =  S[ ⊢rename ρ ⊢ρ ⊢A ] (ρ ∋w)

⊢rename = {!!}
{-
⊢rename σ (Ax ∋w)         =  Ax (σ ∋w)
⊢rename σ (⇒-I ⊢N)        =  ⇒-I (⊢rename (⊢extr σ) ⊢N)
⊢rename σ (⇒-E ⊢L ⊢M)     =  ⇒-E (⊢rename σ ⊢L) (⊢rename σ ⊢M)
⊢rename σ ℕ-I₁            =  ℕ-I₁
⊢rename σ (ℕ-I₂ ⊢M)       =  ℕ-I₂ (⊢rename σ ⊢M)
⊢rename σ (ℕ-E ⊢L ⊢M ⊢N)  =  ℕ-E (⊢rename σ ⊢L) (⊢rename σ ⊢M) (⊢rename (⊢extr σ) ⊢N)
⊢rename σ (Fix ⊢M)        =  Fix (⊢rename (⊢extr σ) ⊢M)
-}
\end{code}


## Weakening

\begin{code}
{-
weak : ∀ {n} {Γ : Context n} {M : Term n} {A B : Term n} {s : Sort}
  → Γ ⊢ A ⦂ ⟪ s ⟫
  → Γ ⊢ M ⦂ B
    ---------------------------------
  → Γ , A ⊢ rename S_ M ⦂ rename S_ B
weak ⊢C ⟪*⟫ = ⟪*⟫
weak ⊢C ⌊ ∋x ⌋ =  ⌊ S[ ⊢C ] ∋x ⌋
weak ⊢C (Π[ st ] ⊢A ⇒ ⊢B) = {! Π[ st ] weak ⊢A ⇒ weak ⊢B!}
weak ⊢C (ƛ[ x ] ⊢M ⇒ ⊢M₁ ⦂ ⊢M₂) = {!!}
weak ⊢C (⊢M · ⊢M₁) = {!!}
weak ⊢C (Eq ⊢M x) = {!!}
-}
\end{code}


## Substitution in type derivations

\begin{code}
{-
exts : ∀ {m n} → (Var m → Term n) → (Var (suc m) → Term (suc n))
exts ρ Z      =  ⌊ Z ⌋
exts ρ (S k)  =  rename S_ (ρ k)

subst : ∀ {m n} → (Var m → Term n) → (Term m → Term n)
subst σ ⟪ s ⟫      =  ⟪ s ⟫
subst σ ⌊ k ⌋      =  σ k
subst σ (Π A ⇒ B)  =  Π subst σ A ⇒ subst (exts σ) B
subst σ (ƛ A ⇒ N)  =  ƛ subst σ A ⇒ subst (exts σ) N
subst σ (L · M)    =  subst σ L · subst σ M

_[_] : ∀ {n} → Term (suc n) → Term n → Term n
_[_] {n} N M  =  subst {suc n} {n} σ N
  where
  σ : Var (suc n) → Term n
  σ Z      =  M
  σ (S k)  =  ⌊ k ⌋
-}
\end{code}

## Test examples are well-typed

\begin{code}
{-
_⊢⇒_ : ∀ {n} {Γ : Context n} {A B : Term n}
         → Γ ⊢ A ⦂ ⟪ * ⟫ → Γ ⊢ B ⦂ ⟪ * ⟫ → Γ ⊢ A ⇒ B ⦂ ⟪ * ⟫
⊢A ⊢⇒ ⊢B  =  Π[ ** ] ⊢A ⇒ rename S_ ⊢B
-}

-- ⊢Ch : ∅ ⊢ Ch ⦂ ⟪ * ⟫
-- ⊢Ch = Π[ ** ] ⟪ * ⟫ ⇒ Π[ ** ] ⌊ Z ⌋
-- Ch = Π ⟪ * ⟫ ⇒ ((# 0 ⇒ # 0) ⇒ # 0 ⇒ # 0)
-- Ch = Π X ⦂ * ⇒ (X ⇒ X) ⇒ X ⇒ X

{-
two : ∀ {n} → Term n
two = ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒ # 1 · (# 1 · # 0)
-- two = ƛ X ⦂ * ⇒ ƛ s ⦂ (X ⇒ X) ⇒ ƛ z ⦂ X ⇒ s · (s · z)

four : ∀ {n} → Term n
four = ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒ # 1 · (# 1 · (# 1 · (# 1 · # 0)))
-- four = ƛ X ⦂ * ⇒ ƛ s ⦂ (X ⇒ X) ⇒ ƛ z ⦂ X ⇒ s · (s · (s · (s · z)))

plus : ∀ {n} → Term n
plus = ƛ Ch ⇒ ƛ Ch ⇒ ƛ ⟪ * ⟫ ⇒ ƛ (# 0 ⇒ # 0) ⇒ ƛ # 1 ⇒
         (# 4 · # 2 · # 1 · (# 3 · # 2 · # 1 · # 0))
-- plus = ƛ m ⦂ Ch ⇒ ƛ n ⦂ Ch ⇒ ƛ X ⦂ * ⇒ ƛ s ⦂ (X ⇒ X) ⇒ ƛ z ⦂ X ⇒
--          m X s (n X s z)
-}
\end{code}




## Progress

\begin{code}
{-
data Progress {n} (M : Term n) : Set where

  step : ∀ {N : Term n}
    → M ⟶ N
      ----------
    → Progress M

  done :
      Normal M
      ----------
    → Progress M

progress : ∀ {n} → (M : Term n) → Progress M
progress ⌊ x ⌋                                 =  done ⌈ ⌊ x ⌋ ⌉
progress (ƛ N)  with  progress N
... | step N⟶N′                              =  step (ζ N⟶N′)
... | done Nⁿ                                  =  done (ƛ Nⁿ)
progress (⌊ x ⌋ · M) with progress M
... | step M⟶M′                              =  step (ξ₂ ⌊ x ⌋ M⟶M′)
... | done Mⁿ                                  =  done ⌈ ⌊ x ⌋ · Mⁿ ⌉
progress ((ƛ N) · M)                           =  step β
progress (L@(_ · _) · M) with progress L
... | step L⟶L′                              =  step (ξ₁ tt L⟶L′)
... | done ⌈ Lᵘ ⌉ with progress M
...    | step M⟶M′                           =  step (ξ₂ Lᵘ M⟶M′)
...    | done Mⁿ                               =  done ⌈ Lᵘ · Mⁿ ⌉
-}
\end{code}


## Normalise

\begin{code}
{-
Gas : Set
Gas = ℕ

data Normalise {n} (M : Term n) : Set where

  out-of-gas : ∀ {N : Term n}
    → M ⟶* N
      -------------
    → Normalise M

  normal : ∀ {N : Term n}
    → Gas
    → M ⟶* N
    → Normal N
     --------------
    → Normalise M

normalise : ∀ {n}
  → Gas
  → ∀ (M : Term n)
    -------------
  → Normalise M
normalise zero L                         =  out-of-gas (L ∎)
normalise (suc g) L with progress L
... | done Lⁿ                            =  normal (suc g) (L ∎) Lⁿ
... | step {M} L⟶M with normalise g M
...     | out-of-gas M⟶*N              =  out-of-gas (L ⟶⟨ L⟶M ⟩ M⟶*N)
...     | normal g′ M⟶*N Nⁿ            =  normal g′ (L ⟶⟨ L⟶M ⟩ M⟶*N) Nⁿ
-}
\end{code}
