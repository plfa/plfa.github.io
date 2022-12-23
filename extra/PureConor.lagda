---
title     : "Pure: Pure Type Systems"
permalink : /Pure/
---

Barendregt, H. (1991). Introduction to generalized type
systems. Journal of Functional Programming, 1(2),
125-154. doi:10.1017/S0956796800020025

Attempt to create inherently typed terms with Connor.

Phil and Conor's work on 24 Aug:
  Tried to define thinning, Γ ⊆ Δ, and got our knickers in a twist.
  Tried to define Wk directly on terms, as in Barendregt
  We need to push weaking through Π, but this requires weaking
    the slot one from the top, rather than the top slot
  Next idea: try weaking at arbitrary position n
  Also, make type weakened on explicit, to catch more errors

## Imports

\begin{code}
module PureConor where
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

\begin{code}
infix   4  _⊢_
infix   4  _∋_
infix   4  _⊆_
infixl  5  _,_
infixl  6  _/_  _∋/_  _⊢/_  _[_]  _⟨_⟩
infix   6  ƛ_⇒_
infix   7  Π_⇒_
-- infixr  8  _⇒_
infixl  9  _·_
infix  20  _W  _S

data Sort : Set where
  * : Sort
  ▢ : Sort

ok2 : Sort → Sort → Set
ok2 * ▢  =  ⊤
ok2 _ _  =  ⊥

ok3 : Sort → Sort → Sort → Set
ok3 * * ▢  =  ⊤
ok3 * ▢ ▢  =  ⊤
ok3 ▢ * *  =  ⊤
ok3 ▢ ▢ ▢  =  ⊤
ok3 _ _ _  =  ⊥

data Ctx : Set

data Tp : ∀ (Γ : Ctx) → Set
data _⊢_ : ∀ (Γ : Ctx) → Tp Γ → Set

data _—→_ {Γ : Ctx} {A : Tp Γ} : Γ ⊢ A → Γ ⊢ A → Set
data _=β_ {Γ : Ctx} {A : Tp Γ} : Γ ⊢ A → Γ ⊢ A → Set

data Ctx where

  ∅ :
      ---
      Ctx

  _,_ :
      (Γ : Ctx)
    → (A : Tp Γ)
      -----------
    → Ctx

data Tp where

  ⟪_⟫ : ∀ {Γ : Ctx}
    → Sort
      ----
    → Tp Γ

  ⌈_⌉ : ∀ {Γ : Ctx} {s : Sort}
    → Γ ⊢ ⟪ s ⟫
      ----------
    → Tp Γ

wk : ∀ {Γ : Ctx} {A : Tp Γ}
    → Tp Γ
      -----------
    → Tp (Γ , A)

_[_] : ∀ {Γ : Ctx} {A : Tp Γ}
  → (B : Tp (Γ , A))
  → (M : Γ ⊢ A)
    ----------------
  → Tp Γ

_⟨_⟩ : ∀ {Γ : Ctx} {A : Tp Γ} {B : Tp (Γ , A)}
  → (N : Γ , A ⊢ B)
  → (M : Γ ⊢ A)
    ---------------
  → Γ ⊢ B [ M ]

data _⊢_ where

  ⟪_⟫ : ∀ {Γ : Ctx} {t : Sort}
    → (s : Sort)
    → {st : ok2 s t}
      -------------
    → Γ ⊢ ⟪ t ⟫

  St : ∀ {Γ : Ctx} {A : Tp Γ}
      ------------
    → Γ , A ⊢ wk A

  Wk : ∀ {Γ : Ctx} {A B : Tp Γ}
    → Γ ⊢ A
      ------------
    → Γ , B ⊢ wk A

  Π_⇒_ : ∀ {Γ : Ctx} {s t u : Sort} {stu : ok3 s t u}
    → (A : Γ ⊢ ⟪ s ⟫)
    → Γ , ⌈ A ⌉ ⊢ ⟪ t ⟫
      ------------------
    → Γ ⊢ ⟪ u ⟫

  ƛ_⇒_ : ∀ {Γ : Ctx} {s t u : Sort} {stu : ok3 s t u}
    → (A : Γ ⊢ ⟪ s ⟫)
    → {B : Γ , ⌈ A ⌉ ⊢ ⟪ t ⟫}
    → Γ , ⌈ A ⌉ ⊢ ⌈ B ⌉
      -------------------------------------
    → Γ ⊢ ⌈ Π_⇒_ {u = u} {stu = stu} A B ⌉

  _·_ : ∀ {Γ : Ctx} {s t u : Sort} {stu : ok3 s t u}
    → {A : Γ ⊢ ⟪ s ⟫}
    → {B : Γ , ⌈ A ⌉ ⊢ ⟪ t ⟫}
    → (L : Γ ⊢ ⌈ Π_⇒_ {u = u} {stu = stu} A B ⌉)
    → (M : Γ ⊢ ⌈ A ⌉)
      ------------------------------------------
    → Γ ⊢ ⌈ B ⌉ [ M ]

  Cnv : ∀ {Γ : Ctx} {s : Sort} {A B : Γ ⊢ ⟪ s ⟫}
    → Γ ⊢ ⌈ A ⌉
    → A =β B
      ---------
    → Γ ⊢ ⌈ B ⌉

wk ⟪ s ⟫ =  ⟪ s ⟫
wk ⌈ A ⌉ =  ⌈ Wk A ⌉

_[_] = {!!}

_⟨_⟩ = {!!}

data _—→_ where

  -- this is bollocks! It weakens on A, not on an arbitrary type
  Wk-Π : ∀ {Γ : Ctx} {s t u : Sort} {stu : ok3 s t u}
    → (A : Γ ⊢ ⟪ s ⟫)
    → (B : Γ , ⌈ A ⌉ ⊢ ⟪ t ⟫)
      -----------------------------------------------------------
    → Wk (Π_⇒_ {stu = stu} A B) —→ Π_⇒_ {stu = stu} (Wk A) (Wk B)

data _=β_ where

  refl : ∀ {Γ : Ctx} {A : Tp Γ} {M : Γ ⊢ A}
    → M =β M

  tran : ∀ {Γ : Ctx} {A : Tp Γ} {L M N : Γ ⊢ A}
    → L =β M
    → M =β N
      ------
    → L =β N

  symm :  ∀ {Γ : Ctx} {A : Tp Γ} {L M : Γ ⊢ A}
    → L =β M
      ------
    → M =β L

  step : ∀ {Γ : Ctx} {A : Tp Γ} {L M : Γ ⊢ A}
    → L —→ M
      ------
    → L =β M
{-

data _⊆_ : Ctx → Ctx → Set

_/_ : ∀ {Γ Δ : Ctx} → Tp Γ → Γ ⊆ Δ → Tp Δ

_∋/_ : ∀ {Γ Δ : Ctx} {A : Tp Γ} → Γ ∋ A → (θ : Γ ⊆ Δ) → Δ ∋ A / θ

_⊢/_ : ∀ {Γ Δ : Ctx} {A : Tp Γ} → Γ ⊢ A → (θ : Γ ⊆ Δ) → Δ ⊢ A / θ

data _∋_ where

  Z : ∀ {Γ : Ctx} {A : Tp Γ}
      ----------------------
    → Γ , A ∋ A / I W

  _S : ∀ {Γ : Ctx} {A B : Tp Γ}
    → Γ ∋ A
      ----------------
    → Γ , B ∋ A / I W

data _⊆_ where

  I : ∀ {Γ : Ctx}
      -----
    → Γ ⊆ Γ

  _W : ∀ {Γ Δ : Ctx} {A : Tp Δ}
    → Γ ⊆ Δ
      -----------
    → Γ ⊆ (Δ , A)

  _S : ∀ {Γ Δ : Ctx} {B : Tp Γ}
    → (θ : Γ ⊆ Δ)
      -----------------------
    → (Γ , B) ⊆ (Δ , (B / θ))

_-_ : ∀ {Γ Δ Θ : Ctx} → Γ ⊆ Δ → Δ ⊆ Θ → Γ ⊆ Θ

lemma : ∀ {Γ Δ Θ : Ctx} (A : Tp Γ)
  → (θ : Γ ⊆ Δ)
  → (φ : Δ ⊆ Θ)
    -----------------------
  → A / θ / φ ≡ A / (θ - φ)

θ - I = θ
θ - (φ W) = (θ - φ) W
I - (φ S) = φ S
(θ W) - (φ S) = (θ - φ) W
_S {B = B} θ - (φ S) rewrite lemma B θ φ  = (θ - φ) S

lemma = {!!}

-- lemma A θ I = refl
-- lemma A θ (φ W) = {!!}
-- lemma A θ (φ S) = {!!}



wk : ∀ {Γ : Ctx} (B : Tp Γ) → Γ ⊆ Γ , B
wk B = I W

⟪ s ⟫ / θ  =  ⟪ s ⟫
⌈ A ⌉ / θ  =  ⌈ A ⊢/ θ ⌉

-- lemma : ∀ {Γ Δ : Ctx} (θ : Γ ⊆ Δ) (A B : Tp Γ)
--  → A / wk B / θ S ≡ A / θ / wk (B / θ)
-- lemma = {!!}

x ∋/ I = {!!}
x ∋/ θ W = {! x ∋/ θ!}
x ∋/ θ S = {!!}


thin-· : ∀ {Γ Δ : Ctx} {A : Tp Γ} (B : Tp (Γ , A)) (M : Γ ⊢ A) (θ : Γ ⊆ Δ)
  → B [ M ] / θ ≡ B / θ S [ M ⊢/ θ ]

⟪ s ⟫ {st} ⊢/ θ =  ⟪ s ⟫ {st}
⌊ x ⌋ ⊢/ θ = ⌊ x ∋/ θ ⌋
Π_⇒_ {stu = stu} A B ⊢/ θ =  Π_⇒_ {stu = stu} (A ⊢/ θ) (B ⊢/ θ S)
ƛ_⇒_ {stu = stu} A N ⊢/ θ = ƛ_⇒_ {stu = stu} (A ⊢/ θ) (N ⊢/ θ S)
_·_ {stu = stu} {B = B} L M ⊢/ θ rewrite thin-· ⌈ B ⌉ M θ
  =  _·_ {stu = stu} (L ⊢/ θ) (M ⊢/ θ)

thin-· = {!!}

_[_]  =  {!!}

_⟨_⟩  =  {!!}

-}

{-
A / I        =  {!!} -- A
⟪ s ⟫ / θ S  =  ⟪ s ⟫
⟪ s ⟫ / θ W  =  ⟪ s ⟫
⌈ A ⌉ / θ S  =  ⌈ A ⊢/ (θ S) ⌉
⌈ A ⌉ / θ W  =  ⌈ A ⊢/ (θ W) ⌉
-}

{-
I /∋ x = x
θ W /∋ x =  {! θ /∋ x!}
_S {B = B} θ /∋ Z rewrite lemma θ B B  =  Z
θ S /∋ x S = {!!}
∅ /∋ Z = Z
W θ /∋ x = {!S (θ / x)!}
S θ /∋ (S x) = {!S (θ / x)!}
-}
\end{code}
