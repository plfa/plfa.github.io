## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
\end{code}

Tiny lambda calculus
\begin{code}
module Source where

  infix  4 _⊢_
  infix  4 _∋_
  infixl 5 _,_
  infix  5 ƛ_
  infixr 7 _⇒_
  infixl 7 _·_
  infix  9 `_
  infix  9 S_

  data Type : Set where
    _⇒_ : Type → Type → Type
    o   : Type

  data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context

  data _∋_ : Context → Type → Set where

    Z : ∀ {Γ A}
        ----------
      → Γ , A ∋ A

    S_ : ∀ {Γ A B}
      → Γ ∋ A
        ---------
      → Γ , B ∋ A

  data _⊢_ : Context → Type → Set where

    `_ : ∀ {Γ} {A}
      → Γ ∋ A
        ------
      → Γ ⊢ A

    ƛ_  :  ∀ {Γ} {A B}
      → Γ , A ⊢ B
        ----------
      → Γ ⊢ A ⇒ B

    _·_ : ∀ {Γ} {A B}
      → Γ ⊢ A ⇒ B
      → Γ ⊢ A
        ----------
      → Γ ⊢ B

  ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
      ----------------------------------
    → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
  ext ρ Z      =  Z
  ext ρ (S x)  =  S (ρ x)

  rename : ∀ {Γ Δ}
    → (∀ {A} → Γ ∋ A → Δ ∋ A)
      ------------------------
    → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
  rename ρ (` x)          =  ` (ρ x)
  rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
  rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)

  exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
      ----------------------------------
    → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
  exts σ Z      =  ` Z
  exts σ (S x)  =  rename S_ (σ x)

  subst : ∀ {Γ Δ}
    → (∀ {A} → Γ ∋ A → Δ ⊢ A)
      ------------------------
    → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
  subst σ (` k)          =  σ k
  subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
  subst σ (L · M)        =  (subst σ L) · (subst σ M)

  _[_] : ∀ {Γ A B}
          → Γ , B ⊢ A
          → Γ ⊢ B
            ---------
          → Γ ⊢ A
  _[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
    where
    σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
    σ Z      =  M
    σ (S x)  =  ` x

  data Value : ∀ {Γ A} → Γ ⊢ A → Set where

    V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
        ---------------------------
      → Value (ƛ N)

  infix 2 _—→_

  data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

    ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
      → L —→ L′
        -----------------
      → L · M —→ L′ · M

    ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
      → Value V
      → M —→ M′
        --------------
      → V · M —→ V · M′

    β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
      → Value W
        -------------------
      → (ƛ N) · W —→ N [ W ]

  infix  2 _—↠_
  infix 1 begin_
  infixr 2 _—→⟨_⟩_
  infix 3 _∎

  data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

    _∎ : ∀ {Γ A} (M : Γ ⊢ A)
        --------
      → M —↠ M

    _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
      → L —→ M
      → M —↠ N
        ---------
      → L —↠ N

  begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A} → (M —↠ N) → (M —↠ N)
  begin M—↠N = M—↠N
\end{code}
