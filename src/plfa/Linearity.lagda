---
title     : "Linearity: Introduction to the Linear Lambda Calculus"
layout    : page
permalink : /Linearity/
---

\begin{code}
module plfa.Linearity where
\end{code}

\begin{code}
open import plfa.Mult
open import Function using (_∘_)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)
\end{code}

\begin{code}
infix  1 _⊢₁_∋_
infix  1 _⊢_
infix  1 _∋_
infixl 5 _,_
infixl 5 _,_∙_
infixr 6 [_∙_]⊸_
infixr 7 _⋈_
infixl 8 _**_
infix  9 _⊛_
\end{code}

\begin{code}
data Type : Set where
  [_∙_]⊸_ : Mult → Type → Type → Type
  `0      : Type
\end{code}

\begin{code}
data Precontext : Set where
  ∅   : Precontext
  _,_ : Precontext → Type → Precontext
\end{code}

\begin{code}
_ : Precontext
_ = ∅ , [ 1# ∙ `0 ]⊸ `0 , `0
\end{code}

\begin{code}
data _∋_ : Precontext → Type → Set where

  Z  : ∀ {γ} {A}

       ---------
     → γ , A ∋ A

  S_ : ∀ {γ} {A B}

     → γ ∋ A
       ---------
     → γ , B ∋ A
\end{code}

\begin{code}
data _⊢_ : Precontext → Type → Set where

  `_  : ∀ {γ} {A}

      → γ ∋ A
        -----
      → γ ⊢ A

  ƛ_  : ∀ {γ} {A B} {π}

      → γ , A ⊢ B
        ----------------
      → γ ⊢ [ π ∙ A ]⊸ B

  _·_ : ∀ {γ} {A B} {π}

      → γ ⊢ [ π ∙ A ]⊸ B
      → γ ⊢ A
        ----------------
      → γ ⊢ B
\end{code}

\begin{code}
ext : ∀ {Γ Δ}

  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)

ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
\end{code}

\begin{code}
rename : ∀ {Γ Δ}

  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)

rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
\end{code}

\begin{code}
exts : ∀ {Γ Δ}

  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)

exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)
\end{code}

\begin{code}
subst : ∀ {Γ Δ}

  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)

subst σ (` k)    =  σ k
subst σ (ƛ N)    =  ƛ (subst (exts σ) N)
subst σ (L · M)  =  (subst σ L) · (subst σ M)
\end{code}

\begin{code}
data Context : Precontext → Set where
  ∅     : Context ∅
  _,_∙_ : ∀ {Γ} → Context Γ → Mult → (A : Type) → Context (Γ , A)
\end{code}

\begin{code}
_ : Context (∅ , [ 1# ∙ `0 ]⊸ `0 , `0)
_ = ∅ , 1# ∙ [ 1# ∙ `0 ]⊸ `0 , 0# ∙ `0
\end{code}

Scaling.

\begin{code}
_**_ : ∀ {γ} → Mult → Context γ → Context γ
π ** ∅ = ∅
π ** (Γ , ρ ∙ A) = π ** Γ , π * ρ ∙ A
\end{code}

Unit scaling does nothing.

\begin{code}
**-identityˡ : ∀ {γ} (Γ : Context γ)

  -------------
  → 1# ** Γ ≡ Γ

**-identityˡ ∅ = refl
**-identityˡ (Γ , π ∙ A) rewrite **-identityˡ Γ = refl
\end{code}

Scaling by a product is the composition of scalings.

\begin{code}
**-assoc : ∀ {γ} (Γ : Context γ) {π π′}

  --------------------------------
  → (π * π′) ** Γ ≡ π ** (π′ ** Γ)

**-assoc ∅ = refl
**-assoc (Γ , π″ ∙ A) {π} {π′} =
  begin
    (π * π′) ** Γ , (π * π′) * π″ ∙ A
  ≡⟨ cong ((π * π′) ** Γ ,_∙ A) (*-assoc π π′ π″) ⟩
    (π * π′) ** Γ , π * (π′ * π″) ∙ A
  ≡⟨ cong (_, π * (π′ * π″) ∙ A) (**-assoc Γ) ⟩
    π ** (π′ ** Γ) , π * (π′ * π″) ∙ A
  ∎
\end{code}

The 0-vector.

\begin{code}
0s : ∀ {γ} → Context γ
0s {∅}     = ∅
0s {γ , A} = 0s , 0# ∙ A
\end{code}

Scaling the 0-vector gives the 0-vector.

\begin{code}
**-zeroʳ : ∀ γ π

  --------------------
  → 0s {γ} ≡ π ** 0s

**-zeroʳ ∅ π = refl
**-zeroʳ (γ , A) π =
  begin
    0s , 0# ∙ A
  ≡⟨ cong (0s ,_∙ A) (sym (*-zeroʳ π)) ⟩
    0s , π * 0# ∙ A
  ≡⟨ cong (_, π * 0# ∙ A) (**-zeroʳ γ π) ⟩
    π ** 0s , π * 0# ∙ A
  ∎
\end{code}

Scaling by 0 gives the 0-vector.

\begin{code}
**-zeroˡ : ∀ {γ} (Γ : Context γ)

  -----------------
  → 0# ** Γ ≡ 0s

**-zeroˡ ∅ = refl
**-zeroˡ (Γ , π ∙ A) rewrite **-zeroˡ Γ = refl
\end{code}

Vector addition.

\begin{code}
_⋈_ : ∀ {γ} → Context γ → Context γ → Context γ
∅ ⋈ ∅ = ∅
(Γ₁ , π₁ ∙ A) ⋈ (Γ₂ , π₂ ∙ .A) = Γ₁ ⋈ Γ₂ , π₁ + π₂ ∙ A
\end{code}

Adding the 0-vector does nothing.

\begin{code}
⋈-identityˡ : ∀ {γ} (Γ : Context γ)

  ---------------
  → 0s ⋈ Γ ≡ Γ

⋈-identityˡ ∅ = refl
⋈-identityˡ (Γ , π ∙ A) rewrite ⋈-identityˡ Γ | +-identityʳ π = refl
\end{code}

\begin{code}
⋈-identityʳ : ∀ {γ} (Γ : Context γ)

  ---------------
  → Γ ⋈ 0s ≡ Γ

⋈-identityʳ ∅ = refl
⋈-identityʳ (Γ , π ∙ A) rewrite ⋈-identityʳ Γ | +-identityʳ π = refl
\end{code}

Vector addition is commutative.

\begin{code}
⋈-comm : ∀ {γ} (Γ₁ Γ₂ : Context γ)

  ---------------------
  → Γ₁ ⋈ Γ₂ ≡ Γ₂ ⋈ Γ₁

⋈-comm ∅ ∅ = refl
⋈-comm (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) =
  begin
    Γ₁ ⋈ Γ₂ , π₁ + π₂ ∙ A
  ≡⟨ cong (Γ₁ ⋈ Γ₂ ,_∙ A) (+-comm π₁ π₂) ⟩
    Γ₁ ⋈ Γ₂ , π₂ + π₁ ∙ A
  ≡⟨ cong (_, π₂ + π₁ ∙ A) (⋈-comm Γ₁ Γ₂) ⟩
    Γ₂ ⋈ Γ₁ , π₂ + π₁ ∙ A
  ∎
\end{code}

Vector addition is associative.

\begin{code}
⋈-assoc : ∀ {γ} (Γ₁ Γ₂ Γ₃ : Context γ)

  -------------------------------------
  → (Γ₁ ⋈ Γ₂) ⋈ Γ₃ ≡ Γ₁ ⋈ (Γ₂ ⋈ Γ₃)

⋈-assoc ∅ ∅ ∅ = refl
⋈-assoc (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) (Γ₃ , π₃ ∙ .A) =
  begin
    (Γ₁ ⋈ Γ₂) ⋈ Γ₃ , (π₁ + π₂) + π₃ ∙ A
  ≡⟨ cong ((Γ₁ ⋈ Γ₂) ⋈ Γ₃ ,_∙ A) (+-assoc π₁ π₂ π₃) ⟩
    (Γ₁ ⋈ Γ₂) ⋈ Γ₃ , π₁ + (π₂ + π₃) ∙ A
  ≡⟨ cong (_, π₁ + (π₂ + π₃) ∙ A) (⋈-assoc Γ₁ Γ₂ Γ₃) ⟩
    Γ₁ ⋈ (Γ₂ ⋈ Γ₃) , π₁ + (π₂ + π₃) ∙ A
  ∎
\end{code}

Scaling by a sum gives the sum of the scalings.

\begin{code}
**-distribʳ-⋈ : ∀ {γ} (Γ : Context γ) π₁ π₂

  -----------------------------------
  → π₁ + π₂ ** Γ ≡ π₁ ** Γ ⋈ π₂ ** Γ

**-distribʳ-⋈ ∅ π₁ π₂ = refl
**-distribʳ-⋈ (Γ , π ∙ A) π₁ π₂ =
  begin
    (π₁ + π₂) ** Γ , (π₁ + π₂) * π ∙ A
  ≡⟨ cong ((π₁ + π₂) ** Γ ,_∙ A) (*-distribʳ-+ π π₁ π₂) ⟩
    (π₁ + π₂) ** Γ , (π₁ * π) + (π₂ * π) ∙ A
  ≡⟨ cong (_, (π₁ * π) + (π₂ * π) ∙ A) (**-distribʳ-⋈ Γ π₁ π₂) ⟩
    π₁ ** Γ ⋈ π₂ ** Γ , (π₁ * π) + (π₂ * π) ∙ A
  ∎
\end{code}

Scaling a sum gives the sum of the scalings.

\begin{code}
**-distribˡ-⋈ : ∀ {γ} (Γ₁ Γ₂ : Context γ) {π}

  --------------------------------------
  → π ** (Γ₁ ⋈ Γ₂) ≡ π ** Γ₁ ⋈ π ** Γ₂

**-distribˡ-⋈ ∅ ∅ = refl
**-distribˡ-⋈ (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) {π} =
  begin
    π ** (Γ₁ ⋈ Γ₂) , π * (π₁ + π₂) ∙ A
  ≡⟨ cong (π ** (Γ₁ ⋈ Γ₂) ,_∙ A) (*-distribˡ-+ π π₁ π₂) ⟩
    π ** (Γ₁ ⋈ Γ₂) , (π * π₁) + (π * π₂) ∙ A
  ≡⟨ cong (_, (π * π₁) + (π * π₂) ∙ A) (**-distribˡ-⋈ Γ₁ Γ₂) ⟩
    π ** Γ₁ ⋈ π ** Γ₂ , (π * π₁) + (π * π₂) ∙ A
  ∎
\end{code}

The identity matrix.

\begin{code}
identity : ∀ {A} {γ : Precontext} → γ ∋ A → Context γ
identity {γ = γ , A} Z     = 0s , 1# ∙ A
identity {γ = γ , B} (S x) = identity x , 0# ∙ B
\end{code}

Matrix-vector multiplication ΔᵀΓ.

\begin{code}
_⊛_ : ∀ {γ δ}

  → (Γ : Context γ)
  → (Δ : ∀ {A} → γ ∋ A → Context δ)
  → Context δ

∅           ⊛ Δ = 0s
(Γ , π ∙ A) ⊛ Δ = (π ** Δ Z) ⋈ Γ ⊛ (Δ ∘ S_)
\end{code}

Linear maps preserve the 0-vector.

\begin{code}
⊛-zeroˡ : ∀ {γ δ}

  → (Δ : ∀ {A} → (γ ∋ A → Context δ))
  -----------------------------------
  → 0s ⊛ Δ ≡ 0s

⊛-zeroˡ {∅}     {δ} Δ = refl
⊛-zeroˡ {γ , A} {δ} Δ =
  begin
    0s ⊛ Δ
  ≡⟨⟩
    0# ** Δ Z ⋈ 0s ⊛ (Δ ∘ S_)
  ≡⟨ cong (0# ** Δ Z ⋈_) (⊛-zeroˡ {γ} (Δ ∘ S_)) ⟩
    0# ** Δ Z ⋈ 0s
  ≡⟨ cong (_⋈ 0s) (**-zeroˡ (Δ Z)) ⟩
    0s ⋈ 0s
  ≡⟨ ⋈-identityʳ 0s ⟩
    0s
  ∎
\end{code}

Adding a row of 0s to the end of the matrix and then multiplying by a vector produces a vector with a 0 at the bottom.

\begin{code}
⊛-zeroʳ : ∀ {γ δ} (Γ : Context γ) {B}

  → (Δ : ∀ {A} → (γ ∋ A → Context δ))
  ---------------------------------------------------
  → Γ ⊛ (λ x → Δ x , 0# ∙ B) ≡ Γ ⊛ Δ , 0# ∙ B

⊛-zeroʳ {γ} {δ} ∅ {B} Δ = refl
⊛-zeroʳ {γ} {δ} (Γ , π ∙ C) {B} Δ =
  begin
    (π ** Δ Z , π * 0# ∙ B) ⋈ (Γ ⊛ (λ x → Δ (S x) , 0# ∙ B))
  ≡⟨ cong ((π ** Δ Z , π * 0# ∙ B) ⋈_) (⊛-zeroʳ Γ (Δ ∘ S_)) ⟩
    (π ** Δ Z , π * 0# ∙ B) ⋈ (Γ ⊛ (λ x → Δ (S x)) , 0# ∙ B)
  ≡⟨⟩
    (π ** Δ Z , π * 0# ∙ B) ⋈ (Γ ⊛ (Δ ∘ S_) , 0# ∙ B)
  ≡⟨⟩
    (π ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_)) , (π * 0#) + 0# ∙ B
  ≡⟨ cong ((π ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_)) ,_∙ B) (+-identityʳ (π * 0#)) ⟩
    (π ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_)) , π * 0# ∙ B
  ≡⟨ cong ((π ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_)) ,_∙ B) (*-zeroʳ π) ⟩
    (π ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_)) , 0# ∙ B
  ∎
\end{code}

Linear maps preserve scaling.

\begin{code}
⊛-preserves-** : ∀ {γ δ} (Γ : Context γ) {π}

  → (Δ : ∀ {A} → γ ∋ A → Context δ)
  -----------------------------------
  → (π ** Γ) ⊛ Δ ≡ π ** (Γ ⊛ Δ)

⊛-preserves-** {γ} {δ} ∅ {π} Δ =
  begin
    0s
  ≡⟨ **-zeroʳ δ π ⟩
    π ** 0s
  ∎

⊛-preserves-** {γ} {δ} (Γ , π′ ∙ A) {π} Δ =
  begin
    ((π * π′) ** Δ Z) ⋈ ((π ** Γ) ⊛ (Δ ∘ S_))
  ≡⟨ cong ((π * π′) ** Δ Z ⋈_) (⊛-preserves-** Γ (Δ ∘ S_)) ⟩
    ((π * π′) ** Δ Z) ⋈ (π ** (Γ ⊛ (Δ ∘ S_)))
  ≡⟨ cong (_⋈ (π ** (Γ ⊛ (Δ ∘ S_)))) (**-assoc (Δ Z)) ⟩
    (π ** (π′ ** Δ Z)) ⋈ (π ** (Γ ⊛ (Δ ∘ S_)))
  ≡⟨ sym (**-distribˡ-⋈ (π′ ** Δ Z) (Γ ⊛ (Δ ∘ S_))) ⟩
    π ** (π′ ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_))
  ∎
\end{code}

Linear maps distribute over sums.

\begin{code}
⊛-distribʳ-⋈ : ∀ {γ} {δ} (Γ₁ Γ₂ : Context γ)

  → (Δ : ∀ {A} → γ ∋ A → Context δ)
  -----------------------------------------------
  → (Γ₁ ⋈ Γ₂) ⊛ Δ ≡ Γ₁ ⊛ Δ ⋈ Γ₂ ⊛ Δ

⊛-distribʳ-⋈ ∅ ∅ Δ =
  begin
    0s
  ≡⟨ sym (⋈-identityʳ 0s) ⟩
    0s ⋈ 0s
  ∎

⊛-distribʳ-⋈ (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) Δ =
  begin
    (π₁ + π₂) ** Δ Z ⋈ (Γ₁ ⋈ Γ₂) ⊛ (Δ ∘ S_)
  ≡⟨ cong ((π₁ + π₂) ** Δ Z ⋈_) (⊛-distribʳ-⋈ Γ₁ Γ₂ (Δ ∘ S_)) ⟩
    (π₁ + π₂) ** Δ Z ⋈ (Γ₁ ⊛ (Δ ∘ S_) ⋈ Γ₂ ⊛ (Δ ∘ S_))
  ≡⟨ cong (_⋈ Γ₁ ⊛ (Δ ∘ S_) ⋈ Γ₂ ⊛ (Δ ∘ S_)) (**-distribʳ-⋈ (Δ Z) π₁ π₂) ⟩
    (π₁ ** Δ Z ⋈ π₂ ** Δ Z) ⋈ (Γ₁ ⊛ (Δ ∘ S_) ⋈ Γ₂ ⊛ (Δ ∘ S_))
  ≡⟨ sym (⋈-assoc (π₁ ** Δ Z ⋈ π₂ ** Δ Z) (Γ₁ ⊛ (Δ ∘ S_)) (Γ₂ ⊛ (Δ ∘ S_))) ⟩
    ((π₁ ** Δ Z ⋈ π₂ ** Δ Z) ⋈ Γ₁ ⊛ (Δ ∘ S_)) ⋈ Γ₂ ⊛ (Δ ∘ S_)
  ≡⟨ cong (_⋈ Γ₂ ⊛ (Δ ∘ S_)) (⋈-assoc (π₁ ** Δ Z) (π₂ ** Δ Z) (Γ₁ ⊛ (Δ ∘ S_))) ⟩
    (π₁ ** Δ Z ⋈ (π₂ ** Δ Z ⋈ Γ₁ ⊛ (Δ ∘ S_))) ⋈ Γ₂ ⊛ (Δ ∘ S_)
  ≡⟨ cong (_⋈ Γ₂ ⊛ (Δ ∘ S_)) (cong (π₁ ** Δ Z ⋈_) (⋈-comm (π₂ ** Δ Z) (Γ₁ ⊛ (Δ ∘ S_)))) ⟩
    (π₁ ** Δ Z ⋈ (Γ₁ ⊛ (Δ ∘ S_) ⋈ π₂ ** Δ Z)) ⋈ Γ₂ ⊛ (Δ ∘ S_)
  ≡⟨ cong (_⋈ Γ₂ ⊛ (Δ ∘ S_)) (sym (⋈-assoc (π₁ ** Δ Z) (Γ₁ ⊛ (Δ ∘ S_)) (π₂ ** Δ Z))) ⟩
    ((π₁ ** Δ Z ⋈ Γ₁ ⊛ (Δ ∘ S_)) ⋈ π₂ ** Δ Z) ⋈ Γ₂ ⊛ (Δ ∘ S_)
  ≡⟨ ⋈-assoc (π₁ ** Δ Z ⋈ Γ₁ ⊛ (Δ ∘ S_)) (π₂ ** Δ Z) (Γ₂ ⊛ (Δ ∘ S_)) ⟩
    (π₁ ** Δ Z ⋈ Γ₁ ⊛ (Δ ∘ S_)) ⋈ (π₂ ** Δ Z ⋈ Γ₂ ⊛ (Δ ∘ S_))
  ∎
\end{code}

Multiplying by a standard basis vector projects out the corresponding column of the matrix.

\begin{code}
⊛-identityˡ : ∀ {γ δ} {A}

  → (Δ : ∀ {A} → (γ ∋ A → Context δ))
  → (x : γ ∋ A)
  -----------------------------------
  → identity x ⊛ Δ ≡ Δ x

⊛-identityˡ {γ , A} {δ} {A} Δ Z =
  begin
    identity Z ⊛ Δ
  ≡⟨⟩
    1# ** Δ Z ⋈ 0s ⊛ (Δ ∘ S_)
  ≡⟨ cong ((1# ** Δ Z) ⋈_) (⊛-zeroˡ (Δ ∘ S_)) ⟩
    1# ** Δ Z ⋈ 0s
  ≡⟨ ⋈-identityʳ (1# ** Δ Z) ⟩
    1# ** Δ Z
  ≡⟨ **-identityˡ (Δ Z) ⟩
    Δ Z
  ∎

⊛-identityˡ {γ , B} {δ} {A} Δ (S x) =
  begin
    identity (S x) ⊛ Δ
  ≡⟨⟩
    0# ** Δ Z ⋈ identity x ⊛ (Δ ∘ S_)
  ≡⟨ cong (0# ** Δ Z ⋈_) (⊛-identityˡ (Δ ∘ S_) x) ⟩
    0# ** Δ Z ⋈ Δ (S x)
  ≡⟨ cong (_⋈ Δ (S x)) (**-zeroˡ (Δ Z)) ⟩
    0s ⋈ Δ (S x)
  ≡⟨ ⋈-identityˡ (Δ (S x)) ⟩
    Δ (S x)
  ∎
\end{code}

The standard basis vectors put together give the identity matrix.

\begin{code}
⊛-identityʳ : ∀ {γ} (Γ : Context γ)

  -------------------
  → Γ ⊛ identity ≡ Γ

⊛-identityʳ {γ} ∅ = refl
⊛-identityʳ {γ , .A} (Γ , π ∙ A) =
  begin
    (π ** 0s , π * 1# ∙ A) ⋈ (Γ ⊛ (λ x → identity x , 0# ∙ A))
  ≡⟨ cong ((π ** 0s , π * 1# ∙ A) ⋈_) (⊛-zeroʳ Γ identity) ⟩
    (π ** 0s , π * 1# ∙ A) ⋈ (Γ ⊛ identity , 0# ∙ A)
  ≡⟨ cong ((π ** 0s , π * 1# ∙ A) ⋈_) (cong (_, 0# ∙ A) (⊛-identityʳ Γ)) ⟩
    (π ** 0s , π * 1# ∙ A) ⋈ (Γ , 0# ∙ A)
  ≡⟨⟩
    π ** 0s ⋈ Γ , (π * 1#) + 0# ∙ A
  ≡⟨ cong ((π ** 0s ⋈ Γ) ,_∙ A) (+-identityʳ (π * 1#)) ⟩
    π ** 0s ⋈ Γ , π * 1# ∙ A
  ≡⟨ cong ((π ** 0s ⋈ Γ) ,_∙ A) (*-identityʳ π) ⟩
    π ** 0s ⋈ Γ , π ∙ A
  ≡⟨ cong (_, π ∙ A) (cong (_⋈ Γ) (sym (**-zeroʳ γ π))) ⟩
    0s ⋈ Γ , π ∙ A
  ≡⟨ cong (_, π ∙ A) (⋈-identityˡ Γ) ⟩
    Γ , π ∙ A
  ∎
\end{code}

\begin{code}
data _⊢₁_∋_ : ∀ {γ} (Γ : Context γ) (A : Type) (M : γ ⊢ A) → Set where

  `_  : ∀ {γ} {A}

      → (x : γ ∋ A)
        -----------
      → identity x ⊢₁ A ∋ (` x)

  ƛ_  : ∀ {γ} {Γ : Context γ} {A B} {π} {N}

      → (Γ , π ∙ A) ⊢₁ B ∋ N
      → Γ ⊢₁ [ π ∙ A ]⊸ B ∋ (ƛ N)

  _·_ : ∀ {γ} {Γ Δ : Context γ} {A B} {π} {L M}

      → Γ ⊢₁ [ π ∙ A ]⊸ B ∋ L
      → Δ ⊢₁ A ∋ M
      → Γ ⋈ π ** Δ ⊢₁ B ∋ (L · M)
\end{code}

We can do a change of basis (or, in this case, permutation of basis and introduction of 0-size dimensions) on the substitution matrix.

\begin{code}
rename′ : ∀ {γ δ} {Γ : Context γ} {B} {M}

  → (ρ : ∀ {A} → γ ∋ A → δ ∋ A)
  → Γ ⊢₁ B ∋ M
  -------------------------------
  → Γ ⊛ (identity ∘ ρ) ⊢₁ B ∋ rename ρ M

rename′ {δ = δ} ρ (`_ {γ} {B} x) =
  Eq.subst (_⊢₁ B ∋ (` ρ x)) lem (` ρ x)
  where
    lem =
      begin
        identity (ρ x)
      ≡⟨ sym (⊛-identityˡ (identity ∘ ρ) x) ⟩
        identity x ⊛ (identity ∘ ρ)
      ∎

rename′ {δ = δ} ρ (ƛ_ {γ} {Γ} {A} {B} {π} {N} ⊢N) =
  ƛ Eq.subst (_⊢₁ B ∋ rename (ext ρ) N) lem (rename′ (ext ρ) ⊢N)
  where
    lem =
      begin
        (π ** 0s , π * 1# ∙ A) ⋈ (Γ ⊛ (λ x → identity (ρ x) , 0# ∙ A))
      ≡⟨ cong ((π ** 0s , π * 1# ∙ A) ⋈_) (⊛-zeroʳ Γ (identity ∘ ρ)) ⟩
        (π ** 0s , π * 1# ∙ A) ⋈ (Γ ⊛ (identity ∘ ρ) , 0# ∙ A)
      ≡⟨⟩
        π ** 0s ⋈ Γ ⊛ (identity ∘ ρ) , (π * 1#) + 0# ∙ A
      ≡⟨ cong (π ** 0s ⋈ Γ ⊛ (identity ∘ ρ) ,_∙ A) (+-identityʳ (π * 1#)) ⟩
        π ** 0s ⋈ Γ ⊛ (identity ∘ ρ) , π * 1# ∙ A
      ≡⟨ cong (π ** 0s ⋈ Γ ⊛ (identity ∘ ρ) ,_∙ A) (*-identityʳ π) ⟩
        π ** 0s ⋈ Γ ⊛ (identity ∘ ρ) , π ∙ A
      ≡⟨ cong (_, π ∙ A) (cong (_⋈ Γ ⊛ (identity ∘ ρ )) (sym (**-zeroʳ δ π))) ⟩
        0s ⋈ Γ ⊛ (identity ∘ ρ) , π ∙ A
      ≡⟨ cong (_, π ∙ A) (⋈-identityˡ (Γ ⊛ (identity ∘ ρ))) ⟩
        Γ ⊛ (identity ∘ ρ) , π ∙ A
      ∎

rename′ {δ = δ} ρ (_·_ {γ} {Γ₁} {Γ₂} {A} {B} {π} {L} {M} ⊢L ⊢M) =
  Eq.subst (_⊢₁ B ∋ (rename ρ L · rename ρ M)) lem (rename′ ρ ⊢L · rename′ ρ ⊢M)
  where
    lem =
      begin
        Γ₁ ⊛ (identity ∘ ρ) ⋈ π ** (Γ₂ ⊛ (identity ∘ ρ))
      ≡⟨ cong (Γ₁ ⊛ (identity ∘ ρ) ⋈_) (sym (⊛-preserves-** Γ₂ (identity ∘ ρ))) ⟩
        Γ₁ ⊛ (identity ∘ ρ) ⋈ (π ** Γ₂) ⊛ (identity ∘ ρ)
      ≡⟨ sym (⊛-distribʳ-⋈ Γ₁ (π ** Γ₂) (identity ∘ ρ)) ⟩
        (Γ₁ ⋈ π ** Γ₂) ⊛ (identity ∘ ρ)
      ∎
\end{code}

We can introduce one 0-size dimension.

\begin{code}
weaken′ : ∀ {γ} {Γ : Context γ} {A B} {M}

  → Γ ⊢₁ A ∋ M
  ---------------------------
  → Γ , 0# ∙ B ⊢₁ A ∋ rename S_ M

weaken′ {γ} {Γ} {A} {B} {M} ⊢₁M
  = Eq.subst (_⊢₁ A ∋ rename S_ M) lem (rename′ S_ ⊢₁M)
  where
    lem =
      begin
        Γ ⊛ (identity ∘ S_)
      ≡⟨⟩
        Γ ⊛ (λ x → identity x , 0# ∙ B)
      ≡⟨ ⊛-zeroʳ Γ identity ⟩
        (Γ ⊛ identity) , 0# ∙ B
      ≡⟨ cong (_, 0# ∙ B) (⊛-identityʳ Γ) ⟩
        Γ , 0# ∙ B
      ∎
\end{code}

We can actually use the substitution matrix.

\begin{code}
subst′ : ∀ {γ δ} {Γ : Context γ} {B} {M}

  → (σ : ∀ {A} → γ ∋ A → δ ⊢ A)
  → (Δ : ∀ {A} → γ ∋ A → Context δ)
  → (P : ∀ {A} → (x : γ ∋ A) → Δ x ⊢₁ A ∋ σ x)
  → Γ ⊢₁ B ∋ M
    --------------------------------------
  → Γ ⊛ Δ ⊢₁ B ∋ (subst σ M)

subst′ {δ = δ} σ Δ P (`_ {γ} {B} x)
  = Eq.subst (_⊢₁ B ∋ σ x) lem (P x)
  where
    lem =
      begin
        Δ x
      ≡⟨ sym (⊛-identityˡ Δ x) ⟩
        identity x ⊛ Δ
      ∎

subst′ {δ = δ} σ Δ P (ƛ_ {γ} {Γ} {A} {B} {π} {N} ⊢N)
  = ƛ Eq.subst (_⊢₁ B ∋ subst (exts σ) N) lem ⊢N′
  where
    ⊢N′ = subst′ (exts σ) Δ′ P′ ⊢N
      where
        Δ′ : ∀ {A B} → γ , B ∋ A → Context (δ , B)
        Δ′ Z     = identity Z
        Δ′ (S x) = Δ x , 0# ∙ _
        P′ : ∀ {A B} → (x : γ , B ∋ A) → Δ′ x ⊢₁ A ∋ (exts σ) x
        P′ Z     = ` Z 
        P′ (S x) = weaken′ (P x)
    lem =
      begin
        (π ** 0s , π * 1# ∙ A) ⋈ (Γ ⊛ (λ x → Δ x , 0# ∙ A))
      ≡⟨ cong ((π ** 0s , π * 1# ∙ A) ⋈_) (⊛-zeroʳ Γ Δ) ⟩
        (π ** 0s , π * 1# ∙ A) ⋈ (Γ ⊛ Δ , 0# ∙ A)
      ≡⟨⟩
        π ** 0s ⋈ Γ ⊛ Δ , (π * 1#) + 0# ∙ A
      ≡⟨ cong (_, (π * 1#) + 0# ∙ A) (cong (_⋈ Γ ⊛ Δ) (sym (**-zeroʳ δ π))) ⟩
        0s ⋈ Γ ⊛ Δ , (π * 1#) + 0# ∙ A
      ≡⟨ cong (_, (π * 1#) + 0# ∙ A) (⋈-identityˡ (Γ ⊛ Δ)) ⟩
        Γ ⊛ Δ , (π * 1#) + 0# ∙ A
      ≡⟨ cong (Γ ⊛ Δ ,_∙ A) (+-identityʳ (π * 1#)) ⟩
        Γ ⊛ Δ , π * 1# ∙ A
      ≡⟨ cong (Γ ⊛ Δ ,_∙ A) (*-identityʳ π) ⟩
        Γ ⊛ Δ , π ∙ A
      ∎

subst′ {δ = δ} σ Δ P (_·_ {γ} {Γ₁} {Γ₂} {A} {B} {π} {L} {M} ⊢L ⊢M)
  = Eq.subst (_⊢₁ B ∋ (subst σ L · subst σ M)) lem (subst′ σ Δ P ⊢L · subst′ σ Δ P ⊢M)
  where
    lem =
      begin
        Γ₁ ⊛ Δ ⋈ π ** (Γ₂ ⊛ Δ)
      ≡⟨ cong (Γ₁ ⊛ Δ ⋈_) (sym (⊛-preserves-** Γ₂ Δ)) ⟩
        Γ₁ ⊛ Δ ⋈ (π ** Γ₂) ⊛ Δ
      ≡⟨ sym (⊛-distribʳ-⋈ Γ₁ (π ** Γ₂) Δ) ⟩
        (Γ₁ ⋈ π ** Γ₂) ⊛ Δ
      ∎
\end{code}
