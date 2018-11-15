---
title     : "Quantative: Quantative Type Theory and the Linear Lambda Calculus"
layout    : page
permalink : /Quantative/
---

\begin{code}
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Algebra.Structures using (module IsSemiring; IsSemiring)
\end{code}

\begin{code}
module plfa.Quantative
  {Mult : Set}
  (_+_ _*_ : Mult → Mult → Mult)
  (0# 1# : Mult)
  (*-+-isSemiring : IsSemiring _≡_ _+_ _*_ 0# 1#)
  where
\end{code}

\begin{code}
open import Function using (_∘_; _|>_)
open Eq using (refl; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)
open IsSemiring *-+-isSemiring hiding (refl; sym)
\end{code}

\begin{code}
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
**-identityˡ (Γ , π ∙ A) rewrite **-identityˡ Γ | *-identityˡ π = refl
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
  ≡⟨ *-assoc π π′ π″ |> cong ((π * π′) ** Γ ,_∙ A) ⟩
    (π * π′) ** Γ , π * (π′ * π″) ∙ A
  ≡⟨ **-assoc Γ |> cong (_, π * (π′ * π″) ∙ A) ⟩
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
**-zeroʳ : ∀ {γ} π

  --------------------
  → 0s {γ} ≡ π ** 0s

**-zeroʳ {∅} π = refl
**-zeroʳ {γ , A} π =
  begin
    0s , 0# ∙ A
  ≡⟨ zeroʳ π |> sym ∘ cong (0s ,_∙ A) ⟩
    0s , π * 0# ∙ A
  ≡⟨ **-zeroʳ π |> cong (_, π * 0# ∙ A) ⟩
    π ** 0s , π * 0# ∙ A
  ∎
\end{code}

Scaling by 0 gives the 0-vector.

\begin{code}
**-zeroˡ : ∀ {γ} (Γ : Context γ)

  -----------------
  → 0# ** Γ ≡ 0s

**-zeroˡ ∅ = refl
**-zeroˡ (Γ , π ∙ A) rewrite **-zeroˡ Γ | zeroˡ π = refl
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
⋈-identityˡ (Γ , π ∙ A) rewrite ⋈-identityˡ Γ | +-identityˡ π = refl
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
  ≡⟨ +-comm π₁ π₂ |> cong (Γ₁ ⋈ Γ₂ ,_∙ A) ⟩
    Γ₁ ⋈ Γ₂ , π₂ + π₁ ∙ A
  ≡⟨ ⋈-comm Γ₁ Γ₂ |> cong (_, π₂ + π₁ ∙ A) ⟩
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
  ≡⟨ +-assoc π₁ π₂ π₃ |> cong ((Γ₁ ⋈ Γ₂) ⋈ Γ₃ ,_∙ A) ⟩
    (Γ₁ ⋈ Γ₂) ⋈ Γ₃ , π₁ + (π₂ + π₃) ∙ A
  ≡⟨ ⋈-assoc Γ₁ Γ₂ Γ₃ |> cong (_, π₁ + (π₂ + π₃) ∙ A) ⟩
    Γ₁ ⋈ (Γ₂ ⋈ Γ₃) , π₁ + (π₂ + π₃) ∙ A
  ∎
\end{code}

Scaling by a sum gives the sum of the scalings.

\begin{code}
**-distribʳ-⋈ : ∀ {γ} (Γ : Context γ) (π₁ π₂ : Mult)

  -----------------------------------
  → (π₁ + π₂) ** Γ ≡ π₁ ** Γ ⋈ π₂ ** Γ

**-distribʳ-⋈ ∅ π₁ π₂ = refl
**-distribʳ-⋈ (Γ , π ∙ A) π₁ π₂ =
  begin
    (π₁ + π₂) ** Γ , (π₁ + π₂) * π ∙ A
  ≡⟨ distribʳ π π₁ π₂ |> cong ((π₁ + π₂) ** Γ ,_∙ A) ⟩
    (π₁ + π₂) ** Γ , (π₁ * π) + (π₂ * π) ∙ A
  ≡⟨ **-distribʳ-⋈ Γ π₁ π₂ |> cong (_, (π₁ * π) + (π₂ * π) ∙ A) ⟩
    π₁ ** Γ ⋈ π₂ ** Γ , (π₁ * π) + (π₂ * π) ∙ A
  ∎
\end{code}

Scaling a sum gives the sum of the scalings.

\begin{code}
**-distribˡ-⋈ : ∀ {γ} (Γ₁ Γ₂ : Context γ) (π : Mult)

  --------------------------------------
  → π ** (Γ₁ ⋈ Γ₂) ≡ π ** Γ₁ ⋈ π ** Γ₂

**-distribˡ-⋈ ∅ ∅ π = refl
**-distribˡ-⋈ (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) π =
  begin
    π ** (Γ₁ ⋈ Γ₂) , π * (π₁ + π₂) ∙ A
  ≡⟨ distribˡ π π₁ π₂ |> cong (π ** (Γ₁ ⋈ Γ₂) ,_∙ A) ⟩
    π ** (Γ₁ ⋈ Γ₂) , (π * π₁) + (π * π₂) ∙ A
  ≡⟨ **-distribˡ-⋈ Γ₁ Γ₂ π |> cong (_, (π * π₁) + (π * π₂) ∙ A) ⟩
    π ** Γ₁ ⋈ π ** Γ₂ , (π * π₁) + (π * π₂) ∙ A
  ∎
\end{code}

\begin{code}
Matrix : Precontext → Precontext → Set
Matrix γ δ = ∀ {A} → γ ∋ A → Context δ
\end{code}

(See [this sidenote][plfa.Linearity.LinAlg].)

The identity matrix.

\begin{code}
identity : ∀ {γ} → Matrix γ γ
identity {γ , A} Z     = 0s , 1# ∙ A
identity {γ , B} (S x) = identity x , 0# ∙ B
\end{code}

Matrix-vector multiplication ΔᵀΓ.

\begin{code}
_⊛_ : ∀ {γ δ}

  → Context γ
  → Matrix γ δ
  → Context δ

∅           ⊛ Δ = 0s
(Γ , π ∙ A) ⊛ Δ = (π ** Δ Z) ⋈ Γ ⊛ (Δ ∘ S_)
\end{code}

Linear maps preserve the 0-vector.

\begin{code}
⊛-zeroˡ : ∀ {γ δ} (Δ : Matrix γ δ)

  -----------------------------------
  → 0s ⊛ Δ ≡ 0s

⊛-zeroˡ {∅}     {δ} Δ = refl
⊛-zeroˡ {γ , A} {δ} Δ =
  begin
    0s ⊛ Δ
  ≡⟨⟩
    0# ** Δ Z ⋈ 0s ⊛ (Δ ∘ S_)
  ≡⟨ ⊛-zeroˡ (Δ ∘ S_) |> cong (0# ** Δ Z ⋈_) ⟩
    0# ** Δ Z ⋈ 0s
  ≡⟨ **-zeroˡ (Δ Z) |> cong (_⋈ 0s) ⟩
    0s ⋈ 0s
  ≡⟨ ⋈-identityʳ 0s ⟩
    0s
  ∎
\end{code}

Adding a row of 0s to the end of the matrix and then multiplying by a vector produces a vector with a 0 at the bottom.

\begin{code}
⊛-zeroʳ : ∀ {γ δ} (Γ : Context γ) (Δ : Matrix γ δ) {B}

  ---------------------------------------------------
  → Γ ⊛ (λ x → Δ x , 0# ∙ B) ≡ Γ ⊛ Δ , 0# ∙ B

⊛-zeroʳ {γ} {δ} ∅ Δ {B} = refl
⊛-zeroʳ {γ} {δ} (Γ , π ∙ C) Δ {B} =
  begin
    (π ** Δ Z , π * 0# ∙ B) ⋈ (Γ ⊛ (λ x → Δ (S x) , 0# ∙ B))
  ≡⟨ ⊛-zeroʳ Γ (Δ ∘ S_) |> cong ((π ** Δ Z , π * 0# ∙ B) ⋈_) ⟩
    (π ** Δ Z , π * 0# ∙ B) ⋈ (Γ ⊛ (λ x → Δ (S x)) , 0# ∙ B)
  ≡⟨⟩
    (π ** Δ Z , π * 0# ∙ B) ⋈ (Γ ⊛ (Δ ∘ S_) , 0# ∙ B)
  ≡⟨⟩
    (π ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_)) , (π * 0#) + 0# ∙ B
  ≡⟨ +-identityʳ (π * 0#) |> cong ((π ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_)) ,_∙ B) ⟩
    (π ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_)) , π * 0# ∙ B
  ≡⟨ zeroʳ π |> cong ((π ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_)) ,_∙ B) ⟩
    (π ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_)) , 0# ∙ B
  ∎
\end{code}

Linear maps preserve scaling.

\begin{code}
⊛-preserves-** : ∀ {γ δ} (Γ : Context γ) (Δ : Matrix γ δ) (π : Mult)

  -----------------------------------
  → (π ** Γ) ⊛ Δ ≡ π ** (Γ ⊛ Δ)

⊛-preserves-** {γ} {δ} ∅ Δ π =
  begin
    0s
  ≡⟨ **-zeroʳ π ⟩
    π ** 0s
  ∎

⊛-preserves-** {γ} {δ} (Γ , π′ ∙ A) Δ π =
  begin
    ((π * π′) ** Δ Z) ⋈ ((π ** Γ) ⊛ (Δ ∘ S_))
  ≡⟨ ⊛-preserves-** Γ (Δ ∘ S_) π |> cong ((π * π′) ** Δ Z ⋈_) ⟩
    ((π * π′) ** Δ Z) ⋈ (π ** (Γ ⊛ (Δ ∘ S_)))
  ≡⟨ **-assoc (Δ Z) |> cong (_⋈ (π ** (Γ ⊛ (Δ ∘ S_)))) ⟩
    (π ** (π′ ** Δ Z)) ⋈ (π ** (Γ ⊛ (Δ ∘ S_)))
  ≡⟨ **-distribˡ-⋈ (π′ ** Δ Z) (Γ ⊛ (Δ ∘ S_)) π |> sym ⟩
    π ** (π′ ** Δ Z ⋈ Γ ⊛ (Δ ∘ S_))
  ∎
\end{code}

Linear maps distribute over sums.

\begin{code}
⊛-distribʳ-⋈ : ∀ {γ} {δ} (Γ₁ Γ₂ : Context γ) (Δ : Matrix γ δ)

  ----------------------------------
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
  ≡⟨ ⊛-distribʳ-⋈ Γ₁ Γ₂ (Δ ∘ S_) |> cong ((π₁ + π₂) ** Δ Z ⋈_) ⟩
    (π₁ + π₂) ** Δ Z ⋈ (Γ₁ ⊛ (Δ ∘ S_) ⋈ Γ₂ ⊛ (Δ ∘ S_))
  ≡⟨ **-distribʳ-⋈ (Δ Z) π₁ π₂ |> cong (_⋈ Γ₁ ⊛ (Δ ∘ S_) ⋈ Γ₂ ⊛ (Δ ∘ S_)) ⟩
    (π₁ ** Δ Z ⋈ π₂ ** Δ Z) ⋈ (Γ₁ ⊛ (Δ ∘ S_) ⋈ Γ₂ ⊛ (Δ ∘ S_))
  ≡⟨ ⋈-assoc (π₁ ** Δ Z ⋈ π₂ ** Δ Z) (Γ₁ ⊛ (Δ ∘ S_)) (Γ₂ ⊛ (Δ ∘ S_)) |> sym ⟩
    ((π₁ ** Δ Z ⋈ π₂ ** Δ Z) ⋈ Γ₁ ⊛ (Δ ∘ S_)) ⋈ Γ₂ ⊛ (Δ ∘ S_)
  ≡⟨ ⋈-assoc (π₁ ** Δ Z) (π₂ ** Δ Z) (Γ₁ ⊛ (Δ ∘ S_)) |> cong (_⋈ Γ₂ ⊛ (Δ ∘ S_)) ⟩
    (π₁ ** Δ Z ⋈ (π₂ ** Δ Z ⋈ Γ₁ ⊛ (Δ ∘ S_))) ⋈ Γ₂ ⊛ (Δ ∘ S_)
  ≡⟨ ⋈-comm (π₂ ** Δ Z) (Γ₁ ⊛ (Δ ∘ S_)) |> cong ((_⋈ Γ₂ ⊛ (Δ ∘ S_)) ∘ (π₁ ** Δ Z ⋈_)) ⟩
    (π₁ ** Δ Z ⋈ (Γ₁ ⊛ (Δ ∘ S_) ⋈ π₂ ** Δ Z)) ⋈ Γ₂ ⊛ (Δ ∘ S_)
  ≡⟨ ⋈-assoc (π₁ ** Δ Z) (Γ₁ ⊛ (Δ ∘ S_)) (π₂ ** Δ Z) |> sym ∘ cong (_⋈ Γ₂ ⊛ (Δ ∘ S_)) ⟩
    ((π₁ ** Δ Z ⋈ Γ₁ ⊛ (Δ ∘ S_)) ⋈ π₂ ** Δ Z) ⋈ Γ₂ ⊛ (Δ ∘ S_)
  ≡⟨ ⋈-assoc (π₁ ** Δ Z ⋈ Γ₁ ⊛ (Δ ∘ S_)) (π₂ ** Δ Z) (Γ₂ ⊛ (Δ ∘ S_)) ⟩
    (π₁ ** Δ Z ⋈ Γ₁ ⊛ (Δ ∘ S_)) ⋈ (π₂ ** Δ Z ⋈ Γ₂ ⊛ (Δ ∘ S_))
  ∎
\end{code}

Multiplying by a standard basis vector projects out the corresponding column of the matrix.

\begin{code}
⊛-identityˡ : ∀ {γ δ} {A} (Δ : Matrix γ δ)

  → (x : γ ∋ A)
  -----------------------
  → identity x ⊛ Δ ≡ Δ x

⊛-identityˡ {γ , A} {δ} {A} Δ Z =
  begin
    identity Z ⊛ Δ
  ≡⟨⟩
    1# ** Δ Z ⋈ 0s ⊛ (Δ ∘ S_)
  ≡⟨ ⊛-zeroˡ (Δ ∘ S_) |> cong ((1# ** Δ Z) ⋈_) ⟩
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
  ≡⟨ ⊛-identityˡ (Δ ∘ S_) x |> cong (0# ** Δ Z ⋈_) ⟩
    0# ** Δ Z ⋈ Δ (S x)
  ≡⟨ **-zeroˡ (Δ Z) |> cong (_⋈ Δ (S x)) ⟩
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
  ≡⟨ ⊛-zeroʳ Γ identity |> cong ((π ** 0s , π * 1# ∙ A) ⋈_) ⟩
    (π ** 0s , π * 1# ∙ A) ⋈ (Γ ⊛ identity , 0# ∙ A)
  ≡⟨ ⊛-identityʳ Γ |> cong (((π ** 0s , π * 1# ∙ A) ⋈_) ∘ (_, 0# ∙ A)) ⟩
    (π ** 0s , π * 1# ∙ A) ⋈ (Γ , 0# ∙ A)
  ≡⟨⟩
    π ** 0s ⋈ Γ , (π * 1#) + 0# ∙ A
  ≡⟨ +-identityʳ (π * 1#) |> cong ((π ** 0s ⋈ Γ) ,_∙ A) ⟩
    π ** 0s ⋈ Γ , π * 1# ∙ A
  ≡⟨ *-identityʳ π |> cong ((π ** 0s ⋈ Γ) ,_∙ A) ⟩
    π ** 0s ⋈ Γ , π ∙ A
  ≡⟨ **-zeroʳ π |> cong ((_, π ∙ A) ∘ (_⋈ Γ)) ∘ sym ⟩
    0s ⋈ Γ , π ∙ A
  ≡⟨ ⋈-identityˡ Γ |> cong (_, π ∙ A) ⟩
    Γ , π ∙ A
  ∎
\end{code}

\begin{code}
data _⊢_ : ∀ {γ} (Γ : Context γ) (A : Type) → Set where

  `_  : ∀ {γ} {A}

      → (x : γ ∋ A)
        --------------
      → identity x ⊢ A

  ƛ_  : ∀ {γ} {Γ : Context γ} {A B} {π}

      → Γ , π ∙ A ⊢ B
        ----------------
      → Γ ⊢ [ π ∙ A ]⊸ B

  _·_ : ∀ {γ} {Γ Γ′ : Context γ} {A B} {π}

      → Γ  ⊢ [ π ∙ A ]⊸ B
      → Γ′ ⊢ A
        ----------------
      → Γ ⋈ π ** Γ′ ⊢ B
\end{code}

\begin{code}
ext : ∀ {γ δ}

  → (∀ {A}   →     γ ∋ A →     δ ∋ A)
    ---------------------------------
  → (∀ {A B} → γ , B ∋ A → δ , B ∋ A)

ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
\end{code}

\begin{code}
rename-` : ∀ {γ δ} {B} (ρ : ∀ {A} → γ ∋ A → δ ∋ A) (x : γ ∋ B) → _
rename-` ρ x =
  begin
    identity (ρ x)
  ≡⟨ ⊛-identityˡ (identity ∘ ρ) x |> sym  ⟩
    identity x ⊛ (identity ∘ ρ)
  ∎
\end{code}

\begin{code}
rename-ƛ : ∀ {γ δ} (Γ : Context γ) {B} {π} (ρ : ∀ {A} → γ ∋ A → δ ∋ A) → _
rename-ƛ {γ} {δ} Γ {B} {π} ρ =
  begin
    (π ** 0s , π * 1# ∙ B) ⋈ (Γ ⊛ (λ x → identity (ρ x) , 0# ∙ B))
  ≡⟨ ⊛-zeroʳ Γ (identity ∘ ρ) |> cong ((π ** 0s , π * 1# ∙ B) ⋈_) ⟩
    (π ** 0s , π * 1# ∙ B) ⋈ (Γ ⊛ (identity ∘ ρ) , 0# ∙ B)
  ≡⟨⟩
    π ** 0s ⋈ Γ ⊛ (identity ∘ ρ) , (π * 1#) + 0# ∙ B
  ≡⟨ +-identityʳ (π * 1#) |> cong (π ** 0s ⋈ Γ ⊛ (identity ∘ ρ) ,_∙ B) ⟩
    π ** 0s ⋈ Γ ⊛ (identity ∘ ρ) , π * 1# ∙ B
  ≡⟨ *-identityʳ π |> cong (π ** 0s ⋈ Γ ⊛ (identity ∘ ρ) ,_∙ B) ⟩
    π ** 0s ⋈ Γ ⊛ (identity ∘ ρ) , π ∙ B
  ≡⟨ **-zeroʳ π |> cong ((_, π ∙ B) ∘ (_⋈ Γ ⊛ (identity ∘ ρ ))) ∘ sym ⟩
    0s ⋈ Γ ⊛ (identity ∘ ρ) , π ∙ B
  ≡⟨ ⋈-identityˡ (Γ ⊛ (identity ∘ ρ)) |> cong (_, π ∙ B) ⟩
    Γ ⊛ (identity ∘ ρ) , π ∙ B
  ∎
\end{code}

\begin{code}
rename-· : ∀ {γ δ} (Γ Γ′ : Context γ) {π} (ρ : ∀ {A} → γ ∋ A → δ ∋ A) → _
rename-· {γ} {δ} Γ Γ′ {π} ρ =
  begin
    Γ ⊛ (identity ∘ ρ) ⋈ π ** (Γ′ ⊛ (identity ∘ ρ))
  ≡⟨ ⊛-preserves-** Γ′ (identity ∘ ρ) π |> sym ∘ cong (Γ ⊛ (identity ∘ ρ) ⋈_) ⟩
    Γ ⊛ (identity ∘ ρ) ⋈ (π ** Γ′) ⊛ (identity ∘ ρ)
  ≡⟨ ⊛-distribʳ-⋈ Γ (π ** Γ′) (identity ∘ ρ) |> sym ⟩
    (Γ ⋈ π ** Γ′) ⊛ (identity ∘ ρ)
  ∎
\end{code}

\begin{code}
rename : ∀ {γ δ} {Γ : Context γ} {B}

  → (ρ : ∀ {A} → γ ∋ A → δ ∋ A)
  → Γ ⊢ B
    ---------------------------
  → Γ ⊛ (identity ∘ ρ) ⊢ B

rename ρ (` x)                       = Eq.subst (_⊢ _) (rename-` ρ x) (` ρ x)
rename ρ (ƛ_  {Γ = Γ} N)             = ƛ (Eq.subst (_⊢ _) (rename-ƛ Γ ρ) (rename (ext ρ) N))
rename ρ (_·_ {Γ = Γ} {Γ′ = Γ′} L M) = Eq.subst (_⊢ _) (rename-· Γ Γ′ ρ) (rename ρ L · rename ρ M)
\end{code}

Extend a matrix as the identity matrix -- add a zero to the end of every row, and add a new row with a 1 and the rest 0s.

\begin{code}
extm : ∀ {γ δ}

  → Matrix γ δ
    --------------------------------
  → (∀ {B} → Matrix (γ , B) (δ , B))

extm Δ {B} {A} Z     = identity Z
extm Δ {B} {A} (S x) = Δ x , 0# ∙ B
\end{code}

\begin{code}
exts : ∀ {γ δ} {Δ : Matrix γ δ}

  → (∀ {A}   → (x :     γ ∋ A) →      Δ x ⊢ A)
    ------------------------------------------
  → (∀ {A B} → (x : γ , B ∋ A) → extm Δ x ⊢ A)

exts {Δ = Δ} σ {A} {B} Z     = ` Z
exts {Δ = Δ} σ {A} {B} (S x) = Eq.subst (_⊢ A) lem (rename S_ (σ x))
  where
    lem =
      begin
        Δ x ⊛ (identity ∘ S_)
     ≡⟨⟩
       Δ x ⊛ (λ x → identity x , 0# ∙ B)
     ≡⟨ ⊛-zeroʳ (Δ x) identity ⟩
       (Δ x ⊛ identity) , 0# ∙ B
     ≡⟨ ⊛-identityʳ (Δ x) |> cong (_, 0# ∙ B) ⟩
       Δ x , 0# ∙ B
     ∎
\end{code}

\begin{code}
subst : ∀ {γ δ} {Γ : Context γ} {Δ : Matrix γ δ} {B}

  → (σ : ∀ {A} → (x : γ ∋ A) → Δ x ⊢ A)
  → Γ ⊢ B
    --------------------------------------
  → Γ ⊛ Δ ⊢ B

subst {Δ = Δ} σ (`_ {γ} {A} x) =
  Eq.subst (_⊢ A) lem (σ x)
  where
    lem =
      begin
        Δ x
      ≡⟨ ⊛-identityˡ Δ x |> sym ⟩
        identity x ⊛ Δ
      ∎

subst {Δ = Δ} σ (ƛ_ {γ} {Γ} {A} {B} {π} N) =
  ƛ Eq.subst (_⊢ B) lem (subst (exts σ) N)
  where
    lem =
      begin
        (π ** 0s , π * 1# ∙ A) ⋈ (Γ ⊛ (λ x → Δ x , 0# ∙ A))
      ≡⟨ ⊛-zeroʳ Γ Δ |> cong ((π ** 0s , π * 1# ∙ A) ⋈_) ⟩
        (π ** 0s , π * 1# ∙ A) ⋈ (Γ ⊛ Δ , 0# ∙ A)
      ≡⟨⟩
        π ** 0s ⋈ Γ ⊛ Δ , (π * 1#) + 0# ∙ A
      ≡⟨ **-zeroʳ π |> cong ((_, (π * 1#) + 0# ∙ A) ∘ (_⋈ Γ ⊛ Δ)) ∘ sym ⟩
        0s ⋈ Γ ⊛ Δ , (π * 1#) + 0# ∙ A
      ≡⟨ ⋈-identityˡ (Γ ⊛ Δ) |> cong (_, (π * 1#) + 0# ∙ A) ⟩
        Γ ⊛ Δ , (π * 1#) + 0# ∙ A
      ≡⟨ +-identityʳ (π * 1#) |> cong (Γ ⊛ Δ ,_∙ A) ⟩
        Γ ⊛ Δ , π * 1# ∙ A
      ≡⟨ *-identityʳ π |> cong (Γ ⊛ Δ ,_∙ A) ⟩
        Γ ⊛ Δ , π ∙ A
      ∎

subst {Δ = Δ} σ (_·_ {γ} {Γ} {Γ′} {A} {B} {π} L M) =
  Eq.subst (_⊢ B) lem (subst σ L · subst σ M)
  where
    lem =
      begin
        Γ ⊛ Δ ⋈ π ** (Γ′ ⊛ Δ)
      ≡⟨ ⊛-preserves-** Γ′ Δ π |> cong (Γ ⊛ Δ ⋈_) ∘ sym ⟩
        Γ ⊛ Δ ⋈ (π ** Γ′) ⊛ Δ
      ≡⟨ ⊛-distribʳ-⋈ Γ (π ** Γ′) Δ |> sym ⟩
        (Γ ⋈ π ** Γ′) ⊛ Δ
      ∎
\end{code}

\begin{code}
_[_] : ∀ {γ} {Γ Γ′ : Context γ} {A B} {π}

  → Γ , π ∙ B ⊢ A
  → Γ′ ⊢ B
    --------------
  → Γ ⋈ π ** Γ′ ⊢ A

_[_] {γ} {Γ} {Γ′} {A} {B} {π} N M = Eq.subst (_⊢ A) lem (subst σ N)
  where
    Δ : Matrix (γ , B) γ
    Δ Z     = Γ′
    Δ (S x) = identity x
    σ : ∀ {A} → (x : γ , B ∋ A) → Δ x ⊢ A
    σ Z     = M
    σ (S x) = ` x
    lem =
      begin
        π ** Γ′ ⋈ Γ ⊛ identity
      ≡⟨ ⋈-comm (π ** Γ′) (Γ ⊛ identity) ⟩
        Γ ⊛ identity ⋈ π ** Γ′
      ≡⟨ ⊛-identityʳ Γ |> cong (_⋈ π ** Γ′) ⟩
        Γ ⋈ π ** Γ′
      ∎
\end{code}

\begin{code}
data Value : ∀ {γ} {Γ : Context γ} {A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {γ} {Γ : Context γ} {A B} {π} {N : Γ , π ∙ A ⊢ B}

      -----------
    → Value (ƛ N)
\end{code}

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {γ} {Γ : Context γ} {A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {γ} {Γ Γ′ : Context γ} {A B} {π} {L L′ : Γ ⊢ [ π ∙ A ]⊸ B} {M : Γ′ ⊢ A}

    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {γ} {Γ Γ′ : Context γ} {A B} {π} {V : Γ ⊢ [ π ∙ A ]⊸ B} {M M′ : Γ′ ⊢ A}

    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′

  β-ƛ : ∀ {γ} {Γ Γ′ : Context γ} {A B} {π} {N : Γ , π ∙ A ⊢ B} {W : Γ′ ⊢ A}

    → Value W
      -------------------
    → (ƛ N) · W —→ N [ W ]
\end{code}

\begin{code}
data Progress {γ} {Γ : Context γ} {A} (M : Γ ⊢ A) : Set where

  step : {N : Γ ⊢ A}

    → M —→ N
      ----------
    → Progress M

  done :

      Value M
      ----------
    → Progress M
\end{code}

\begin{code}
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress M = go refl M
  where
    go : ∀ {γ} {Γ : Context γ} {A} → γ ≡ ∅ → (M : Γ ⊢ A) → Progress M
    go refl (` ())
    go refl (ƛ N)           = done V-ƛ
    go refl (L · M) with go refl L
    ...    | step L-→L′     = step (ξ-·₁ L-→L′)
    ...    | done V-ƛ with go refl M
    ...        | step M-→M′ = step (ξ-·₂ V-ƛ M-→M′)
    ...        | done VM    = step (β-ƛ VM)
\end{code}
