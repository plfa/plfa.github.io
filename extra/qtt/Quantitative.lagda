---
title     : "Quantitative: Counting Resources in Types"
permalink : /Quantitative/
---

In previous chapters, we introduced the lambda calculus, with [a formalisation based on named variables][plfa.Lambda] and [an inherently-typed version][plfa.DeBruijn].  This chapter presents a refinement of those approaches, in which we not only care about the types of variables, but also about *how often they're used*.


# Imports & Module declaration

\begin{code}
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Algebra.Structures using (module IsSemiring; IsSemiring)
\end{code}

\begin{code}
module qtt.Quantitative
  {Mult : Set}
  (_+_ _*_ : Mult → Mult → Mult)
  (0# 1# : Mult)
  (*-+-isSemiring : IsSemiring _≡_ _+_ _*_ 0# 1#)
  where
\end{code}

\begin{code}
open import Function using (_∘_; _|>_)
open Eq using (refl; sym; trans; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)
open IsSemiring *-+-isSemiring hiding (refl; sym; trans)
\end{code}


# Syntax

\begin{code}
infix  1 _⊢_
infix  1 _∋_
infixl 5 _,_
infixl 5 _,_∙_
infixr 6 [_∙_]⊸_
infixl 7 _+̇_
infixl 8 _*̇_
infixl 8 _*⟩_
\end{code}


# Types

\begin{code}
data Type : Set where
  `0      : Type
  [_∙_]⊸_ : Mult → Type → Type → Type
  `1      : Type
  _⊗_     : Type → Type → Type
  _⊕_     : Type → Type → Type
\end{code}

\begin{code}
_⊸_ : Type → Type → Type
A ⊸ B = [ 1# ∙ A ]⊸ B
\end{code}

# Precontexts

\begin{code}
data Precontext : Set where
  ∅   : Precontext
  _,_ : Precontext → Type → Precontext

variable γ δ : Precontext
\end{code}

\begin{code}
_ : Precontext
_ = ∅ , `0 ⊸ `0 , `0
\end{code}


# Variables and the lookup judgment

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


# Contexts

\begin{code}
data Context : Precontext → Set where
  ∅     : Context ∅
  _,_∙_ : ∀ {Γ} → Context Γ → Mult → (A : Type) → Context (Γ , A)

variable Γ Δ Θ : Context γ
\end{code}

\begin{code}
_ : Context (∅ , `0 ⊸ `0 , `0)
_ = ∅ , 1# ∙ `0 ⊸ `0 , 0# ∙ `0
\end{code}


# Resources and linear algebra

Scaling.

\begin{code}
_*̇_ : ∀ {γ} → Mult → Context γ → Context γ
π *̇ ∅ = ∅
π *̇ (Γ , ρ ∙ A) = π *̇ Γ , π * ρ ∙ A
\end{code}

The 0-vector.

\begin{code}
0s : ∀ {γ} → Context γ
0s {∅}     = ∅
0s {γ , A} = 0s , 0# ∙ A
\end{code}

Vector addition.

\begin{code}
_+̇_ : ∀ {γ} → Context γ → Context γ → Context γ
∅ +̇ ∅ = ∅
(Γ₁ , π₁ ∙ A) +̇ (Γ₂ , π₂ ∙ .A) = Γ₁ +̇ Γ₂ , π₁ + π₂ ∙ A
\end{code}

Matrices.

See [this sidenote][plfa.Quantitative.LinAlg].

\begin{code}
Matrix : Precontext → Precontext → Set
Matrix γ δ = ∀ {A} → γ ∋ A → Context δ

variable Ξ : Matrix γ δ
\end{code}

The identity matrix.

          "x"       "y"       "z"
    "x"  1 ∙ A  ,  0 ∙ B  ,  0 ∙ C
    "y"  0 ∙ A  ,  1 ∙ B  ,  0 ∙ C
    "z"  0 ∙ A  ,  0 ∙ B  ,  1 ∙ C

\begin{code}
identity : ∀ {γ} → Matrix γ γ
identity {γ , A} Z     = 0s , 1# ∙ A
identity {γ , B} (S x) = identity x , 0# ∙ B
\end{code}


# Terms and the typing judgment

\begin{code}
data _⊢_ : ∀ {γ} (Γ : Context γ) (A : Type) → Set where

  `_    : ∀ {γ} {A}

        → (x : γ ∋ A)
          --------------
        → identity x ⊢ A

  ƛ_    : ∀ {γ} {Γ : Context γ} {A B} {π}

        → Γ , π ∙ A ⊢ B
          ----------------
        → Γ ⊢ [ π ∙ A ]⊸ B

  _·_   : ∀ {γ} {Γ Δ : Context γ} {A B} {π}

        → Γ ⊢ [ π ∙ A ]⊸ B
        → Δ ⊢ A
          ----------------
        → Γ +̇ π *̇ Δ ⊢ B

  ⟨⟩    : ∀ {γ}

          -----------
        → 0s {γ} ⊢ `1

  case1 : ∀ {γ} {Γ Δ : Context γ} {A}

        → Γ ⊢ `1
        → Δ ⊢ A
          ---------
        → Γ +̇ Δ ⊢ A

  ⟨_,_⟩ : ∀ {γ} {Γ Δ : Context γ} {A B}

        → Γ ⊢ A
        → Δ ⊢ B
          -------------
        → Γ +̇ Δ ⊢ A ⊗ B

  case⊗ : ∀ {γ} {Γ Δ : Context γ} {A B C}

        → Γ ⊢ A ⊗ B
        → Δ , 1# ∙ A , 1# ∙ B ⊢ C
          -----------------------
        → Γ +̇ Δ ⊢ C

  inj₁  : ∀ {γ} {Γ : Context γ} {A B}

        → Γ ⊢ A
          ---------
        → Γ ⊢ A ⊕ B

  inj₂  : ∀ {γ} {Γ : Context γ} {A B}

        → Γ ⊢ B
          ---------
        → Γ ⊢ A ⊕ B

  case⊕ : ∀ {γ} {Γ Δ : Context γ} {A B C}

        → Γ ⊢ A ⊕ B
        → Δ , 1# ∙ A ⊢ C
        → Δ , 1# ∙ B ⊢ C
          --------------
        → Γ +̇ Δ ⊢ C
\end{code}


# Properties of vector operations

Unit scaling does nothing.

\begin{code}
*̇-identityˡ : ∀ {γ} (Γ : Context γ)

    -----------
  → 1# *̇ Γ ≡ Γ

*̇-identityˡ ∅ = refl
*̇-identityˡ (Γ , π ∙ A) =
  begin
    1# *̇ Γ , 1# * π ∙ A
  ≡⟨ *-identityˡ π |> cong (1# *̇ Γ ,_∙ A) ⟩
    1# *̇ Γ , π ∙ A
  ≡⟨ *̇-identityˡ Γ |> cong (_, π ∙ A) ⟩
    Γ , π ∙ A
  ∎
\end{code}

Scaling by a product is the composition of scalings.

\begin{code}
*̇-assoc : ∀ {γ} (Γ : Context γ) {π π′}

    ------------------------------
  → (π * π′) *̇ Γ ≡ π *̇ (π′ *̇ Γ)

*̇-assoc ∅ = refl
*̇-assoc (Γ , π″ ∙ A) {π} {π′} =
  begin
    (π * π′) *̇ Γ , (π * π′) * π″ ∙ A
  ≡⟨ *-assoc π π′ π″ |> cong ((π * π′) *̇ Γ ,_∙ A) ⟩
    (π * π′) *̇ Γ , π * (π′ * π″) ∙ A
  ≡⟨ *̇-assoc Γ |> cong (_, π * (π′ * π″) ∙ A) ⟩
    π *̇ (π′ *̇ Γ) , π * (π′ * π″) ∙ A
  ∎
\end{code}

Scaling the 0-vector gives the 0-vector.

\begin{code}
*̇-zeroʳ : ∀ {γ} π

    ----------------
  → 0s {γ} ≡ π *̇ 0s

*̇-zeroʳ {∅} π = refl
*̇-zeroʳ {γ , A} π =
  begin
    0s , 0# ∙ A
  ≡⟨ zeroʳ π |> sym ∘ cong (0s ,_∙ A) ⟩
    0s , π * 0# ∙ A
  ≡⟨ *̇-zeroʳ π |> cong (_, π * 0# ∙ A) ⟩
    π *̇ 0s , π * 0# ∙ A
  ∎
\end{code}

Scaling by 0 gives the 0-vector.

\begin{code}
*̇-zeroˡ : ∀ {γ} (Γ : Context γ)

    ------------
  → 0# *̇ Γ ≡ 0s

*̇-zeroˡ ∅ = refl
*̇-zeroˡ (Γ , π ∙ A) =
  begin
    0# *̇ Γ , 0# * π ∙ A
  ≡⟨ zeroˡ π |> cong (0# *̇ Γ ,_∙ A) ⟩
    0# *̇ Γ , 0# ∙ A
  ≡⟨ *̇-zeroˡ Γ |> cong (_, 0# ∙ A) ⟩
    0s , 0# ∙ A
  ∎
\end{code}

Adding the 0-vector does nothing.

\begin{code}
+̇-identityˡ : ∀ {γ} (Γ : Context γ)

    ----------
  → 0s +̇ Γ ≡ Γ

+̇-identityˡ ∅ = refl
+̇-identityˡ (Γ , π ∙ A) =
  begin
    0s +̇ Γ , 0# + π ∙ A
  ≡⟨ +-identityˡ π |> cong (0s +̇ Γ ,_∙ A) ⟩
    0s +̇ Γ , π ∙ A
  ≡⟨ +̇-identityˡ Γ |> cong (_, π ∙ A) ⟩
    Γ , π ∙ A
  ∎
\end{code}

\begin{code}
+̇-identityʳ : ∀ {γ} (Γ : Context γ)

    ----------
  → Γ +̇ 0s ≡ Γ

+̇-identityʳ ∅ = refl
+̇-identityʳ (Γ , π ∙ A) =
  begin
    Γ +̇ 0s , π + 0# ∙ A
  ≡⟨ +-identityʳ π |> cong (Γ +̇ 0s ,_∙ A) ⟩
    Γ +̇ 0s , π ∙ A
  ≡⟨ +̇-identityʳ Γ |> cong (_, π ∙ A) ⟩
    Γ , π ∙ A
  ∎
\end{code}

Vector addition is commutative.

\begin{code}
+̇-comm : ∀ {γ} (Γ₁ Γ₂ : Context γ)

    -----------------
  → Γ₁ +̇ Γ₂ ≡ Γ₂ +̇ Γ₁

+̇-comm ∅ ∅ = refl
+̇-comm (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) =
  begin
    Γ₁ +̇ Γ₂ , π₁ + π₂ ∙ A
  ≡⟨ +-comm π₁ π₂ |> cong (Γ₁ +̇ Γ₂ ,_∙ A) ⟩
    Γ₁ +̇ Γ₂ , π₂ + π₁ ∙ A
  ≡⟨ +̇-comm Γ₁ Γ₂ |> cong (_, π₂ + π₁ ∙ A) ⟩
    Γ₂ +̇ Γ₁ , π₂ + π₁ ∙ A
  ∎
\end{code}

Vector addition is associative.

\begin{code}
+̇-assoc : ∀ {γ} (Γ₁ Γ₂ Γ₃ : Context γ)

  -------------------------------------
  → (Γ₁ +̇ Γ₂) +̇ Γ₃ ≡ Γ₁ +̇ (Γ₂ +̇ Γ₃)

+̇-assoc ∅ ∅ ∅ = refl
+̇-assoc (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) (Γ₃ , π₃ ∙ .A) =
  begin
    (Γ₁ +̇ Γ₂) +̇ Γ₃ , (π₁ + π₂) + π₃ ∙ A
  ≡⟨ +-assoc π₁ π₂ π₃ |> cong ((Γ₁ +̇ Γ₂) +̇ Γ₃ ,_∙ A) ⟩
    (Γ₁ +̇ Γ₂) +̇ Γ₃ , π₁ + (π₂ + π₃) ∙ A
  ≡⟨ +̇-assoc Γ₁ Γ₂ Γ₃ |> cong (_, π₁ + (π₂ + π₃) ∙ A) ⟩
    Γ₁ +̇ (Γ₂ +̇ Γ₃) , π₁ + (π₂ + π₃) ∙ A
  ∎
\end{code}

Scaling by a sum gives the sum of the scalings.

\begin{code}
*̇-distribʳ-+̇ : ∀ {γ} (Γ : Context γ) (π₁ π₂ : Mult)

  -----------------------------------
  → (π₁ + π₂) *̇ Γ ≡ π₁ *̇ Γ +̇ π₂ *̇ Γ

*̇-distribʳ-+̇ ∅ π₁ π₂ = refl
*̇-distribʳ-+̇ (Γ , π ∙ A) π₁ π₂ =
  begin
    (π₁ + π₂) *̇ Γ , (π₁ + π₂) * π ∙ A
  ≡⟨ distribʳ π π₁ π₂ |> cong ((π₁ + π₂) *̇ Γ ,_∙ A) ⟩
    (π₁ + π₂) *̇ Γ , (π₁ * π) + (π₂ * π) ∙ A
  ≡⟨ *̇-distribʳ-+̇ Γ π₁ π₂ |> cong (_, (π₁ * π) + (π₂ * π) ∙ A) ⟩
    π₁ *̇ Γ +̇ π₂ *̇ Γ , (π₁ * π) + (π₂ * π) ∙ A
  ∎
\end{code}

Scaling a sum gives the sum of the scalings.

\begin{code}
*̇-distribˡ-+̇ : ∀ {γ} (Γ₁ Γ₂ : Context γ) (π : Mult)

  --------------------------------------
  → π *̇ (Γ₁ +̇ Γ₂) ≡ π *̇ Γ₁ +̇ π *̇ Γ₂

*̇-distribˡ-+̇ ∅ ∅ π = refl
*̇-distribˡ-+̇ (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) π =
  begin
    π *̇ (Γ₁ +̇ Γ₂) , π * (π₁ + π₂) ∙ A
  ≡⟨ distribˡ π π₁ π₂ |> cong (π *̇ (Γ₁ +̇ Γ₂) ,_∙ A) ⟩
    π *̇ (Γ₁ +̇ Γ₂) , (π * π₁) + (π * π₂) ∙ A
  ≡⟨ *̇-distribˡ-+̇ Γ₁ Γ₂ π |> cong (_, (π * π₁) + (π * π₂) ∙ A) ⟩
    π *̇ Γ₁ +̇ π *̇ Γ₂ , (π * π₁) + (π * π₂) ∙ A
  ∎
\end{code}



# Vector-matrix multiplication

Vector-matrix multiplication.

\begin{code}
_*⟩_ : ∀ {γ δ} → Context γ → Matrix γ δ → Context δ
∅           *⟩ Ξ = 0s
(Γ , π ∙ A) *⟩ Ξ = (π *̇ Ξ Z) +̇ Γ *⟩ (Ξ ∘ S_)
\end{code}

Linear maps preserve the 0-vector.

\begin{code}
*⟩-zeroˡ : ∀ {γ δ} (Ξ : Matrix γ δ)

  --------------
  → 0s *⟩ Ξ ≡ 0s

*⟩-zeroˡ {∅}     {δ} Ξ = refl
*⟩-zeroˡ {γ , A} {δ} Ξ =
  begin
    0s *⟩ Ξ
  ≡⟨⟩
    0# *̇ Ξ Z +̇ 0s *⟩ (Ξ ∘ S_)
  ≡⟨ *⟩-zeroˡ (Ξ ∘ S_) |> cong (0# *̇ Ξ Z +̇_) ⟩
    0# *̇ Ξ Z +̇ 0s
  ≡⟨ *̇-zeroˡ (Ξ Z) |> cong (_+̇ 0s) ⟩
    0s +̇ 0s
  ≡⟨ +̇-identityʳ 0s ⟩
    0s
  ∎
\end{code}

Adding a row of 0s to the end of the matrix and then multiplying by a vector produces a vector with a 0 at the bottom.

\begin{code}
*⟩-zeroʳ : ∀ {γ δ} (Γ : Context γ) (Ξ : Matrix γ δ) {B}

  ---------------------------------------------
  → Γ *⟩ (λ x → Ξ x , 0# ∙ B) ≡ Γ *⟩ Ξ , 0# ∙ B

*⟩-zeroʳ {γ} {δ} ∅ Ξ {B} = refl
*⟩-zeroʳ {γ} {δ} (Γ , π ∙ C) Ξ {B} =
  begin
    (π *̇ Ξ Z , π * 0# ∙ B) +̇ (Γ *⟩ (λ x → Ξ (S x) , 0# ∙ B))
  ≡⟨ *⟩-zeroʳ Γ (Ξ ∘ S_) |> cong ((π *̇ Ξ Z , π * 0# ∙ B) +̇_) ⟩
    (π *̇ Ξ Z , π * 0# ∙ B) +̇ (Γ *⟩ (λ x → Ξ (S x)) , 0# ∙ B)
  ≡⟨⟩
    (π *̇ Ξ Z , π * 0# ∙ B) +̇ (Γ *⟩ (Ξ ∘ S_) , 0# ∙ B)
  ≡⟨⟩
    (π *̇ Ξ Z +̇ Γ *⟩ (Ξ ∘ S_)) , (π * 0#) + 0# ∙ B
  ≡⟨ +-identityʳ (π * 0#) |> cong ((π *̇ Ξ Z +̇ Γ *⟩ (Ξ ∘ S_)) ,_∙ B) ⟩
    (π *̇ Ξ Z +̇ Γ *⟩ (Ξ ∘ S_)) , π * 0# ∙ B
  ≡⟨ zeroʳ π |> cong ((π *̇ Ξ Z +̇ Γ *⟩ (Ξ ∘ S_)) ,_∙ B) ⟩
    (π *̇ Ξ Z +̇ Γ *⟩ (Ξ ∘ S_)) , 0# ∙ B
  ∎
\end{code}

Linear maps preserve scaling.

\begin{code}
*⟩-assoc : ∀ {γ δ} (Γ : Context γ) (Ξ : Matrix γ δ) (π : Mult)

  -----------------------------------
  → (π *̇ Γ) *⟩ Ξ ≡ π *̇ (Γ *⟩ Ξ)

*⟩-assoc {γ} {δ} ∅ Ξ π =
  begin
    0s
  ≡⟨ *̇-zeroʳ π ⟩
    π *̇ 0s
  ∎

*⟩-assoc {γ} {δ} (Γ , π′ ∙ A) Ξ π =
  begin
    ((π * π′) *̇ Ξ Z) +̇ ((π *̇ Γ) *⟩ (Ξ ∘ S_))
  ≡⟨ *⟩-assoc Γ (Ξ ∘ S_) π |> cong ((π * π′) *̇ Ξ Z +̇_) ⟩
    ((π * π′) *̇ Ξ Z) +̇ (π *̇ (Γ *⟩ (Ξ ∘ S_)))
  ≡⟨ *̇-assoc (Ξ Z) |> cong (_+̇ (π *̇ (Γ *⟩ (Ξ ∘ S_)))) ⟩
    (π *̇ (π′ *̇ Ξ Z)) +̇ (π *̇ (Γ *⟩ (Ξ ∘ S_)))
  ≡⟨ *̇-distribˡ-+̇ (π′ *̇ Ξ Z) (Γ *⟩ (Ξ ∘ S_)) π |> sym ⟩
    π *̇ (π′ *̇ Ξ Z +̇ Γ *⟩ (Ξ ∘ S_))
  ∎
\end{code}

Linear maps distribute over sums.

\begin{code}
*⟩-distribʳ-+̇ : ∀ {γ} {δ} (Γ₁ Γ₂ : Context γ) (Ξ : Matrix γ δ)

  ----------------------------------
  → (Γ₁ +̇ Γ₂) *⟩ Ξ ≡ Γ₁ *⟩ Ξ +̇ Γ₂ *⟩ Ξ

*⟩-distribʳ-+̇ ∅ ∅ Ξ =
  begin
    0s
  ≡⟨ sym (+̇-identityʳ 0s) ⟩
    0s +̇ 0s
  ∎

*⟩-distribʳ-+̇ (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) Ξ =
  begin
    (π₁ + π₂) *̇ Ξ Z +̇ (Γ₁ +̇ Γ₂) *⟩ (Ξ ∘ S_)
  ≡⟨ *⟩-distribʳ-+̇ Γ₁ Γ₂ (Ξ ∘ S_) |> cong ((π₁ + π₂) *̇ Ξ Z +̇_) ⟩
    (π₁ + π₂) *̇ Ξ Z +̇ (Γ₁ *⟩ (Ξ ∘ S_) +̇ Γ₂ *⟩ (Ξ ∘ S_))
  ≡⟨ *̇-distribʳ-+̇ (Ξ Z) π₁ π₂ |> cong (_+̇ (Γ₁ *⟩ (Ξ ∘ S_) +̇ Γ₂ *⟩ (Ξ ∘ S_))) ⟩
    (π₁ *̇ Ξ Z +̇ π₂ *̇ Ξ Z) +̇ (Γ₁ *⟩ (Ξ ∘ S_) +̇ Γ₂ *⟩ (Ξ ∘ S_))
  ≡⟨ +̇-assoc (π₁ *̇ Ξ Z +̇ π₂ *̇ Ξ Z) (Γ₁ *⟩ (Ξ ∘ S_)) (Γ₂ *⟩ (Ξ ∘ S_)) |> sym ⟩
    ((π₁ *̇ Ξ Z +̇ π₂ *̇ Ξ Z) +̇ Γ₁ *⟩ (Ξ ∘ S_)) +̇ Γ₂ *⟩ (Ξ ∘ S_)
  ≡⟨ +̇-assoc (π₁ *̇ Ξ Z) (π₂ *̇ Ξ Z) (Γ₁ *⟩ (Ξ ∘ S_)) |> cong (_+̇ Γ₂ *⟩ (Ξ ∘ S_)) ⟩
    (π₁ *̇ Ξ Z +̇ (π₂ *̇ Ξ Z +̇ Γ₁ *⟩ (Ξ ∘ S_))) +̇ Γ₂ *⟩ (Ξ ∘ S_)
  ≡⟨ +̇-comm (π₂ *̇ Ξ Z) (Γ₁ *⟩ (Ξ ∘ S_)) |> cong ((_+̇ Γ₂ *⟩ (Ξ ∘ S_)) ∘ (π₁ *̇ Ξ Z +̇_)) ⟩
    (π₁ *̇ Ξ Z +̇ (Γ₁ *⟩ (Ξ ∘ S_) +̇ π₂ *̇ Ξ Z)) +̇ Γ₂ *⟩ (Ξ ∘ S_)
  ≡⟨ +̇-assoc (π₁ *̇ Ξ Z) (Γ₁ *⟩ (Ξ ∘ S_)) (π₂ *̇ Ξ Z) |> sym ∘ cong (_+̇ Γ₂ *⟩ (Ξ ∘ S_)) ⟩
    ((π₁ *̇ Ξ Z +̇ Γ₁ *⟩ (Ξ ∘ S_)) +̇ π₂ *̇ Ξ Z) +̇ Γ₂ *⟩ (Ξ ∘ S_)
  ≡⟨ +̇-assoc (π₁ *̇ Ξ Z +̇ Γ₁ *⟩ (Ξ ∘ S_)) (π₂ *̇ Ξ Z) (Γ₂ *⟩ (Ξ ∘ S_)) ⟩
    (π₁ *̇ Ξ Z +̇ Γ₁ *⟩ (Ξ ∘ S_)) +̇ (π₂ *̇ Ξ Z +̇ Γ₂ *⟩ (Ξ ∘ S_))
  ∎
\end{code}

Multiplying by a standard basis vector projects out the corresponding column of the matrix.

\begin{code}
*⟩-identityˡ : ∀ {γ δ} {A} (Ξ : Matrix γ δ)

  → (x : γ ∋ A)
  -----------------------
  → identity x *⟩ Ξ ≡ Ξ x

*⟩-identityˡ {γ , A} {δ} {A} Ξ Z =
  begin
    identity Z *⟩ Ξ
  ≡⟨⟩
    1# *̇ Ξ Z +̇ 0s *⟩ (Ξ ∘ S_)
  ≡⟨ *⟩-zeroˡ (Ξ ∘ S_) |> cong ((1# *̇ Ξ Z) +̇_) ⟩
    1# *̇ Ξ Z +̇ 0s
  ≡⟨ +̇-identityʳ (1# *̇ Ξ Z) ⟩
    1# *̇ Ξ Z
  ≡⟨ *̇-identityˡ (Ξ Z) ⟩
    Ξ Z
  ∎

*⟩-identityˡ {γ , B} {δ} {A} Ξ (S x) =
  begin
    identity (S x) *⟩ Ξ
  ≡⟨⟩
    0# *̇ Ξ Z +̇ identity x *⟩ (Ξ ∘ S_)
  ≡⟨ *⟩-identityˡ (Ξ ∘ S_) x |> cong (0# *̇ Ξ Z +̇_) ⟩
    0# *̇ Ξ Z +̇ Ξ (S x)
  ≡⟨ *̇-zeroˡ (Ξ Z) |> cong (_+̇ Ξ (S x)) ⟩
    0s +̇ Ξ (S x)
  ≡⟨ +̇-identityˡ (Ξ (S x)) ⟩
    Ξ (S x)
  ∎
\end{code}

The standard basis vectors put together give the identity matrix.

\begin{code}
*⟩-identityʳ : ∀ {γ} (Γ : Context γ)

  -------------------
  → Γ *⟩ identity ≡ Γ

*⟩-identityʳ {γ} ∅ = refl
*⟩-identityʳ {γ , .A} (Γ , π ∙ A) =
  begin
    (π *̇ 0s , π * 1# ∙ A) +̇ (Γ *⟩ (λ x → identity x , 0# ∙ A))
  ≡⟨ *⟩-zeroʳ Γ identity |> cong ((π *̇ 0s , π * 1# ∙ A) +̇_) ⟩
    (π *̇ 0s , π * 1# ∙ A) +̇ (Γ *⟩ identity , 0# ∙ A)
  ≡⟨ *⟩-identityʳ Γ |> cong (((π *̇ 0s , π * 1# ∙ A) +̇_) ∘ (_, 0# ∙ A)) ⟩
    (π *̇ 0s , π * 1# ∙ A) +̇ (Γ , 0# ∙ A)
  ≡⟨⟩
    π *̇ 0s +̇ Γ , (π * 1#) + 0# ∙ A
  ≡⟨ +-identityʳ (π * 1#) |> cong ((π *̇ 0s +̇ Γ) ,_∙ A) ⟩
    π *̇ 0s +̇ Γ , π * 1# ∙ A
  ≡⟨ *-identityʳ π |> cong ((π *̇ 0s +̇ Γ) ,_∙ A) ⟩
    π *̇ 0s +̇ Γ , π ∙ A
  ≡⟨ *̇-zeroʳ π |> cong ((_, π ∙ A) ∘ (_+̇ Γ)) ∘ sym ⟩
    0s +̇ Γ , π ∙ A
  ≡⟨ +̇-identityˡ Γ |> cong (_, π ∙ A) ⟩
    Γ , π ∙ A
  ∎
\end{code}


# Renaming

\begin{code}
ext : ∀ {γ δ}

  → (∀ {A}   →     γ ∋ A →     δ ∋ A)
    ---------------------------------
  → (∀ {A B} → γ , B ∋ A → δ , B ∋ A)

ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
\end{code}

\begin{code}
lem-` : ∀ {γ δ} {A} {Ξ : Matrix γ δ} (x : γ ∋ A) → _
lem-` {γ} {δ} {A} {Ξ} x =
  begin
    Ξ x
  ≡⟨ *⟩-identityˡ Ξ x |> sym ⟩
    identity x *⟩ Ξ
  ∎
\end{code}

\begin{code}
lem-ƛ : ∀ {γ δ} (Γ : Context γ) {A} {π} {Ξ : Matrix γ δ} → _
lem-ƛ {γ} {δ} Γ {A} {π} {Ξ} =
  begin
    (π *̇ 0s , π * 1# ∙ A) +̇ (Γ *⟩ (λ x → Ξ x , 0# ∙ A))
  ≡⟨ *⟩-zeroʳ Γ Ξ |> cong ((π *̇ 0s , π * 1# ∙ A) +̇_) ⟩
    (π *̇ 0s , π * 1# ∙ A) +̇ (Γ *⟩ Ξ , 0# ∙ A)
  ≡⟨⟩
    π *̇ 0s +̇ Γ *⟩ Ξ , (π * 1#) + 0# ∙ A
  ≡⟨ *̇-zeroʳ π |> cong ((_, (π * 1#) + 0# ∙ A) ∘ (_+̇ Γ *⟩ Ξ)) ∘ sym ⟩
    0s +̇ Γ *⟩ Ξ , (π * 1#) + 0# ∙ A
  ≡⟨ +̇-identityˡ (Γ *⟩ Ξ) |> cong (_, (π * 1#) + 0# ∙ A) ⟩
    Γ *⟩ Ξ , (π * 1#) + 0# ∙ A
  ≡⟨ +-identityʳ (π * 1#) |> cong (Γ *⟩ Ξ ,_∙ A) ⟩
    Γ *⟩ Ξ , π * 1# ∙ A
  ≡⟨ *-identityʳ π |> cong (Γ *⟩ Ξ ,_∙ A) ⟩
    Γ *⟩ Ξ , π ∙ A
  ∎
\end{code}

\begin{code}
lem-· : ∀ {γ δ} (Γ Δ : Context γ) {π} {Ξ : Matrix γ δ} → _
lem-· {γ} {δ} Γ Δ {π} {Ξ} =
  begin
    Γ *⟩ Ξ +̇ π *̇ (Δ *⟩ Ξ)
  ≡⟨ *⟩-assoc Δ Ξ π |> cong (Γ *⟩ Ξ +̇_) ∘ sym ⟩
    Γ *⟩ Ξ +̇ (π *̇ Δ) *⟩ Ξ
  ≡⟨ *⟩-distribʳ-+̇ Γ (π *̇ Δ) Ξ |> sym ⟩
    (Γ +̇ π *̇ Δ) *⟩ Ξ ∎
\end{code}

\begin{code}
lem-, : ∀ {γ δ} (Γ Δ : Context γ) {Ξ : Matrix γ δ} → _
lem-, {γ} {δ} Γ Δ {Ξ} =
  begin
    Γ *⟩ Ξ +̇ Δ *⟩ Ξ
  ≡⟨ *⟩-distribʳ-+̇ Γ Δ Ξ |> sym ⟩
    (Γ +̇ Δ) *⟩ Ξ
  ∎
\end{code}

\begin{code}
lem-case⊗ : ∀ {γ δ} (Γ : Context γ) {A B} {Ξ : Matrix γ δ} → _
lem-case⊗ {γ} {δ} Γ {A} {B} {Ξ} =
  let
    lem1 : ∀ {γ} (Γ : Context γ) → _
    lem1 {γ} Γ =
      begin
        (1# *̇ 0s) +̇ Γ
      ≡⟨ *̇-identityˡ 0s |> cong (_+̇ Γ) ⟩
        0s +̇ Γ
      ≡⟨ +̇-identityˡ Γ ⟩
        Γ
      ∎
  in
    begin

      (1# *̇ 0s , 1# * 0# ∙ A , 1# * 1# ∙ B) +̇ ((1# *̇ 0s , 1# * 1# ∙ A , 1# * 0# ∙ B) +̇ Γ *⟩ (λ x → Ξ x , 0# ∙ A , 0# ∙ B))

    -- Step 1. Move the three occurrences of A and B to the top-level.
    ≡⟨ trans (*⟩-zeroʳ Γ (λ x → Ξ x , 0# ∙ A)) (*⟩-zeroʳ Γ Ξ |> cong (_, 0# ∙ B))
      |> cong (((1# *̇ 0s , 1# * 0# ∙ A , 1# * 1# ∙ B) +̇_) ∘ ((1# *̇ 0s , 1# * 1# ∙ A , 1# * 0# ∙ B) +̇_)) ⟩

      (1# *̇ 0s) +̇ ((1# *̇ 0s) +̇ (Γ *⟩ Ξ)) , (1# * 0#) + ((1# * 1#) + 0#) ∙ A , (1# * 1#) + ((1# * 0#) + 0#) ∙ B

    -- Step 2. Remove the empty environments (1# *̇ 0s).
    ≡⟨ trans (lem1 (Γ *⟩ Ξ) |> cong (1# *̇ 0s +̇_)) (lem1 (Γ *⟩ Ξ))
      |> cong ((_, (1# * 1#) + ((1# * 0#) + 0#) ∙ B) ∘ (_, (1# * 0#) + ((1# * 1#) + 0#) ∙ A)) ⟩

      Γ *⟩ Ξ , (1# * 0#) + ((1# * 1#) + 0#) ∙ A , (1# * 1#) + ((1# * 0#) + 0#) ∙ B

    -- Step 3. Reduce the complex sum for the usage of B to 1#.
    ≡⟨ trans (trans (+-identityʳ (1# * 0#)) (*-identityˡ 0#) |> cong ((1# * 1#) +_)) (trans (+-identityʳ (1# * 1#)) (*-identityˡ 1#))
      |> cong (Γ *⟩ Ξ , (1# * 0#) + ((1# * 1#) + 0#) ∙ A ,_∙ B) ⟩

      Γ *⟩ Ξ , (1# * 0#) + ((1# * 1#) + 0#) ∙ A , 1# ∙ B

    -- Step 4. Reduce the complex sum for the usage of A to 1#.
    ≡⟨ trans (*-identityˡ 0# |> cong (_+ ((1# * 1#) + 0#))) (trans (+-identityˡ ((1# * 1#) + 0#)) (trans (+-identityʳ (1# * 1#)) (*-identityʳ 1#)))
      |> cong ((_, 1# ∙ B) ∘ (Γ *⟩ Ξ ,_∙ A)) ⟩

      Γ *⟩ Ξ , 1# ∙ A , 1# ∙ B

    ∎
\end{code}

\begin{code}
lem-⟨⟩ : ∀ {γ δ} {Ξ : Matrix δ γ} → _
lem-⟨⟩ {γ} {δ} {Ξ} =
  begin
    0s {γ}
  ≡⟨ *⟩-zeroˡ Ξ |> sym ⟩
    0s {δ} *⟩ Ξ
  ∎
\end{code}

\begin{code}
lem-case⊕ : ∀ {γ δ} (Γ : Context γ) {A : Type} {Ξ : Matrix γ δ} → _
lem-case⊕ {γ} {δ} Γ {A} {Ξ} =
  begin
    (1# *̇ 0s , 1# * 1# ∙ A) +̇ Γ *⟩ (λ x → Ξ x , 0# ∙ A)
  ≡⟨ *̇-identityˡ 0s |> cong ((_+̇ Γ *⟩ (λ x → Ξ x , 0# ∙ A)) ∘ (_, 1# * 1# ∙ A)) ⟩
    (0s , 1# * 1# ∙ A) +̇ Γ *⟩ (λ x → Ξ x , 0# ∙ A)
  ≡⟨ *-identityˡ 1# |> cong ((_+̇ Γ *⟩ (λ x → Ξ x , 0# ∙ A)) ∘ (0s ,_∙ A)) ⟩
    (0s , 1# ∙ A) +̇ Γ *⟩ (λ x → Ξ x , 0# ∙ A)
  ≡⟨ *⟩-zeroʳ Γ Ξ |> cong (( 0s , 1# ∙ A) +̇_) ⟩
    (0s , 1# ∙ A) +̇ (Γ *⟩ Ξ , 0# ∙ A)
  ≡⟨⟩
    (0s +̇ Γ *⟩ Ξ) , 1# + 0# ∙ A
  ≡⟨ +̇-identityˡ (Γ *⟩ Ξ) |> cong (_, 1# + 0# ∙ A) ⟩
    Γ *⟩ Ξ , 1# + 0# ∙ A
  ≡⟨ +-identityʳ 1# |> cong (Γ *⟩ Ξ ,_∙ A) ⟩
    Γ *⟩ Ξ , 1# ∙ A
  ∎
\end{code}

\begin{code}
rename : ∀ {γ δ} {Γ : Context γ} {B}

  → (ρ : ∀ {A} → γ ∋ A → δ ∋ A)
  → Γ ⊢ B
    ---------------------------
  → Γ *⟩ (identity ∘ ρ) ⊢ B

rename ρ (` x) =
  Eq.subst (_⊢ _) (lem-` x) (` ρ x)
rename ρ (ƛ_  {Γ = Γ} N) =
  ƛ (Eq.subst (_⊢ _) (lem-ƛ Γ) (rename (ext ρ) N))
rename ρ (_·_ {Γ = Γ} {Δ = Δ} L M) =
  Eq.subst (_⊢ _) (lem-· Γ Δ) (rename ρ L · rename ρ M)
rename ρ ⟨⟩ =
  Eq.subst (_⊢ _) (lem-⟨⟩ {Ξ = identity ∘ ρ}) ⟨⟩
rename ρ (case1 {Γ = Γ} {Δ = Δ} L N) =
  Eq.subst (_⊢ _) (lem-, Γ Δ) (case1 (rename ρ L) (rename ρ N))
rename ρ (⟨_,_⟩ {Γ = Γ} {Δ = Δ} L M) =
  Eq.subst (_⊢ _) (lem-, Γ Δ) ⟨ rename ρ L , rename ρ M ⟩
rename ρ (case⊗ {Γ = Γ} {Δ = Δ} L N) =
  Eq.subst (_⊢ _) (lem-, Γ Δ) (case⊗ (rename ρ L) (Eq.subst (_⊢ _) (lem-case⊗ Δ) (rename (ext (ext ρ)) N)))
rename ρ (inj₁ {Γ = Γ} L) =
  inj₁ (rename ρ L)
rename ρ (inj₂ {Γ = Γ} L) =
  inj₂ (rename ρ L)
rename ρ (case⊕ {Γ = Γ} {Δ = Δ} L M N) =
  Eq.subst (_⊢ _) (lem-, Γ Δ) (case⊕ (rename ρ L) (Eq.subst (_⊢ _) (lem-case⊕ Δ) (rename (ext ρ) M)) (Eq.subst (_⊢ _) (lem-case⊕ Δ) (rename (ext ρ) N)))
\end{code}


# Simultaneous Substitution

Extend a matrix as the identity matrix -- add a zero to the end of every row, and add a new row with a 1 and the rest 0s.

\begin{code}
extm : ∀ {γ δ}

  → Matrix γ δ
    --------------------------------
  → (∀ {B} → Matrix (γ , B) (δ , B))

extm Ξ {B} {A} Z     = identity Z
extm Ξ {B} {A} (S x) = Ξ x , 0# ∙ B
\end{code}

\begin{code}
exts : ∀ {γ δ} {Ξ : Matrix γ δ}

  → (∀ {A}   → (x :     γ ∋ A) →      Ξ x ⊢ A)
    ------------------------------------------
  → (∀ {A B} → (x : γ , B ∋ A) → extm Ξ x ⊢ A)

exts {Ξ = Ξ} σ {A} {B} Z     = ` Z
exts {Ξ = Ξ} σ {A} {B} (S x) = Eq.subst (_⊢ A) lem (rename S_ (σ x))
  where
    lem =
      begin
        Ξ x *⟩ (identity ∘ S_)
     ≡⟨⟩
       Ξ x *⟩ (λ x → identity x , 0# ∙ B)
     ≡⟨ *⟩-zeroʳ (Ξ x) identity ⟩
       (Ξ x *⟩ identity) , 0# ∙ B
     ≡⟨ *⟩-identityʳ (Ξ x) |> cong (_, 0# ∙ B) ⟩
       Ξ x , 0# ∙ B
     ∎
\end{code}

\begin{code}
subst : ∀ {γ δ} {Γ : Context γ} {Ξ : Matrix γ δ} {B}

  → (σ : ∀ {A} → (x : γ ∋ A) → Ξ x ⊢ A)
  → Γ ⊢ B
    --------------------------------------
  → Γ *⟩ Ξ ⊢ B

subst {Ξ = Ξ} σ (` x) =
  Eq.subst (_⊢ _) (lem-` x) (σ x)
subst {Ξ = Ξ} σ (ƛ_  {Γ = Γ} N) =
  ƛ (Eq.subst (_⊢ _) (lem-ƛ Γ) (subst (exts σ) N))
subst {Ξ = Ξ} σ (_·_ {Γ = Γ} {Δ = Δ} L M) =
  Eq.subst (_⊢ _) (lem-· Γ Δ)(subst σ L · subst σ M)
subst {Ξ = Ξ} σ ⟨⟩ =
  Eq.subst (_⊢ _) (lem-⟨⟩ {Ξ = Ξ}) ⟨⟩
subst {Ξ = Ξ} σ (case1 {Γ = Γ} {Δ = Δ} L N) =
  Eq.subst (_⊢ _) (lem-, Γ Δ) (case1 (subst σ L) (subst σ N))
subst {Ξ = Ξ} σ (⟨_,_⟩ {Γ = Γ} {Δ = Δ} L M) =
  Eq.subst (_⊢ _) (lem-, Γ Δ) ⟨ subst σ L , subst σ M ⟩
subst {Ξ = Ξ} σ (case⊗ {Γ = Γ} {Δ = Δ} L N) =
  Eq.subst (_⊢ _) (lem-, Γ Δ) (case⊗ (subst σ L) (Eq.subst (_⊢ _) (lem-case⊗ Δ) (subst (exts (exts σ)) N)))
subst {Ξ = Ξ} σ (inj₁ {Γ = Γ} L) =
  inj₁ (subst σ L)
subst {Ξ = Ξ} σ (inj₂ {Γ = Γ} L) =
  inj₂ (subst σ L)
subst {Ξ = Ξ} σ (case⊕ {Γ = Γ} {Δ = Δ} L M N) =
  Eq.subst (_⊢ _) (lem-, Γ Δ) (case⊕ (subst σ L) (Eq.subst (_⊢ _) (lem-case⊕ Δ) (subst (exts σ) M)) (Eq.subst (_⊢ _) (lem-case⊕ Δ) (subst (exts σ) N)))
\end{code}


# Values

\begin{code}
data Value : ∀ {γ} {Γ : Context γ} {A} → Γ ⊢ A → Set where

  V-ƛ    : ∀ {γ} {Γ : Context γ} {A B} {π} {N : Γ , π ∙ A ⊢ B}

      -----------
    → Value (ƛ N)

  V-⟨⟩   : ∀ {γ}

      --------------
    → Value (⟨⟩ {γ})

  V-,    : ∀ {γ} {Γ Δ : Context γ} {A B} {L : Γ ⊢ A} {M : Δ ⊢ B}

    → Value L
    → Value M
      ---------------
    → Value ⟨ L , M ⟩

  V-inj₁ : ∀ {γ} {Γ : Context γ} {A B} {L : Γ ⊢ A}

    → Value L
      --------------
    → Value (inj₁ {B = B} L)

  V-inj₂ : ∀ {γ} {Γ : Context γ} {A B} {L : Γ ⊢ B}

    → Value L
      --------------
    → Value (inj₂ {A = A} L)
\end{code}


# Single Substitution

\begin{code}
_⊸[_] : ∀ {γ} {Γ Δ : Context γ} {A B} {π}

  → Γ , π ∙ B ⊢ A
  → Δ ⊢ B
    --------------
  → Γ +̇ π *̇ Δ ⊢ A

_⊸[_] {γ} {Γ} {Δ} {A} {B} {π} N M = Eq.subst (_⊢ _) lem (subst σ′ N)
  where
    Ξ′ : Matrix (γ , B) γ
    Ξ′ Z     = Δ
    Ξ′ (S x) = identity x
    σ′ : ∀ {A} → (x : γ , B ∋ A) → Ξ′ x ⊢ A
    σ′ Z     = M
    σ′ (S x) = ` x

    lem =
      begin
        π *̇ Δ +̇ Γ *⟩ identity
      ≡⟨ +̇-comm (π *̇ Δ) (Γ *⟩ identity) ⟩
        Γ *⟩ identity +̇ π *̇ Δ
      ≡⟨ *⟩-identityʳ Γ |> cong (_+̇ π *̇ Δ) ⟩
       Γ +̇ π *̇ Δ
      ∎
\end{code}

\begin{code}
_1[_] : ∀ {γ} {Γ Δ : Context γ} {A} {V : Γ ⊢ `1}

  → Δ ⊢ A
  → Value V
    ---------
  → Γ +̇ Δ ⊢ A

_1[_] {Δ = Δ}  N V-⟨⟩ = Eq.subst (_⊢ _) lem N
  where
    lem =
      begin
        Δ
      ≡⟨ +̇-identityˡ Δ |> sym ⟩
        0s +̇ Δ
      ∎
\end{code}

\begin{code}
_⊗[_][_] : ∀ {γ} {Γ Δ Θ : Context γ} {A B C}

  → Θ , 1# ∙ A , 1# ∙ B ⊢ C
  → Γ ⊢ A
  → Δ ⊢ B
    ---------------
  → Γ +̇ Δ +̇ Θ ⊢ C

_⊗[_][_] {γ} {Γ} {Δ} {Θ} {A} {B} {C} N L M = Eq.subst (_⊢ _) lem (subst σ′ N)
  where
    Ξ′ : Matrix (γ , A , B) γ
    Ξ′ Z         = Δ
    Ξ′ (S Z)     = Γ
    Ξ′ (S (S x)) = identity x
    σ′ : ∀ {D} → (x : γ , A , B ∋ D) → Ξ′ x ⊢ D
    σ′ Z         = M
    σ′ (S Z)     = L
    σ′ (S (S x)) = ` x

    lem =
      begin
        1# *̇ Δ +̇ (1# *̇ Γ +̇ Θ *⟩ identity)
      ≡⟨ *⟩-identityʳ Θ |> cong ((1# *̇ Δ +̇_) ∘ (1# *̇ Γ +̇_)) ⟩
        1# *̇ Δ +̇ (1# *̇ Γ +̇ Θ)
      ≡⟨ *̇-identityˡ Γ |> cong ((1# *̇ Δ +̇_) ∘ (_+̇ Θ)) ⟩
        1# *̇ Δ +̇ (Γ +̇ Θ)
      ≡⟨ *̇-identityˡ Δ |> cong (_+̇ (Γ +̇ Θ)) ⟩
        Δ +̇ (Γ +̇ Θ)
      ≡⟨ +̇-assoc Δ Γ Θ |> sym ⟩
        (Δ +̇ Γ) +̇ Θ
      ≡⟨ +̇-comm Δ Γ |> cong (_+̇ Θ) ⟩
        (Γ +̇ Δ) +̇ Θ
      ∎
\end{code}

\begin{code}
_⊕[_] : ∀ {γ} {Γ Δ : Context γ} {A B}

  → Δ , 1# ∙ B ⊢ A
  → Γ ⊢ B
    --------------
  → Γ +̇ Δ ⊢ A

_⊕[_] {γ} {Γ} {Δ} {A} {B} N M = Eq.subst (_⊢ _) lem (N ⊸[ M ])
  where
    lem =
      begin
        Δ +̇ 1# *̇ Γ
      ≡⟨ *̇-identityˡ Γ |> cong (Δ +̇_) ⟩
        Δ +̇ Γ
      ≡⟨ +̇-comm Δ Γ ⟩
        Γ +̇ Δ
      ∎
\end{code}


# Reduction

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {γ} {Γ : Context γ} {A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {γ} {Γ Δ : Context γ} {A B} {π} {L L′ : Γ ⊢ [ π ∙ A ]⊸ B} {M : Δ ⊢ A}

       → L —→ L′
        -----------------
       → L · M —→ L′ · M

  ξ-·₂ : ∀ {γ} {Γ Δ : Context γ} {A B} {π} {V : Γ ⊢ [ π ∙ A ]⊸ B} {M M′ : Δ ⊢ A}

       → Value V
       → M —→ M′
         --------------
       → V · M —→ V · M′

  ξ-case1 : ∀ {γ} {Γ Δ : Context γ} {A} {L L′ : Γ ⊢ `1} {M : Δ ⊢ A}

       → L —→ L′
         -----------------------
       → case1 L M —→ case1 L′ M

  ξ-,₁ : ∀ {γ} {Γ Δ : Context γ} {A B} {L L′ : Γ ⊢ A} {M : Δ ⊢ B}

       → L —→ L′
         -----------------------
       → ⟨ L , M ⟩ —→ ⟨ L′ , M ⟩

  ξ-,₂ : ∀ {γ} {Γ Δ : Context γ} {A B} {V : Γ ⊢ A} {M M′ : Δ ⊢ B}

       → Value V
       → M —→ M′
         -----------------------
       → ⟨ V , M ⟩ —→ ⟨ V , M′ ⟩

  ξ-case⊗ : ∀ {γ} {Γ Δ : Context γ} {A B C} {L L′ : Γ ⊢ A ⊗ B} {N : Δ , 1# ∙ A , 1# ∙ B ⊢ C}

       → L —→ L′
         ------------------------
       → case⊗ L N —→ case⊗ L′ N

  ξ-inj₁ : ∀ {γ} {Γ : Context γ} {A B} {L L′ : Γ ⊢ A}

       → L —→ L′
         ---------------------------------
       → inj₁ {B = B} L —→ inj₁ {B = B} L′

  ξ-inj₂ : ∀ {γ} {Γ : Context γ} {A B} {L L′ : Γ ⊢ B}

       → L —→ L′
         ---------------------------------
       → inj₂ {A = A} L —→ inj₂ {A = A} L′

  ξ-case⊕ : ∀ {γ} {Γ Δ : Context γ} {A B C} {L L′ : Γ ⊢ A ⊕ B} {M : Δ , 1# ∙ A ⊢ C} {N : Δ , 1# ∙ B ⊢ C}

       → L —→ L′
         ---------------------------
       → case⊕ L M N —→ case⊕ L′ M N

  β-⊸  : ∀ {γ} {Γ Δ : Context γ} {A B} {π} {N : Γ , π ∙ A ⊢ B} {W : Δ ⊢ A}

       → (VW : Value W)
         --------------------
       → (ƛ N) · W —→ N ⊸[ W ]

  β-1  : ∀ {γ} {Γ Δ : Context γ} {A} {V : Γ ⊢ `1} {N : Δ ⊢ A}

       → (VV : Value V)
         ----------------------
       → case1 V N —→ N 1[ VV ]

  β-⊗  : ∀ {γ} {Γ Δ Θ : Context γ} {A B C} {V : Γ ⊢ A} {W : Δ ⊢ B} {N : Θ , 1# ∙ A , 1# ∙ B ⊢ C}

       → (VV : Value V)
       → (VW : Value W)
         ---------------------------------
       → case⊗ ⟨ V , W ⟩ N —→ N ⊗[ V ][ W ]

  β-⊕₁ : ∀ {γ} {Γ Δ : Context γ} {A B C} {V : Γ ⊢ A} {M : Δ , 1# ∙ A ⊢ C} {N : Δ , 1# ∙ B ⊢ C}

       → (VV : Value V)
         -----------------------------
       → case⊕ (inj₁ V) M N —→ M ⊕[ V ]


  β-⊕₂ : ∀ {γ} {Γ Δ : Context γ} {A B C} {V : Γ ⊢ B} {M : Δ , 1# ∙ A ⊢ C} {N : Δ , 1# ∙ B ⊢ C}

       → (VV : Value V)
         -----------------------------
       → case⊕ (inj₂ V) M N —→ N ⊕[ V ]
\end{code}


# Progress

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
    go refl (ƛ N)               = done V-ƛ
    go refl (L · M)       with go refl L
    ...    | step L—→L′         = step (ξ-·₁ L—→L′)
    ...    | done V-ƛ     with go refl M
    ...        | step M—→M′     = step (ξ-·₂ V-ƛ M—→M′)
    ...        | done V-M       = step (β-⊸ V-M)
    go refl ⟨⟩                  = done V-⟨⟩
    go refl (case1 L N)   with go refl L
    ...    | step L—→L′         = step (ξ-case1 L—→L′)
    ...    | done V-L           = step (β-1 V-L)
    go refl ⟨ L , M ⟩     with go refl L
    ...    | step L—→L′         = step (ξ-,₁ L—→L′)
    ...    | done V-L     with go refl M
    ...        | step M—→M′     = step (ξ-,₂ V-L M—→M′)
    ...        | done V-M       = done (V-, V-L V-M)
    go refl (case⊗ L N)   with go refl L
    ...    | step L—→L′         = step (ξ-case⊗ L—→L′)
    ...    | done (V-, V-L V-M) = step (β-⊗ V-L V-M)
    go refl (inj₁ L)      with go refl L
    ...    | step L—→L′         = step (ξ-inj₁ L—→L′)
    ...    | done V-L           = done (V-inj₁ V-L)
    go refl (inj₂ L)      with go refl L
    ...    | step L—→L′         = step (ξ-inj₂ L—→L′)
    ...    | done V-L           = done (V-inj₂ V-L)
    go refl (case⊕ L M N) with go refl L
    ...    | step L—→L′         = step (ξ-case⊕ L—→L′)
    ...    | done (V-inj₁ V-L)  = step (β-⊕₁ V-L)
    ...    | done (V-inj₂ V-L)  = step (β-⊕₂ V-L)
\end{code}
