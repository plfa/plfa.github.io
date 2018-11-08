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
infix  1 _⊢₁_
infix  1 _⊢_
infix  1 _∋_
infixl 5 _,_
infixl 5 _,_∙_
infixr 6 [_∙_]⊸_
infixr 8 _++_
infixl 9 _**_
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

\begin{code}
_**_ : ∀ {γ} → Mult → Context γ → Context γ
π ** ∅ = ∅
π ** (Γ , ρ ∙ A) = π ** Γ , π * ρ ∙ A
\end{code}

\begin{code}
**-identity : ∀ {γ} (Γ : Context γ)

  -------------
  → 1# ** Γ ≡ Γ

**-identity ∅ = refl
**-identity (Γ , π ∙ A) rewrite **-identity Γ = refl
\end{code}

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

\begin{code}
0∙_ : ∀ γ → Context γ
0∙  ∅      = ∅
0∙ (γ , A) = 0∙ γ , 0# ∙ A
\end{code}

\begin{code}
0∙-absorb : ∀ γ π

  --------------------
  → 0∙ γ ≡ π ** (0∙ γ)

0∙-absorb ∅ π =
  begin
    ∅
    ≡⟨⟩
    ∅
  ∎

0∙-absorb (γ , A) π =
  begin
    (0∙ γ) , 0# ∙ A
  ≡⟨ cong ((0∙ γ) ,_∙ A) (sym (*-zeroʳ π)) ⟩
    (0∙ γ) , π * 0# ∙ A
  ≡⟨ cong (_, π * 0# ∙ A) (0∙-absorb γ π) ⟩
    π ** (0∙ γ) , π * 0# ∙ A
  ∎
\end{code}

\begin{code}
0**Γ≡0∙γ : ∀ {γ} (Γ : Context γ)

  -----------------
  → 0# ** Γ ≡ 0∙ γ

0**Γ≡0∙γ ∅ = refl
0**Γ≡0∙γ (Γ , π ∙ A) rewrite 0**Γ≡0∙γ Γ = refl
\end{code}

\begin{code}
_++_ : ∀ {γ} → Context γ → Context γ → Context γ
∅ ++ ∅ = ∅
(Γ₁ , π₁ ∙ A) ++ (Γ₂ , π₂ ∙ .A) = Γ₁ ++ Γ₂ , π₁ + π₂ ∙ A
\end{code}

\begin{code}
++-identityˡ : ∀ {γ} (Γ : Context γ)

  ---------------
  → 0∙ γ ++ Γ ≡ Γ

++-identityˡ ∅ = refl
++-identityˡ (Γ , π ∙ A) rewrite ++-identityˡ Γ | +-identityʳ π = refl
\end{code}

\begin{code}
++-identityʳ : ∀ {γ} (Γ : Context γ)

  ---------------
  → Γ ++ 0∙ γ ≡ Γ

++-identityʳ ∅ = refl
++-identityʳ (Γ , π ∙ A) rewrite ++-identityʳ Γ | +-identityʳ π = refl
\end{code}

\begin{code}
VC : ∀ {A} {γ : Precontext} → γ ∋ A → Context γ
VC {γ = γ , A} Z     = 0∙ γ , 1# ∙ A
VC {γ = γ , B} (S x) = VC x , 0# ∙ B
\end{code}

\begin{code}
smash : ∀ {γ δ}

  → (Γ : Context γ)
  → (Δ : ∀ {A} → γ ∋ A → Context δ)
  → Context δ

smash {δ = δ} ∅           Δ = 0∙ δ
smash {δ = δ} (Γ , π ∙ A) Δ = (π ** Δ Z) ++ smash Γ (Δ ∘ S_)
\end{code}

\begin{code}
smash-0∙ : ∀ {γ δ}

  → (Δ : ∀ {A} → (γ ∋ A → Context δ))
  -----------------------------------
  → smash (0∙ γ) Δ ≡ 0∙ δ

smash-0∙ {∅}     {δ} Δ = refl
smash-0∙ {γ , A} {δ} Δ =
  begin
    smash (0∙ (γ , A)) Δ
  ≡⟨⟩
    0# ** Δ Z ++ smash (0∙ γ) (Δ ∘ S_)
  ≡⟨ cong (0# ** Δ Z ++_) (smash-0∙ {γ} (Δ ∘ S_)) ⟩
    0# ** Δ Z ++ (0∙ δ)
  ≡⟨ cong (_++ (0∙ δ)) (0**Γ≡0∙γ (Δ Z)) ⟩
    0∙ δ ++ (0∙ δ)
  ≡⟨ ++-identityʳ (0∙ δ) ⟩
    (0∙ δ)
  ∎
\end{code}

\begin{code}
smash-0# : ∀ {γ δ} (Γ : Context γ) {B}

  → (Δ : ∀ {A} → (γ ∋ A → Context δ))
  ---------------------------------------------------
  → smash Γ (λ x → Δ x , 0# ∙ B) ≡ smash Γ Δ , 0# ∙ B

smash-0# {γ} {δ} ∅ {B} Δ =
  begin
    (0∙ δ) , 0# ∙ B
  ≡⟨⟩
    (0∙ δ) , 0# ∙ B
  ∎

smash-0# {γ} {δ} (Γ , π ∙ C) {B} Δ =
  begin
    (π ** Δ Z , π * 0# ∙ B) ++ (smash Γ (λ x → Δ (S x) , 0# ∙ B))
  ≡⟨ cong ((π ** Δ Z , π * 0# ∙ B) ++_) (smash-0# Γ (Δ ∘ S_)) ⟩
    (π ** Δ Z , π * 0# ∙ B) ++ (smash Γ (λ x → Δ (S x)) , 0# ∙ B)
  ≡⟨⟩
    (π ** Δ Z , π * 0# ∙ B) ++ (smash Γ (Δ ∘ S_) , 0# ∙ B)
  ≡⟨⟩
    (π ** Δ Z ++ smash Γ (Δ ∘ S_)) , (π * 0#) + 0# ∙ B
  ≡⟨ cong ((π ** Δ Z ++ smash Γ (Δ ∘ S_)) ,_∙ B) (+-identityʳ (π * 0#)) ⟩
    (π ** Δ Z ++ smash Γ (Δ ∘ S_)) , π * 0# ∙ B
  ≡⟨ cong ((π ** Δ Z ++ smash Γ (Δ ∘ S_)) ,_∙ B) (*-zeroʳ π) ⟩
    (π ** Δ Z ++ smash Γ (Δ ∘ S_)) , 0# ∙ B
  ∎
\end{code}

\begin{code}
smash-VC₁ : ∀ {γ δ} {A}

  → (Δ : ∀ {A} → (γ ∋ A → Context δ))
  → (x : γ ∋ A)
  -----------------------------------
  → smash (VC x) Δ ≡ Δ x

smash-VC₁ {γ , A} {δ} {A} Δ Z =
  begin
    smash (VC Z) Δ
  ≡⟨⟩
    1# ** Δ Z ++ smash (0∙ γ) (Δ ∘ S_)
  ≡⟨ cong ((1# ** Δ Z) ++_) (smash-0∙ (Δ ∘ S_)) ⟩
    1# ** Δ Z ++ (0∙ δ)
  ≡⟨ ++-identityʳ (1# ** Δ Z) ⟩
    1# ** Δ Z
  ≡⟨ **-identity (Δ Z) ⟩
    Δ Z
  ∎

smash-VC₁ {γ , B} {δ} {A} Δ (S x) =
  begin
    smash (VC (S x)) Δ
  ≡⟨⟩
    0# ** Δ Z ++ smash (VC x) (Δ ∘ S_)
  ≡⟨ cong (0# ** Δ Z ++_) (smash-VC₁ (Δ ∘ S_) x) ⟩
    0# ** Δ Z ++ Δ (S x)
  ≡⟨ cong (_++ Δ (S x)) (0**Γ≡0∙γ (Δ Z)) ⟩
    (0∙ δ) ++ Δ (S x)
  ≡⟨ ++-identityˡ (Δ (S x)) ⟩
    Δ (S x)
  ∎
\end{code}

\begin{code}
smash-VC₂ : ∀ {γ} (Γ : Context γ)

  ----------------
  → smash Γ VC ≡ Γ

smash-VC₂ {γ} ∅ =
  begin
    ∅
  ≡⟨⟩
    ∅
  ∎

smash-VC₂ {γ , .A} (Γ , π ∙ A) =
  begin
    (π ** (0∙ γ) , π * 1# ∙ A) ++ (smash Γ (λ x → VC x , 0# ∙ A))
  ≡⟨ cong ((π ** (0∙ γ) , π * 1# ∙ A) ++_) (smash-0# Γ VC) ⟩
    (π ** (0∙ γ) , π * 1# ∙ A) ++ (smash Γ VC , 0# ∙ A)
  ≡⟨ cong ((π ** (0∙ γ) , π * 1# ∙ A) ++_) (cong (_, 0# ∙ A) (smash-VC₂ Γ)) ⟩
    (π ** (0∙ γ) , π * 1# ∙ A) ++ (Γ , 0# ∙ A)
  ≡⟨⟩
    π ** (0∙ γ) ++ Γ , (π * 1#) + 0# ∙ A
  ≡⟨ cong ((π ** (0∙ γ) ++ Γ) ,_∙ A) (+-identityʳ (π * 1#)) ⟩
    π ** (0∙ γ) ++ Γ , π * 1# ∙ A
  ≡⟨ cong ((π ** (0∙ γ) ++ Γ) ,_∙ A) (*-identityʳ π) ⟩
    π ** (0∙ γ) ++ Γ , π ∙ A
  ≡⟨ cong (_, π ∙ A) (cong (_++ Γ) (sym (0∙-absorb γ π))) ⟩
    (0∙ γ) ++ Γ , π ∙ A
  ≡⟨ cong (_, π ∙ A) (++-identityˡ Γ) ⟩
    Γ , π ∙ A
  ∎
\end{code}

\begin{code}
data _⊢₁_ : ∀ {γ} {A} → Context γ → γ ⊢ A → Set where

  var : ∀ {γ} {Γ : Context γ} {A}
      → (x : γ ∋ A)
      → Γ ≡ VC x
        -----------
      → Γ ⊢₁ (` x)

  lam : ∀ {γ} {Γ : Context γ} {A B} {π}

      → {M : γ , A ⊢ B}
      → (Γ , π ∙ A) ⊢₁ M
      → Γ ⊢₁ (ƛ_ {π = π} M)

  app : ∀ {γ} {Γ Δ Θ : Context γ} {A B} {π}

      → {M : γ ⊢ [ π ∙ A ]⊸ B}
      → {N : γ ⊢ A}
      → Γ ⊢₁ M
      → Δ ⊢₁ N
      → Θ ≡ Γ ++ π ** Δ
      → Θ ⊢₁ (M · N)
\end{code}

\begin{code}
postulate
  rename-⊢₁ : ∀ {γ δ} {Γ : Context γ} {B}

    → {M : γ ⊢ B}
    → (ρ : ∀ {A} → γ ∋ A → δ ∋ A)
    → Γ ⊢₁ M
    -------------------------------
    → smash Γ (VC ∘ ρ) ⊢₁ rename ρ M
\end{code}

\begin{code}
weaken-⊢₁ : ∀ {γ} {Γ : Context γ} {A B}

  → {M : γ ⊢ A}
  → Γ ⊢₁ M
  ---------------------------
  → Γ , 0# ∙ B ⊢₁ rename S_ M

weaken-⊢₁ {γ} {Γ} {A} {B} {M} ⊢₁M
  = Eq.subst (_⊢₁ rename S_ M) lem (rename-⊢₁ S_ ⊢₁M)
  where
    lem =
      begin
        smash Γ (VC ∘ S_)
      ≡⟨⟩
        smash Γ (λ x → VC x , 0# ∙ B)
      ≡⟨ smash-0# Γ VC ⟩
        (smash Γ VC) , 0# ∙ B
      ≡⟨ cong (_, 0# ∙ B) (smash-VC₂ Γ) ⟩
        Γ , 0# ∙ B
      ∎
\end{code}

\begin{code}
++-comm : ∀ {γ} (Γ₁ Γ₂ : Context γ)

  ---------------------
  → Γ₁ ++ Γ₂ ≡ Γ₂ ++ Γ₁

++-comm ∅ ∅ =
  begin
    ∅
  ≡⟨⟩
    ∅
  ∎

++-comm (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) =
  begin
    Γ₁ ++ Γ₂ , π₁ + π₂ ∙ A
  ≡⟨ cong (Γ₁ ++ Γ₂ ,_∙ A) (+-comm π₁ π₂) ⟩
    Γ₁ ++ Γ₂ , π₂ + π₁ ∙ A
  ≡⟨ cong (_, π₂ + π₁ ∙ A) (++-comm Γ₁ Γ₂) ⟩
    Γ₂ ++ Γ₁ , π₂ + π₁ ∙ A
  ∎
\end{code}

\begin{code}
++-assoc : ∀ {γ} (Γ₁ Γ₂ Γ₃ : Context γ)

  -------------------------------------
  → (Γ₁ ++ Γ₂) ++ Γ₃ ≡ Γ₁ ++ (Γ₂ ++ Γ₃)

++-assoc ∅ ∅ ∅ =
  begin
    ∅
  ≡⟨⟩
    ∅
  ∎

++-assoc (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) (Γ₃ , π₃ ∙ .A) =
  begin
    (Γ₁ ++ Γ₂) ++ Γ₃ , (π₁ + π₂) + π₃ ∙ A
  ≡⟨ cong ((Γ₁ ++ Γ₂) ++ Γ₃ ,_∙ A) (+-assoc π₁ π₂ π₃) ⟩
    (Γ₁ ++ Γ₂) ++ Γ₃ , π₁ + (π₂ + π₃) ∙ A
  ≡⟨ cong (_, π₁ + (π₂ + π₃) ∙ A) (++-assoc Γ₁ Γ₂ Γ₃) ⟩
    Γ₁ ++ (Γ₂ ++ Γ₃) , π₁ + (π₂ + π₃) ∙ A
  ∎
\end{code}

\begin{code}
**-distribʳ-++ : ∀ {γ} (Γ : Context γ) π₁ π₂

  -----------------------------------
  → π₁ + π₂ ** Γ ≡ π₁ ** Γ ++ π₂ ** Γ

**-distribʳ-++ ∅ π₁ π₂ =
  begin
    ∅
  ≡⟨⟩
    ∅
  ∎

**-distribʳ-++ (Γ , π ∙ A) π₁ π₂ =
  begin
    (π₁ + π₂) ** Γ , (π₁ + π₂) * π ∙ A
  ≡⟨ cong ((π₁ + π₂) ** Γ ,_∙ A) (*-distribʳ-+ π π₁ π₂) ⟩
    (π₁ + π₂) ** Γ , (π₁ * π) + (π₂ * π) ∙ A
  ≡⟨ cong (_, (π₁ * π) + (π₂ * π) ∙ A) (**-distribʳ-++ Γ π₁ π₂) ⟩
    π₁ ** Γ ++ π₂ ** Γ , (π₁ * π) + (π₂ * π) ∙ A
  ∎
\end{code}

\begin{code}
subst-split : ∀ {γ δ} (Γ Γ₁ Γ₂ : Context γ)
  → (σ : ∀ {A} → γ ∋ A → δ ⊢ A)
  → (Δ : ∀ {A} → γ ∋ A → Context δ)
  → (P : ∀ {A} → (x : γ ∋ A) → Δ x ⊢₁ σ x)
  → Γ ≡ Γ₁ ++ Γ₂
  → Σ[ Δ₁ ∈ (∀ {A} → γ ∋ A → Context δ) ]
    Σ[ Δ₂ ∈ (∀ {A} → γ ∋ A → Context δ) ]
     ( (∀ {A} → (x : γ ∋ A) → Δ₁ x ⊢₁ σ x)
     × (∀ {A} → (x : γ ∋ A) → Δ₂ x ⊢₁ σ x)
     × smash Γ₁ Δ₁ ++ smash Γ₂ Δ₂ ≡ smash Γ Δ )
subst-split {γ} {δ} ∅ ∅ ∅ σ Δ P _ =
  ⟨ (λ()) , ⟨ (λ()) , ⟨ (λ()) , ⟨ (λ()) , (++-identityʳ (0∙ δ)) ⟩ ⟩ ⟩ ⟩
subst-split {γ} {δ} (Γ , π ∙ A) (Γ₁ , π₁ ∙ .A) (Γ₂ , π₂ ∙ .A) σ Δ P refl
  with subst-split Γ Γ₁ Γ₂ (σ ∘ S_) (Δ ∘ S_) (P ∘ S_) refl
... | ⟨ Δ₁ , ⟨ Δ₂ , ⟨ P₁ , ⟨ P₂ , smash-++ ⟩ ⟩ ⟩ ⟩ =
  ⟨ Δ₁′ , ⟨ Δ₂′ , ⟨ P₁′ , ⟨ P₂′ , smash-++′ ⟩ ⟩ ⟩ ⟩
  where
    Δ₁′ : ∀ {A} → γ ∋ A → Context δ
    Δ₁′ Z     = Δ Z
    Δ₁′ (S x) = Δ₁ x
    Δ₂′ : ∀ {A} → γ ∋ A → Context δ
    Δ₂′ Z     = Δ Z
    Δ₂′ (S x) = Δ₂ x
    P₁′ : ∀ {A} → (x : γ ∋ A) → Δ₁′ x ⊢₁ σ x
    P₁′ Z     = P Z
    P₁′ (S x) = P₁ x
    P₂′ : ∀ {A} → (x : γ ∋ A) → Δ₂′ x ⊢₁ σ x
    P₂′ Z     = P Z
    P₂′ (S x) = P₂ x
    smash-++′ =
      begin
        (π₁ ** Δ Z ++ smash Γ₁ Δ₁) ++ (π₂ ** Δ Z ++ smash Γ₂ Δ₂)
      ≡⟨ sym (++-assoc (π₁ ** Δ Z ++ smash Γ₁ Δ₁) (π₂ ** Δ Z) (smash Γ₂ Δ₂)) ⟩
        ((π₁ ** Δ Z ++ smash Γ₁ Δ₁) ++ π₂ ** Δ Z) ++ smash Γ₂ Δ₂
      ≡⟨ cong (_++ smash Γ₂ Δ₂) (++-comm (π₁ ** Δ Z ++ smash Γ₁ Δ₁) (π₂ ** Δ Z)) ⟩
        (π₂ ** Δ Z ++ (π₁ ** Δ Z ++ smash Γ₁ Δ₁)) ++ smash Γ₂ Δ₂
      ≡⟨ cong (_++ smash Γ₂ Δ₂) (sym (++-assoc (π₂ ** Δ Z) (π₁ ** Δ Z) (smash Γ₁ Δ₁)) ) ⟩
        ((π₂ ** Δ Z ++ π₁ ** Δ Z) ++ smash Γ₁ Δ₁) ++ smash Γ₂ Δ₂
      ≡⟨ ++-assoc (π₂ ** Δ Z ++ π₁ ** Δ Z) (smash Γ₁ Δ₁) (smash Γ₂ Δ₂) ⟩
        (π₂ ** Δ Z ++ π₁ ** Δ Z) ++ (smash Γ₁ Δ₁ ++ smash Γ₂ Δ₂)
      ≡⟨ cong (_++ (smash Γ₁ Δ₁ ++ smash Γ₂ Δ₂)) (++-comm (π₂ ** Δ Z) (π₁ ** Δ Z)) ⟩
        (π₁ ** Δ Z ++ π₂ ** Δ Z) ++ (smash Γ₁ Δ₁ ++ smash Γ₂ Δ₂)
      ≡⟨ cong (_++ (smash Γ₁ Δ₁ ++ smash Γ₂ Δ₂)) (sym (**-distribʳ-++ (Δ Z) π₁ π₂)) ⟩
        (π₁ + π₂) ** Δ Z ++ (smash Γ₁ Δ₁ ++ smash Γ₂ Δ₂)
      ≡⟨ cong ((π₁ + π₂) ** Δ Z ++_) smash-++ ⟩
        (π₁ + π₂) ** Δ Z ++ smash (Γ₁ ++ Γ₂) (Δ ∘ S_)
      ∎
\end{code}

\begin{code}
**-distribˡ-++ : ∀ {γ} (Γ₁ Γ₂ : Context γ) {π}

  --------------------------------------
  → π ** (Γ₁ ++ Γ₂) ≡ π ** Γ₁ ++ π ** Γ₂

**-distribˡ-++ ∅ ∅ =
  begin
    ∅
  ≡⟨⟩
    ∅
  ∎

**-distribˡ-++ (Γ₁ , π₁ ∙ A) (Γ₂ , π₂ ∙ .A) {π} =
  begin
    π ** (Γ₁ ++ Γ₂) , π * (π₁ + π₂) ∙ A
  ≡⟨ cong (π ** (Γ₁ ++ Γ₂) ,_∙ A) (*-distribˡ-+ π π₁ π₂) ⟩
    π ** (Γ₁ ++ Γ₂) , (π * π₁) + (π * π₂) ∙ A
  ≡⟨ cong (_, (π * π₁) + (π * π₂) ∙ A) (**-distribˡ-++ Γ₁ Γ₂) ⟩
    π ** Γ₁ ++ π ** Γ₂ , (π * π₁) + (π * π₂) ∙ A
  ∎
\end{code}

\begin{code}
smash-** : ∀ {γ δ} (Γ : Context γ) {π}

  → (Δ : ∀ {A} → γ ∋ A → Context δ)
  -----------------------------------
  → smash (π ** Γ) Δ ≡ π ** smash Γ Δ

smash-** {γ} {δ} ∅ {π} Δ =
  begin
    (0∙ δ)
  ≡⟨ 0∙-absorb δ π ⟩
    π ** (0∙ δ)
  ∎

smash-** {γ} {δ} (Γ , π′ ∙ A) {π} Δ =
  begin
    ((π * π′) ** Δ Z) ++ (smash (π ** Γ) (Δ ∘ S_))
  ≡⟨ cong ((π * π′) ** Δ Z ++_) (smash-** Γ (Δ ∘ S_)) ⟩
    ((π * π′) ** Δ Z) ++ (π ** smash Γ (Δ ∘ S_))
  ≡⟨ cong (_++ (π ** smash Γ (Δ ∘ S_))) (**-assoc (Δ Z)) ⟩
    (π ** (π′ ** Δ Z)) ++ (π ** smash Γ (Δ ∘ S_))
  ≡⟨ sym (**-distribˡ-++ (π′ ** Δ Z) (smash Γ (Δ ∘ S_))) ⟩
    π ** (π′ ** Δ Z ++ smash Γ (Δ ∘ S_))
  ∎
\end{code}

\begin{code}
subst-⊢₁ : ∀ {γ δ} {Γ : Context γ} {B}

  → {M : γ ⊢ B}
  → (σ : ∀ {A} → γ ∋ A → δ ⊢ A)
  → (Δ : ∀ {A} → γ ∋ A → Context δ)
  → (P : ∀ {A} → (x : γ ∋ A) → Δ x ⊢₁ σ x)
  → Γ ⊢₁ M
    --------------------------------------
  → (smash Γ Δ) ⊢₁ (subst σ M)

subst-⊢₁ {δ = δ} σ Δ P (var {γ} {Γ} {B} x refl)
  = Eq.subst (_⊢₁ σ x) lem (P x)
  where
    lem =
      begin
        Δ x
      ≡⟨ sym (smash-VC₁ Δ x) ⟩
        smash (VC x) Δ
      ∎

subst-⊢₁ {δ = δ} σ Δ P (lam {γ} {Γ} {A} {B} {π} {M} ⊢₁M)
  = lam (Eq.subst (_⊢₁ subst (exts σ) M) lem ⊢₁M′)
  where
    ⊢₁M′ = subst-⊢₁ (exts σ) Δ′ P′ ⊢₁M
      where
        Δ′ : ∀ {A B} → γ , B ∋ A → Context (δ , B)
        Δ′ Z     = VC Z
        Δ′ (S x) = Δ x , 0# ∙ _
        P′ : ∀ {A B} → (x : γ , B ∋ A) → Δ′ x ⊢₁ (exts σ) x
        P′ Z     = var Z refl
        P′ (S x) = weaken-⊢₁ (P x)
    lem =
      begin
        (π ** (0∙ δ) , π * 1# ∙ A) ++ (smash Γ (λ x → Δ x , 0# ∙ A))
      ≡⟨ cong ((π ** (0∙ δ) , π * 1# ∙ A) ++_) (smash-0# Γ Δ) ⟩
        (π ** (0∙ δ) , π * 1# ∙ A) ++ (smash Γ Δ , 0# ∙ A)
      ≡⟨⟩
        π ** (0∙ δ) ++ smash Γ Δ , (π * 1#) + 0# ∙ A
      ≡⟨ cong (_, (π * 1#) + 0# ∙ A) (cong (_++ smash Γ Δ) (sym (0∙-absorb δ π))) ⟩
        (0∙ δ) ++ smash Γ Δ , (π * 1#) + 0# ∙ A
      ≡⟨ cong (_, (π * 1#) + 0# ∙ A) (++-identityˡ (smash Γ Δ)) ⟩
        smash Γ Δ , (π * 1#) + 0# ∙ A
      ≡⟨ cong (smash Γ Δ ,_∙ A) (+-identityʳ (π * 1#)) ⟩
        smash Γ Δ , π * 1# ∙ A
      ≡⟨ cong (smash Γ Δ ,_∙ A) (*-identityʳ π) ⟩
        smash Γ Δ , π ∙ A
      ∎

subst-⊢₁ {δ = δ} σ Δ P (app {γ} {Γ₁} {Γ₂} {Γ} {A} {B} {π} ⊢₁M ⊢₁N Γ≡Γ₁++π**Γ₂)
  with subst-split Γ Γ₁ (π ** Γ₂) σ Δ P Γ≡Γ₁++π**Γ₂
... | ⟨ Δ₁ , ⟨ Δ₂ , ⟨ P₁ , ⟨ P₂ , smash-++ ⟩ ⟩ ⟩ ⟩ = app ⊢₁M′ ⊢₁N′ lem
  where
    ⊢₁M′ = subst-⊢₁ σ Δ₁ P₁ ⊢₁M
    ⊢₁N′ = subst-⊢₁ σ Δ₂ P₂ ⊢₁N
    lem =
      begin
        smash Γ Δ
      ≡⟨ sym (smash-++) ⟩
        smash Γ₁ Δ₁ ++ smash (π ** Γ₂) Δ₂
      ≡⟨ cong (smash Γ₁ Δ₁ ++_) (smash-** Γ₂ Δ₂) ⟩
        smash Γ₁ Δ₁ ++ π ** smash Γ₂ Δ₂
      ∎
\end{code}
