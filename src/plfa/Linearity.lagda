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
open import Data.Product using (Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)
\end{code}

\begin{code}
infix  1 _⊨_
infix  1 _⊢_
infix  1 _∋_
infixl 5 _,_
infixl 5 _,_∙_
infixr 6 [_∙_]⊸_
infixr 8 _⋈_
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
0#∙_ : ∀ γ → Context γ
0#∙  ∅      = ∅
0#∙ (γ , A) = 0#∙ γ , 0# ∙ A
\end{code}

\begin{code}
0**Γ≡0∙γ : ∀ {γ} (Γ : Context γ)

  -----------------
  → 0# ** Γ ≡ 0#∙ γ

0**Γ≡0∙γ ∅ = refl
0**Γ≡0∙γ (Γ , π ∙ A) rewrite 0**Γ≡0∙γ Γ = refl
\end{code}

\begin{code}
_⋈_ : ∀ {γ} → Context γ → Context γ → Context γ
∅ ⋈ ∅ = ∅
(Γ₁ , π₁ ∙ A) ⋈ (Γ₂ , π₂ ∙ .A) = Γ₁ ⋈ Γ₂ , π₁ + π₂ ∙ A
\end{code}

\begin{code}
⋈-identityˡ : ∀ {γ} (Γ : Context γ)

  ---------------
  → 0#∙ γ ⋈ Γ ≡ Γ

⋈-identityˡ ∅ = refl
⋈-identityˡ (Γ , π ∙ A) rewrite ⋈-identityˡ Γ | +-identityʳ π = refl
\end{code}

\begin{code}
⋈-identityʳ : ∀ {γ} (Γ : Context γ)

  ---------------
  → Γ ⋈ 0#∙ γ ≡ Γ

⋈-identityʳ ∅ = refl
⋈-identityʳ (Γ , π ∙ A) rewrite ⋈-identityʳ Γ | +-identityʳ π = refl
\end{code}

\begin{code}
VC : ∀ {A} {γ : Precontext} → γ ∋ A → Context γ
VC {γ = γ , A} Z     = 0#∙ γ , 1# ∙ A
VC {γ = γ , B} (S x) = VC x , 0# ∙ B
\end{code}

\begin{code}
smash : ∀ {γ δ}

  → (Γ : Context γ)
  → (Δ : ∀ {A} → γ ∋ A → Context δ)
  → Context δ

smash {δ = δ} ∅           Δ = 0#∙ δ
smash {δ = δ} (Γ , π ∙ A) Δ = (π ** Δ Z) ⋈ smash Γ (Δ ∘ S_)
\end{code}

\begin{code}
smash-0∙ : ∀ {γ δ}

  → (Δ : ∀ {A} → (γ ∋ A → Context δ))
  -----------------------------------
  → smash (0#∙ γ) Δ ≡ 0#∙ δ

smash-0∙ {∅}     {δ} Δ = refl
smash-0∙ {γ , A} {δ} Δ =
  begin
    smash (0#∙ (γ , A)) Δ
  ≡⟨⟩
    0# ** Δ Z ⋈ smash (0#∙ γ) (Δ ∘ S_)
  ≡⟨ cong (0# ** Δ Z ⋈_) (smash-0∙ {γ} (Δ ∘ S_)) ⟩
    0# ** Δ Z ⋈ (0#∙ δ)
  ≡⟨ cong (_⋈ (0#∙ δ)) (0**Γ≡0∙γ (Δ Z)) ⟩
    0#∙ δ ⋈ (0#∙ δ)
  ≡⟨ ⋈-identityʳ (0#∙ δ) ⟩
    (0#∙ δ)
  ∎
\end{code}

\begin{code}
smash-VC : ∀ {γ δ} {A}

  → (Δ : ∀ {A} → (γ ∋ A → Context δ))
  → (x : γ ∋ A)
  -----------------------------------
  → smash (VC x) Δ ≡ Δ x

smash-VC {γ , A} {δ} {A} Δ Z =
  begin
    smash (VC Z) Δ
  ≡⟨⟩
    1# ** Δ Z ⋈ smash (0#∙ γ) (Δ ∘ S_)
  ≡⟨ cong ((1# ** Δ Z) ⋈_) (smash-0∙ (Δ ∘ S_)) ⟩
    1# ** Δ Z ⋈ (0#∙ δ)
  ≡⟨ ⋈-identityʳ (1# ** Δ Z) ⟩
    1# ** Δ Z
  ≡⟨ **-identity (Δ Z) ⟩
    Δ Z
  ∎
smash-VC {γ , B} {δ} {A} Δ (S x) =
  begin
    smash (VC (S x)) Δ
  ≡⟨⟩
    0# ** Δ Z ⋈ smash (VC x) (Δ ∘ S_)
  ≡⟨ cong (0# ** Δ Z ⋈_) (smash-VC (Δ ∘ S_) x) ⟩
    0# ** Δ Z ⋈ Δ (S x)
  ≡⟨ cong (_⋈ Δ (S x)) (0**Γ≡0∙γ (Δ Z)) ⟩
    (0#∙ δ) ⋈ Δ (S x)
  ≡⟨ ⋈-identityˡ (Δ (S x)) ⟩
    Δ (S x)
  ∎
\end{code}

\begin{code}
data _⊨_ : ∀ {γ} {A} → Context γ → γ ⊢ A → Set where

  var : ∀ {γ} {Γ : Context γ} {A}
      → (x : γ ∋ A)
      → Γ ≡ VC x
        -----------
      → Γ ⊨ (` x)

  lam : ∀ {γ} {Γ : Context γ} {A B} {π}

      → {M : γ , A ⊢ B}
      → (Γ , π ∙ A) ⊨ M
      → Γ ⊨ (ƛ_ {π = π} M)

  app : ∀ {γ} {Γ Δ Θ : Context γ} {A B} {π}

      → {M : γ ⊢ [ π ∙ A ]⊸ B}
      → {N : γ ⊢ A}
      → Γ ⊨ M
      → Δ ⊨ N
      → Θ ≡ Γ ⋈ π ** Δ
      → Θ ⊨ (M · N)
\end{code}

\begin{code}
postulate
  rename-⊨ : ∀ {γ δ} {Γ : Context γ} {B}

    → {M : γ ⊢ B}
    → (ρ : ∀ {A} → γ ∋ A → δ ∋ A)
    → Γ ⊨ M
    -------------------------------
    → smash Γ (VC ∘ ρ) ⊨ rename ρ M
\end{code}

\begin{code}
weaken-⊨ : ∀ {γ} {Γ : Context γ} {A B}

  → {M : γ ⊢ A}
  → Γ ⊨ M
  ---------------------------
  → Γ , 0# ∙ B ⊨ rename S_ M

weaken-⊨ ⊨M = {!rename-⊨ S_ ⊨M!}
\end{code}

\begin{code}
substSplit : ∀ {γ δ} (Γ Γ₁ Γ₂ : Context γ)
  → (σ : ∀ {A} → γ ∋ A → δ ⊢ A)
  → (Δ : ∀ {A} → γ ∋ A → Context δ)
  → (P : ∀ {A} → (x : γ ∋ A) → Δ x ⊨ σ x)
  → Γ₁ ⋈ Γ₂ ≡ Γ
  → Σ[ Δ₁ ∈ (∀ {A} → γ ∋ A → Context δ) ]
    Σ[ Δ₂ ∈ (∀ {A} → γ ∋ A → Context δ) ]
     ( smash Γ₁ Δ₁ ⋈ smash Γ₂ Δ₂ ≡ smash Γ Δ )
substSplit ∅ ∅ ∅ σ Δ P p = ⟨ (λ()) , ⟨ (λ()) , ⋈-identityʳ _ ⟩ ⟩
substSplit (Γ , π ∙ A) (Γ₁ , π₁ ∙ .A) (Γ₂ , π₂ ∙ .A) σ Δ P refl
  with substSplit Γ Γ₁ Γ₂ (σ ∘ S_) (Δ ∘ S_) (P ∘ S_) refl
...| ⟨ Δ₁ , ⟨ Δ₂ , Q ⟩ ⟩ = ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩
\end{code}

-- TODO both of those Δᵢs need to be fine and dandy

\begin{code}
subst-⊨ : ∀ {γ δ} {Γ : Context γ} {B}

  → {M : γ ⊢ B}
  → (σ : ∀ {A} → γ ∋ A → δ ⊢ A)
  → (Δ : ∀ {A} → γ ∋ A → Context δ)
  → (P : ∀ {A} → (x : γ ∋ A) → Δ x ⊨ σ x)
  → Γ ⊨ M
    --------------
  → (smash Γ Δ) ⊨ (subst σ M)

subst-⊨ σ Δ P (var x refl) rewrite smash-VC Δ x = P x
subst-⊨ {γ} {δ} σ Δ P (lam M)
  = lam {!subst-⊨ σ′ Δ′ P′ M!}
  where
    σ′ : ∀ {A B} → γ , B ∋ A → δ , B ⊢ A
    σ′ = exts σ
    Δ′ : ∀ {A B} → γ , B ∋ A → Context (δ , B)
    Δ′ {A} {B} Z     = VC Z
    Δ′ {A} {B} (S x) = Δ x , 0# ∙ B
    P′ : ∀ {A B} → (x : γ , B ∋ A) → Δ′ x ⊨ σ′ x
    P′ {A} {B} Z     = var Z refl
    P′ {A} {B} (S x) = weaken-⊨ (P x)
subst-⊨ σ Δ P (app M N Θ≡Γ⋈π**Δ)
  = app
    (subst-⊨ {!!} {!!} {!!} M)
    (subst-⊨ {!!} {!!} {!!} N)
    {!!}
\end{code}
