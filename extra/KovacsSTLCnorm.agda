{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Function

-- some HoTT-inspired combinators

_&_ = cong
_⁻¹ = sym
_◾_ = trans

coe : {A B : Set} → A ≡ B → A → B
coe refl a = a

_⊗_ : ∀ {A B : Set}{f g : A → B}{a a'} → f ≡ g → a ≡ a' → f a ≡ g a'
refl ⊗ refl = refl

infix 6 _⁻¹
infixr 4 _◾_
infixl 9 _&_
infixl 8 _⊗_

-- Syntax
--------------------------------------------------------------------------------

infixr 4 _⇒_
infixr 4 _,_

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

data Tm Γ : Ty → Set where
  var : ∀ {A} → A ∈ Γ → Tm Γ A
  lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

-- Embedding
--------------------------------------------------------------------------------

-- Order-preserving embedding
data OPE : Con → Con → Set where
  ∙    : OPE ∙ ∙
  drop : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) Δ
  keep : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) (Δ , A)

-- OPE is a category
idₑ : ∀ {Γ} → OPE Γ Γ
idₑ {∙}     = ∙
idₑ {Γ , A} = keep (idₑ {Γ})

wk : ∀ {A Γ} → OPE (Γ , A) Γ
wk = drop idₑ

_∘ₑ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → OPE Γ Δ → OPE Γ Σ
σ      ∘ₑ ∙      = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

idlₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₑ ∘ₑ σ ≡ σ
idlₑ ∙        = refl
idlₑ (drop σ) = drop & idlₑ σ
idlₑ (keep σ) = keep & idlₑ σ

idrₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ∘ₑ idₑ ≡ σ
idrₑ ∙        = refl
idrₑ (drop σ) = drop & idrₑ σ
idrₑ (keep σ) = keep & idrₑ σ

assₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₑ δ) ∘ₑ ν ≡ σ ∘ₑ (δ ∘ₑ ν)
assₑ σ        δ        ∙        = refl
assₑ σ        δ        (drop ν) = drop & assₑ σ δ ν
assₑ σ        (drop δ) (keep ν) = drop & assₑ σ δ ν
assₑ (drop σ) (keep δ) (keep ν) = drop & assₑ σ δ ν
assₑ (keep σ) (keep δ) (keep ν) = keep & assₑ σ δ ν

∈ₑ : ∀ {A Γ Δ} → OPE Γ Δ → A ∈ Δ → A ∈ Γ
∈ₑ ∙        v      = v
∈ₑ (drop σ) v      = vs (∈ₑ σ v)
∈ₑ (keep σ) vz     = vz
∈ₑ (keep σ) (vs v) = vs (∈ₑ σ v)

∈-idₑ : ∀ {A Γ}(v : A ∈ Γ) → ∈ₑ idₑ v ≡ v
∈-idₑ vz     = refl
∈-idₑ (vs v) = vs & ∈-idₑ v

∈-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(v : A ∈ Σ) → ∈ₑ (σ ∘ₑ δ) v ≡ ∈ₑ δ (∈ₑ σ v)
∈-∘ₑ ∙        ∙        v      = refl
∈-∘ₑ σ        (drop δ) v      = vs & ∈-∘ₑ σ δ v
∈-∘ₑ (drop σ) (keep δ) v      = vs & ∈-∘ₑ σ δ v
∈-∘ₑ (keep σ) (keep δ) vz     = refl
∈-∘ₑ (keep σ) (keep δ) (vs v) = vs & ∈-∘ₑ σ δ v

Tmₑ : ∀ {A Γ Δ} → OPE Γ Δ → Tm Δ A → Tm Γ A
Tmₑ σ (var v)   = var (∈ₑ σ v)
Tmₑ σ (lam t)   = lam (Tmₑ (keep σ) t)
Tmₑ σ (app f a) = app (Tmₑ σ f) (Tmₑ σ a)

Tm-idₑ : ∀ {A Γ}(t : Tm Γ A) → Tmₑ idₑ t ≡ t
Tm-idₑ (var v)   = var & ∈-idₑ v
Tm-idₑ (lam t)   = lam & Tm-idₑ t
Tm-idₑ (app f a) = app & Tm-idₑ f ⊗ Tm-idₑ a

Tm-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₑ (σ ∘ₑ δ) t ≡ Tmₑ δ (Tmₑ σ t)
Tm-∘ₑ σ δ (var v)   = var & ∈-∘ₑ σ δ v
Tm-∘ₑ σ δ (lam t)   = lam & Tm-∘ₑ (keep σ) (keep δ) t
Tm-∘ₑ σ δ (app f a) = app & Tm-∘ₑ σ δ f ⊗ Tm-∘ₑ σ δ a

-- Theory of substitution & embedding
--------------------------------------------------------------------------------

infixr 6 _ₑ∘ₛ_ _ₛ∘ₑ_ _∘ₛ_

data Sub (Γ : Con) : Con → Set where
  ∙   : Sub Γ ∙
  _,_ : ∀ {A : Ty}{Δ : Con} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ , A)

_ₛ∘ₑ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → OPE Γ Δ → Sub Γ Σ
∙       ₛ∘ₑ δ = ∙
(σ , t) ₛ∘ₑ δ = σ ₛ∘ₑ δ , Tmₑ δ t

_ₑ∘ₛ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → Sub Γ Δ → Sub Γ Σ
∙      ₑ∘ₛ δ       = δ
drop σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ
keep σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ , t

dropₛ : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ , A) Δ
dropₛ σ = σ ₛ∘ₑ wk

keepₛ : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ , A) (Δ , A)
keepₛ σ = dropₛ σ , var vz

⌜_⌝ᵒᵖᵉ : ∀ {Γ Δ} → OPE Γ Δ → Sub Γ Δ
⌜ ∙      ⌝ᵒᵖᵉ = ∙
⌜ drop σ ⌝ᵒᵖᵉ = dropₛ ⌜ σ ⌝ᵒᵖᵉ
⌜ keep σ ⌝ᵒᵖᵉ = keepₛ ⌜ σ ⌝ᵒᵖᵉ

∈ₛ : ∀ {A Γ Δ} → Sub Γ Δ → A ∈ Δ → Tm Γ A
∈ₛ (σ , t) vz     = t
∈ₛ (σ  , t)(vs v) = ∈ₛ σ v

Tmₛ : ∀ {A Γ Δ} → Sub Γ Δ → Tm Δ A → Tm Γ A
Tmₛ σ (var v)   = ∈ₛ σ v
Tmₛ σ (lam t)   = lam (Tmₛ (keepₛ σ) t)
Tmₛ σ (app f a) = app (Tmₛ σ f) (Tmₛ σ a)

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ {∙}     = ∙
idₛ {Γ , A} = (idₛ {Γ} ₛ∘ₑ drop idₑ) , var vz

_∘ₛ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
∙       ∘ₛ δ = ∙
(σ , t) ∘ₛ δ = σ ∘ₛ δ , Tmₛ δ t

assₛₑₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ₛ∘ₑ δ) ₛ∘ₑ ν ≡ σ ₛ∘ₑ (δ ∘ₑ ν)
assₛₑₑ ∙       δ ν = refl
assₛₑₑ (σ , t) δ ν = _,_ & assₛₑₑ σ δ ν ⊗ (Tm-∘ₑ δ ν t ⁻¹)

assₑₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : Sub Δ Σ)(ν : OPE Γ Δ)
  → (σ ₑ∘ₛ δ) ₛ∘ₑ ν ≡ σ ₑ∘ₛ (δ ₛ∘ₑ ν)
assₑₛₑ ∙        δ       ν = refl
assₑₛₑ (drop σ) (δ , t) ν = assₑₛₑ σ δ ν
assₑₛₑ (keep σ) (δ , t) ν = (_, Tmₑ ν t) & assₑₛₑ σ δ ν

idlₑₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → idₑ ₑ∘ₛ σ ≡ σ
idlₑₛ ∙       = refl
idlₑₛ (σ , t) = (_, t) & idlₑₛ σ

idlₛₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₛ ₛ∘ₑ σ ≡ ⌜ σ ⌝ᵒᵖᵉ
idlₛₑ ∙        = refl
idlₛₑ (drop σ) =
      ((idₛ ₛ∘ₑ_) ∘ drop) & idrₑ σ ⁻¹
    ◾ assₛₑₑ idₛ σ wk ⁻¹
    ◾ dropₛ & idlₛₑ σ
idlₛₑ (keep σ) =
  (_, var vz) &
      (assₛₑₑ idₛ wk (keep σ)
    ◾ ((idₛ ₛ∘ₑ_) ∘ drop) & (idlₑ σ ◾ idrₑ σ ⁻¹)
    ◾ assₛₑₑ idₛ σ wk ⁻¹
    ◾ (_ₛ∘ₑ wk) & idlₛₑ σ )

idrₑₛ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ₑ∘ₛ idₛ ≡ ⌜ σ ⌝ᵒᵖᵉ
idrₑₛ ∙        = refl
idrₑₛ (drop σ) = assₑₛₑ σ idₛ wk ⁻¹ ◾ dropₛ & idrₑₛ σ
idrₑₛ (keep σ) = (_, var vz) & (assₑₛₑ σ idₛ wk ⁻¹ ◾ (_ₛ∘ₑ wk) & idrₑₛ σ)

∈-ₑ∘ₛ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ₑ∘ₛ δ) v ≡ ∈ₛ δ (∈ₑ σ v)
∈-ₑ∘ₛ ∙        δ       v      = refl
∈-ₑ∘ₛ (drop σ) (δ , t) v      = ∈-ₑ∘ₛ σ δ v
∈-ₑ∘ₛ (keep σ) (δ , t) vz     = refl
∈-ₑ∘ₛ (keep σ) (δ , t) (vs v) = ∈-ₑ∘ₛ σ δ v

Tm-ₑ∘ₛ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ A) → Tmₛ (σ ₑ∘ₛ δ) t ≡ Tmₛ δ (Tmₑ σ t)
Tm-ₑ∘ₛ σ δ (var v) = ∈-ₑ∘ₛ σ δ v
Tm-ₑ∘ₛ σ δ (lam t) =
  lam & ((λ x → Tmₛ (x , var vz) t) & assₑₛₑ σ δ wk ◾ Tm-ₑ∘ₛ (keep σ) (keepₛ δ) t)
Tm-ₑ∘ₛ σ δ (app f a) = app & Tm-ₑ∘ₛ σ δ f ⊗ Tm-ₑ∘ₛ σ δ a

∈-ₛ∘ₑ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ₛ∘ₑ δ) v ≡ Tmₑ δ (∈ₛ σ v)
∈-ₛ∘ₑ (σ , _) δ vz     = refl
∈-ₛ∘ₑ (σ , _) δ (vs v) = ∈-ₛ∘ₑ σ δ v

Tm-ₛ∘ₑ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₛ (σ ₛ∘ₑ δ) t ≡ Tmₑ δ (Tmₛ σ t)
Tm-ₛ∘ₑ σ δ (var v)   = ∈-ₛ∘ₑ σ δ v
Tm-ₛ∘ₑ σ δ (lam t)   =
  lam &
      ((λ x → Tmₛ (x , var vz) t) &
          (assₛₑₑ σ δ wk
        ◾ (σ ₛ∘ₑ_) & (drop & (idrₑ δ ◾ idlₑ δ ⁻¹))
        ◾ assₛₑₑ σ wk (keep δ) ⁻¹)
    ◾ Tm-ₛ∘ₑ (keepₛ σ) (keep δ) t)
Tm-ₛ∘ₑ σ δ (app f a) = app & Tm-ₛ∘ₑ σ δ f ⊗ Tm-ₛ∘ₑ σ δ a

assₛₑₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Δ Σ)(ν : Sub Γ Δ)
  → (σ ₛ∘ₑ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ₑ∘ₛ ν)
assₛₑₛ ∙       δ ν = refl
assₛₑₛ (σ , t) δ ν = _,_ & assₛₑₛ σ δ ν ⊗ (Tm-ₑ∘ₛ δ ν t ⁻¹)

assₛₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : Sub Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₛ δ) ₛ∘ₑ ν ≡ σ ∘ₛ (δ ₛ∘ₑ ν)
assₛₛₑ ∙       δ ν = refl
assₛₛₑ (σ , t) δ ν = _,_ & assₛₛₑ σ δ ν ⊗ (Tm-ₛ∘ₑ δ ν t ⁻¹)

∈-idₛ : ∀ {A Γ}(v : A ∈ Γ) → ∈ₛ idₛ v ≡ var v
∈-idₛ vz     = refl
∈-idₛ (vs v) = ∈-ₛ∘ₑ idₛ wk v ◾ Tmₑ wk & ∈-idₛ v ◾ (var ∘ vs) & ∈-idₑ v

∈-∘ₛ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ∘ₛ δ) v ≡ Tmₛ δ (∈ₛ σ v)
∈-∘ₛ (σ , _) δ vz     = refl
∈-∘ₛ (σ , _) δ (vs v) = ∈-∘ₛ σ δ v

Tm-idₛ : ∀ {A Γ}(t : Tm Γ A) → Tmₛ idₛ t ≡ t
Tm-idₛ (var v)   = ∈-idₛ v
Tm-idₛ (lam t)   = lam & Tm-idₛ t
Tm-idₛ (app f a) = app & Tm-idₛ f ⊗ Tm-idₛ a

Tm-∘ₛ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ A) → Tmₛ (σ ∘ₛ δ) t ≡ Tmₛ δ (Tmₛ σ t)
Tm-∘ₛ σ δ (var v)   = ∈-∘ₛ σ δ v
Tm-∘ₛ σ δ (lam t)   =
  lam &
      ((λ x → Tmₛ (x , var vz) t) &
          (assₛₛₑ σ δ wk
        ◾ (σ ∘ₛ_) & (idlₑₛ  (dropₛ δ) ⁻¹) ◾ assₛₑₛ σ wk (keepₛ δ) ⁻¹)
    ◾ Tm-∘ₛ (keepₛ σ) (keepₛ δ) t)
Tm-∘ₛ σ δ (app f a) = app & Tm-∘ₛ σ δ f ⊗ Tm-∘ₛ σ δ a

idrₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → σ ∘ₛ idₛ ≡ σ
idrₛ ∙       = refl
idrₛ (σ , t) = _,_ & idrₛ σ ⊗ Tm-idₛ t

idlₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → idₛ ∘ₛ σ ≡ σ
idlₛ ∙       = refl
idlₛ (σ , t) = (_, t) & (assₛₑₛ idₛ wk (σ , t) ◾ (idₛ ∘ₛ_) & idlₑₛ σ ◾ idlₛ σ)

-- Reduction
--------------------------------------------------------------------------------

data _~>_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  β    : ∀ {A B}(t : Tm (Γ , A) B) t'  → app (lam t) t' ~> Tmₛ (idₛ , t') t
  lam  : ∀ {A B}{t t' : Tm (Γ , A) B}     → t ~> t' →  lam t   ~> lam t'
  app₁ : ∀ {A B}{f}{f' : Tm Γ (A ⇒ B)}{a} → f ~> f' →  app f a ~> app f' a
  app₂ : ∀ {A B}{f : Tm Γ (A ⇒ B)} {a a'} → a ~> a' →  app f a ~> app f  a'
infix 3 _~>_

~>ₛ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : Sub Δ Γ) → t ~> t' → Tmₛ σ t ~> Tmₛ σ t'
~>ₛ σ (β t t') =
  coe ((app (lam (Tmₛ (keepₛ σ) t)) (Tmₛ σ t') ~>_) &
      (Tm-∘ₛ (keepₛ σ) (idₛ , Tmₛ σ t') t ⁻¹
    ◾ (λ x → Tmₛ (x , Tmₛ σ t') t) &
        (assₛₑₛ σ wk (idₛ , Tmₛ σ t')
      ◾ ((σ ∘ₛ_) & idlₑₛ idₛ ◾ idrₛ σ) ◾ idlₛ σ ⁻¹)
    ◾ Tm-∘ₛ (idₛ , t') σ t))
  (β (Tmₛ (keepₛ σ) t) (Tmₛ σ t'))
~>ₛ σ (lam  step) = lam  (~>ₛ (keepₛ σ) step)
~>ₛ σ (app₁ step) = app₁ (~>ₛ σ step)
~>ₛ σ (app₂ step) = app₂ (~>ₛ σ step)

~>ₑ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : OPE Δ Γ) → t ~> t' → Tmₑ σ t ~> Tmₑ σ t'
~>ₑ σ (β t t')    =
  coe ((app (lam (Tmₑ (keep σ) t)) (Tmₑ σ t') ~>_)
      & (Tm-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ t') t ⁻¹
      ◾ (λ x → Tmₛ (x , Tmₑ σ t') t) & (idrₑₛ σ ◾ idlₛₑ σ ⁻¹)
      ◾ Tm-ₛ∘ₑ (idₛ , t') σ t))
  (β (Tmₑ (keep σ) t) (Tmₑ σ t'))
~>ₑ σ (lam step)  = lam (~>ₑ (keep σ) step)
~>ₑ σ (app₁ step) = app₁ (~>ₑ σ step)
~>ₑ σ (app₂ step) = app₂ (~>ₑ σ step)

Tmₑ~> :
  ∀ {Γ Δ A}{t : Tm Γ A}{σ : OPE Δ Γ}{t'}
  → Tmₑ σ t ~> t' → ∃ λ t'' → (t ~> t'') × (Tmₑ σ t'' ≡ t')
Tmₑ~> {t = var x} ()
Tmₑ~> {t = lam t} (lam step) with Tmₑ~> step
... | t'' , (p , refl) = lam t'' , lam p , refl
Tmₑ~> {t = app (var v) a} (app₁ ())
Tmₑ~> {t = app (var v) a} (app₂ step) with Tmₑ~> step
... | t'' , (p , refl) = app (var v) t'' , app₂ p , refl
Tmₑ~> {t = app (lam f) a} {σ} (β _ _) =
  Tmₛ (idₛ , a) f , β _ _ ,
      Tm-ₛ∘ₑ (idₛ , a) σ f ⁻¹
    ◾ (λ x →  Tmₛ (x , Tmₑ σ a) f) & (idlₛₑ σ ◾ idrₑₛ σ ⁻¹)
    ◾ Tm-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ a) f
Tmₑ~> {t = app (lam f) a}     (app₁ (lam step)) with Tmₑ~> step
... | t'' , (p , refl) = app (lam t'') a , app₁ (lam p) , refl
Tmₑ~> {t = app (lam f) a}     (app₂ step) with Tmₑ~> step
... | t'' , (p , refl) = app (lam f) t'' , app₂ p , refl
Tmₑ~> {t = app (app f a) a'}  (app₁ step) with Tmₑ~> step
... | t'' , (p , refl) = app t'' a' , app₁ p , refl
Tmₑ~> {t = app (app f a) a''} (app₂ step) with Tmₑ~> step
... | t'' , (p , refl) = app (app f a) t'' , app₂ p , refl

-- Strong normalization/neutrality definition
--------------------------------------------------------------------------------

data SN {Γ A} (t : Tm Γ A) : Set where
  sn : (∀ {t'} → t ~> t' → SN t') → SN t

SNₑ→ : ∀ {Γ Δ A}{t : Tm Γ A}(σ : OPE Δ Γ) → SN t → SN (Tmₑ σ t)
SNₑ→ σ (sn s) = sn λ {t'} step →
  let (t'' , (p , q)) = Tmₑ~> step in coe (SN & q) (SNₑ→ σ (s p))

SNₑ← : ∀ {Γ Δ A}{t : Tm Γ A}(σ : OPE Δ Γ) → SN (Tmₑ σ t) → SN t
SNₑ← σ (sn s) = sn λ step → SNₑ← σ (s (~>ₑ σ step))

SN-app₁ : ∀ {Γ A B}{f : Tm Γ (A ⇒ B)}{a} → SN (app f a) → SN f
SN-app₁ (sn s) = sn λ f~>f' → SN-app₁ (s (app₁ f~>f'))

neu : ∀ {Γ A} → Tm Γ A → Set
neu (lam _)   = ⊥
neu _         = ⊤

neuₑ : ∀ {Γ Δ A}(σ : OPE Δ Γ)(t : Tm Γ A) → neu t → neu (Tmₑ σ t)
neuₑ σ (lam t)   nt = nt
neuₑ σ (var v)   nt = tt
neuₑ σ (app f a) nt = tt

-- The actual proof, by Kripke logical predicate
--------------------------------------------------------------------------------

Tmᴾ : ∀ {Γ A} → Tm Γ A → Set
Tmᴾ {Γ}{ι}     t = SN t
Tmᴾ {Γ}{A ⇒ B} t = ∀ {Δ}(σ : OPE Δ Γ){a} → Tmᴾ a → Tmᴾ (app (Tmₑ σ t) a)

data Subᴾ {Γ} : ∀ {Δ} → Sub Γ Δ → Set where
  ∙   : Subᴾ ∙
  _,_ : ∀ {A Δ}{σ : Sub Γ Δ}{t : Tm Γ A}(σᴾ : Subᴾ σ)(tᴾ : Tmᴾ t) → Subᴾ (σ , t)

Tmᴾₑ : ∀ {Γ Δ A}{t : Tm Γ A}(σ : OPE Δ Γ) → Tmᴾ t → Tmᴾ (Tmₑ σ t)
Tmᴾₑ {A = ι}        σ tᴾ = SNₑ→ σ tᴾ
Tmᴾₑ {A = A ⇒ B}{t} σ tᴾ δ aᴾ rewrite Tm-∘ₑ σ δ t ⁻¹ = tᴾ (σ ∘ₑ δ) aᴾ

Subᴾₑ : ∀ {Γ Δ Σ}{σ : Sub Δ Σ}(δ : OPE Γ Δ) → Subᴾ σ → Subᴾ (σ ₛ∘ₑ δ)
Subᴾₑ σ ∙        = ∙
Subᴾₑ σ (δ , tᴾ) = Subᴾₑ σ δ , Tmᴾₑ σ tᴾ

~>ᴾ : ∀ {Γ A}{t t' : Tm Γ A} → t ~> t' → Tmᴾ t → Tmᴾ t'
~>ᴾ {A = ι}     t~>t' (sn tˢⁿ) = tˢⁿ t~>t'
~>ᴾ {A = A ⇒ B} t~>t' tᴾ       = λ σ aᴾ → ~>ᴾ (app₁ (~>ₑ σ t~>t')) (tᴾ σ aᴾ)

mutual
  -- quote
  qᴾ : ∀ {Γ A}{t : Tm Γ A} → Tmᴾ t → SN t
  qᴾ {A = ι}     tᴾ = tᴾ
  qᴾ {A = A ⇒ B} tᴾ = SNₑ← wk $ SN-app₁ (qᴾ $ tᴾ wk (uᴾ (var vz) (λ ())))

  -- unquote
  uᴾ : ∀ {Γ A}(t : Tm Γ A){nt : neu t} → (∀ {t'} → t ~> t' → Tmᴾ t') → Tmᴾ t
  uᴾ {Γ} {A = ι} t      f     = sn f
  uᴾ {Γ} {A ⇒ B} t {nt} f {Δ} σ {a} aᴾ =
    uᴾ (app (Tmₑ σ t) a) (go (Tmₑ σ t) (neuₑ σ t nt) f' a aᴾ (qᴾ aᴾ))
    where
      f' : ∀ {t'} → Tmₑ σ t ~> t' → Tmᴾ t'
      f' step δ aᴾ with Tmₑ~> step
      ... | t'' , step' , refl rewrite Tm-∘ₑ σ δ t'' ⁻¹ = f step' (σ ∘ₑ δ) aᴾ

      go :
        ∀ {Γ A B}(t : Tm Γ (A ⇒ B)) → neu t → (∀ {t'} → t ~> t' → Tmᴾ t')
        → ∀ a → Tmᴾ a → SN a → ∀ {t'} → app t a ~> t' → Tmᴾ t'
      go _ () _ _ _ _ (β _ _)
      go t nt f a aᴾ sna (app₁ {f' = f'} step) =
        coe ((λ x → Tmᴾ (app x a)) & Tm-idₑ f') (f step idₑ aᴾ)
      go t nt f a aᴾ (sn aˢⁿ) (app₂ {a' = a'} step) =
        uᴾ (app t a') (go t nt f a' (~>ᴾ step aᴾ) (aˢⁿ step))

fundThm-∈ : ∀ {Γ A}(v : A ∈ Γ) → ∀ {Δ}{σ : Sub Δ Γ} → Subᴾ σ → Tmᴾ (∈ₛ σ v)
fundThm-∈ vz     (σᴾ , tᴾ) = tᴾ
fundThm-∈ (vs v) (σᴾ , tᴾ) = fundThm-∈ v σᴾ

fundThm-lam :
  ∀ {Γ A B}
    (t : Tm (Γ , A) B)
  → SN t
  → (∀ {a} → Tmᴾ a → Tmᴾ (Tmₛ (idₛ , a) t))
  → ∀ a → SN a → Tmᴾ a → Tmᴾ (app (lam t) a)
fundThm-lam {Γ} t (sn tˢⁿ) hyp a (sn aˢⁿ) aᴾ = uᴾ (app (lam t) a)
  λ {(β _ _) → hyp aᴾ;
     (app₁ (lam {t' = t'} t~>t')) →
       fundThm-lam t' (tˢⁿ t~>t') (λ aᴾ → ~>ᴾ (~>ₛ _ t~>t') (hyp aᴾ)) a (sn aˢⁿ) aᴾ;
     (app₂ a~>a') →
       fundThm-lam t (sn tˢⁿ) hyp _ (aˢⁿ a~>a') (~>ᴾ a~>a' aᴾ)}

fundThm : ∀ {Γ A}(t : Tm Γ A) → ∀ {Δ}{σ : Sub Δ Γ} → Subᴾ σ → Tmᴾ (Tmₛ σ t)
fundThm (var v) σᴾ = fundThm-∈ v σᴾ
fundThm (lam {A} t) {σ = σ} σᴾ δ {a} aᴾ
  rewrite Tm-ₛ∘ₑ (keepₛ σ) (keep δ) t ⁻¹ | assₛₑₑ σ (wk {A}) (keep δ) | idlₑ δ
  = fundThm-lam
      (Tmₛ (σ ₛ∘ₑ drop δ , var vz) t)
      (qᴾ (fundThm t (Subᴾₑ (drop δ) σᴾ , uᴾ (var vz) (λ ()))))
      (λ aᴾ → coe (Tmᴾ & sub-sub-lem) (fundThm t (Subᴾₑ δ σᴾ , aᴾ)))
      a (qᴾ aᴾ) aᴾ
  where
    sub-sub-lem : ∀ {a} → Tmₛ (σ ₛ∘ₑ δ , a) t ≡ Tmₛ (idₛ , a) (Tmₛ (σ ₛ∘ₑ drop δ , var vz) t)
    sub-sub-lem {a} =
        (λ x → Tmₛ (x , a) t) &
          (idrₛ (σ ₛ∘ₑ δ) ⁻¹ ◾ assₛₑₛ σ δ idₛ ◾ assₛₑₛ σ (drop δ) (idₛ , a) ⁻¹)
      ◾ Tm-∘ₛ (σ ₛ∘ₑ drop δ , var vz) (idₛ , a) t
fundThm (app f a) {σ = σ} σᴾ
  rewrite Tm-idₑ (Tmₛ σ f) ⁻¹
  = fundThm f σᴾ idₑ (fundThm a σᴾ)

idₛᴾ : ∀ {Γ} → Subᴾ (idₛ {Γ})
idₛᴾ {∙}     = ∙
idₛᴾ {Γ , A} = Subᴾₑ wk idₛᴾ , uᴾ (var vz) (λ ())

strongNorm : ∀ {Γ A}(t : Tm Γ A) → SN t
strongNorm t = qᴾ (coe (Tmᴾ & Tm-idₛ t) (fundThm t idₛᴾ))
