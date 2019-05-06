\begin{code}
module extra.ComposeSubst where
\end{code}

I was having trouble proving a lemma about composition of subsitution.
To find the proof, I had to strip away the well-scoping requirements
for terms. Next I'm going to see if I can do the proof with
well-scoped terms. -Jeremy


## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat
open import Function using (_∘_)
\end{code}

\begin{code}
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
\end{code}

## Untyped Lambda Calculus

\begin{code}
Var : Set
Var = ℕ

data Term : Set where

  `_ :
      Var
      ----
    → Term

  ƛ_  :
      Term
      ----
    → Term

  _·_ : 
      Term
    → Term
      ----
    → Term

ext : (Var → Var)
      -----------
    → (Var → Var)
ext ρ zero      =  zero
ext ρ (suc x)   =  suc (ρ x)

rename : 
    (Var → Var)
    -------------
  → (Term → Term)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)

exts : (Var → Term)
       ------------
     → (Var → Term)
exts σ zero      =  ` zero
exts σ (suc x)  =  rename suc (σ x)

subst :
    (Var → Term)
    -------------
  → (Term → Term)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)


same-subst : (Var → Term) → (Var → Term) → Set
same-subst σ σ' = ∀{x : Var} → σ x ≡ σ' x


same-subst-ext : {σ σ' : Var → Term}
   → same-subst σ σ'
   → same-subst (exts σ) (exts σ' )
same-subst-ext ss {x = zero} = refl
same-subst-ext ss {x = suc x} = cong (rename suc) ss


subst-equal : {σ σ' : Var → Term}{M : Term}
        → same-subst σ σ' 
        → subst σ M ≡ subst σ' M
subst-equal {σ} {σ'} {` x} ss = ss
subst-equal {σ} {σ'} {ƛ M} ss =
   let ih = subst-equal {σ = exts σ}{σ' = exts σ'} {M = M}
            (λ {x} → same-subst-ext{σ}{σ'} ss {x}) in
   cong ƛ_ ih
subst-equal {σ} {σ'} {L · M} ss =
   let ih1 = subst-equal {σ} {σ'} {L} ss in
   let ih2 = subst-equal {σ} {σ'} {M} ss in
   cong₂ _·_ ih1 ih2


compose-ext : ∀{ρ ρ' : Var → Var} 
  → (ext ρ) ∘ (ext ρ') ≡ ext (ρ ∘ ρ') 
compose-ext{ρ}{ρ'} = extensionality lemma
  where
  lemma : (x : Var) → ext ρ (ext ρ' x) ≡ ext (ρ ∘ ρ') x
  lemma zero = refl
  lemma (suc x) = refl


compose-rename : ∀{M : Term}{ρ ρ' : Var → Var} 
  → rename ρ (rename ρ' M) ≡ rename (ρ ∘ ρ') M
compose-rename {` x} {ρ} {ρ'} = refl
compose-rename {ƛ N} {ρ} {ρ'} = cong ƛ_ G
  where IH : {ρ : Var → Var} {ρ' : Var → Var} →
               rename ρ (rename ρ' N) ≡ rename (ρ ∘ ρ') N
        IH = compose-rename {N}
        G : rename (ext ρ) (rename (ext ρ') N)
          ≡ rename (ext (ρ ∘ ρ')) N
        G =
          begin
            rename (ext ρ) (rename (ext ρ') N)
          ≡⟨ IH ⟩
            rename ((ext ρ) ∘ (ext ρ')) N
          ≡⟨ cong₂ rename compose-ext refl ⟩
            rename (ext (ρ ∘ ρ')) N
          ∎        
compose-rename {L · M} {ρ} {ρ'} = cong₂ _·_ compose-rename compose-rename


commute-subst-rename : ∀{M : Term}{σ : Var → Term}{ρ : Var → Var}
     → (∀{x : Var} → exts σ (ρ x) ≡ rename ρ (σ x))
     → subst (exts σ) (rename ρ M) ≡ rename ρ (subst σ M)
commute-subst-rename {` x} {σ}{ρ} r = r
commute-subst-rename {ƛ N} {σ}{ρ} r = cong ƛ_ G
   where
   IH : ∀ {σ : Var → Term}{ρ : Var → Var} 
      → (∀{x : Var} → exts σ (ρ x) ≡ rename ρ (σ x))
      → subst (exts σ) (rename ρ N) ≡ rename ρ (subst σ N)
   IH = commute-subst-rename {N}

   H : ∀{x : Var} →
        exts (exts σ) (ext ρ x) ≡ rename (ext ρ) (exts σ x)
   H {zero} = refl
   H {suc x} =
     begin
       rename suc (exts σ (ρ x)) 
     ≡⟨ cong₂ rename (extensionality (λ x₁ → refl)) r ⟩
       rename suc (rename ρ (σ x))
     ≡⟨ compose-rename ⟩
       rename (suc ∘ ρ) (σ x)
     ≡⟨ cong₂ rename (extensionality λ x₁ → refl) refl ⟩
       rename ((ext ρ) ∘ suc) (σ x)
     ≡⟨ sym compose-rename ⟩
       rename (ext ρ) (rename suc (σ x))
     ∎
   G : subst (exts (exts σ)) (rename (ext ρ) N) ≡
        rename (ext ρ) (subst (exts σ) N)
   G = IH{σ = exts σ}{ρ = ext ρ} (λ {x} → H{x})
commute-subst-rename {L · M} {σ} r =
  cong₂ _·_ (commute-subst-rename{L} r) (commute-subst-rename{M} r)


subst-exts : ∀{x : Var} {σ₁ σ₂ : Var → Term}
   → ((subst (exts σ₂)) ∘ (exts σ₁)) x ≡ exts ((subst σ₂) ∘ σ₁) x
subst-exts {zero} = refl
subst-exts {suc x}{σ₁}{σ₂} = G
   where
   G : ((subst (exts σ₂)) ∘ exts σ₁) (suc x) ≡ rename suc (((subst σ₂) ∘ σ₁) x)
   G =
     begin
       ((subst (exts σ₂)) ∘ exts σ₁) (suc x)
     ≡⟨⟩
       subst (exts σ₂) (rename suc (σ₁ x))
     ≡⟨ commute-subst-rename{σ₁ x}{σ₂}{suc} (λ {x₁} → refl) ⟩
       rename suc (subst σ₂ (σ₁ x))
     ≡⟨⟩
       rename suc (((subst σ₂) ∘ σ₁) x)
     ∎


subst-subst : ∀{M : Term} {σ₁ σ₂ : Var → Term} 
            → ((subst σ₂) ∘ (subst σ₁)) M ≡ subst (subst σ₂ ∘ σ₁) M
subst-subst {` x} {σ₁} {σ₂} = refl
subst-subst {ƛ N} {σ₁} {σ₂} = G
  where
  IH : ∀ {σ₁ σ₂ :  ℕ → Term} →
         ((subst σ₂) ∘ (subst σ₁)) N ≡ subst ((subst σ₂) ∘ σ₁) N
  IH = subst-subst {N}
  
  G : ((subst σ₂) ∘ subst σ₁) (ƛ N) ≡ (ƛ subst (exts ((subst σ₂) ∘ σ₁)) N)
  G =
     begin
      ((subst σ₂) ∘ subst σ₁) (ƛ N)
     ≡⟨⟩
      ƛ ((subst (exts σ₂)) ∘ (subst (exts σ₁))) N
     ≡⟨ cong ƛ_ (IH{σ₁ = exts σ₁}{σ₂ = exts σ₂}) ⟩
      ƛ subst ((subst (exts σ₂)) ∘ (exts σ₁)) N
     ≡⟨ cong ƛ_ (subst-equal{M = N} λ {x} → subst-exts{x}) ⟩
      (ƛ subst (exts ((subst σ₂) ∘ σ₁)) N)
     ∎
subst-subst {L · M} {σ₁} {σ₂} = cong₂ _·_ (subst-subst{L}) (subst-subst{M})
\end{code}
