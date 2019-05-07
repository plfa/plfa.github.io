\begin{code}
module extra.Substitution where
\end{code}

## Imports

\begin{code}
open import plfa.Untyped
  using (Type; Context; _⊢_; ★; _∋_; ∅; _,_; Z; S_; `_; ƛ_; _·_; rename; subst;
         ext; exts; _[_]; subst-zero)
  renaming (_∎ to _[])
open import plfa.Denotational using (Rename)
open import plfa.Soundness using (Subst)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Function using (_∘_)
\end{code}

## Properties of renaming and substitution


\begin{code}
same-rename : ∀{Γ Δ} → Rename Γ Δ → Rename Γ Δ → Set
same-rename{Γ}{Δ} σ σ' = ∀{A}{x : Γ ∋ A} → σ x ≡ σ' x

same-rename-ext : ∀{Γ Δ}{σ σ' : Rename Γ Δ}
   → same-rename σ σ'
   → same-rename (ext σ {B = ★}) (ext σ' )
same-rename-ext ss {x = Z} = refl
same-rename-ext ss {x = S x} = cong S_ ss

rename-equal : ∀{Γ Δ}{ρ ρ' : Rename Γ Δ}{M : Γ ⊢ ★}
        → same-rename ρ ρ'
        → rename ρ M ≡ rename ρ' M
rename-equal {M = ` x} s = cong `_ s
rename-equal {ρ = ρ}{ρ' = ρ'}{M = ƛ N} s =
   cong ƛ_ (rename-equal {ρ = ext ρ}{ρ' = ext ρ'}{M = N} (same-rename-ext s))
rename-equal {M = L · M} s = cong₂ _·_ (rename-equal s) (rename-equal s)
\end{code}

\begin{code}
same-subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
same-subst{Γ}{Δ} σ σ' = ∀{A}{x : Γ ∋ A} → σ x ≡ σ' x

same-subst-ext : ∀{Γ Δ}{σ σ' : Subst Γ Δ}{B}
   → same-subst σ σ'
   → same-subst (exts σ {B = B}) (exts σ' )
same-subst-ext ss {x = Z} = refl
same-subst-ext ss {x = S x} = cong (rename (λ {A} → S_)) ss

subst-equal : ∀{Γ Δ}{σ σ' : Subst Γ Δ}{M : Γ ⊢ ★}
            → same-subst σ σ' 
            → subst σ M ≡ subst σ' M
subst-equal {Γ} {Δ} {σ} {σ'} {` x} ss = ss
subst-equal {Γ} {Δ} {σ} {σ'} {ƛ M} ss =
   let ih = subst-equal {Γ = Γ , ★} {Δ = Δ , ★}
            {σ = exts σ}{σ' = exts σ'} {M = M}
            (λ {x}{A} → same-subst-ext {Γ}{Δ}{σ}{σ'} ss {x}{A}) in
   cong ƛ_ ih
subst-equal {Γ} {Δ} {σ} {σ'} {L · M} ss =
   let ih1 = subst-equal {Γ} {Δ} {σ} {σ'} {L} ss in
   let ih2 = subst-equal {Γ} {Δ} {σ} {σ'} {M} ss in
   cong₂ _·_ ih1 ih2
\end{code}

\begin{code}
compose-ext : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ' : Rename Γ Δ} {A B} {x : Γ , B ∋ A}
            → ((ext ρ) ∘ (ext ρ')) x ≡ ext (ρ ∘ ρ') x
compose-ext {x = Z} = refl
compose-ext {x = S x} = refl
\end{code}

\begin{code}
compose-rename : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A}{ρ : Rename Δ Σ}{ρ' : Rename Γ Δ} 
  → rename ρ (rename ρ' M) ≡ rename (ρ ∘ ρ') M
compose-rename {M = ` x} = refl
compose-rename {Γ}{Δ}{Σ}{A}{ƛ N}{ρ}{ρ'} = cong ƛ_ G
  where
  IH : rename ( ext ρ) (rename ( ext ρ') N) ≡ rename ((ext ρ) ∘ (ext ρ')) N
  IH = compose-rename{Γ , ★}{Δ , ★}{Σ , ★}{★}{N}{ext ρ}{ext ρ'}
  G : rename (ext ρ) (rename (ext ρ') N) ≡ rename (ext (ρ ∘ ρ')) N
  G =
      begin
        rename (ext ρ) (rename (ext ρ') N)
      ≡⟨ IH ⟩
        rename ((ext ρ) ∘ (ext ρ')) N
      ≡⟨ rename-equal compose-ext ⟩
        rename (ext (ρ ∘ ρ')) N
      ∎        
compose-rename {M = L · M} =
   cong₂ _·_ compose-rename compose-rename
\end{code}


\begin{code}
commute-subst-rename : ∀{Γ Δ}{M : Γ ⊢ ★}{σ : Subst Γ Δ}
                        {ρ : ∀{Γ} → Rename Γ (Γ , ★)}
     → (∀{x : Γ ∋ ★} → exts σ {B = ★} (ρ x) ≡ rename ρ (σ x))
     → subst (exts σ {B = ★}) (rename ρ M) ≡ rename ρ (subst σ M)
commute-subst-rename {M = ` x} r = r
commute-subst-rename{Γ}{Δ}{ƛ N}{σ}{ρ} r = cong ƛ_ IH
   where
   ρ' : ∀ {Γ} → Rename Γ (Γ , ★)
   ρ' {∅} = λ ()
   ρ' {Γ , ★} = ext ρ

   H : {x : Γ , ★ ∋ ★} → exts (exts σ) (ext ρ x) ≡ rename (ext ρ) (exts σ x)
   H {Z} = refl
   H {S x} =
     begin
       rename S_ (exts σ (ρ x)) 
     ≡⟨ cong (rename S_) r ⟩
       rename S_ (rename ρ (σ x))
     ≡⟨ compose-rename ⟩
       rename (S_ ∘ ρ) (σ x)
     ≡⟨ rename-equal (λ {A} {x₁} → refl) ⟩
       rename ((ext ρ) ∘ S_) (σ x)
     ≡⟨ sym compose-rename ⟩
       rename (ext ρ) (rename S_ (σ x))
     ∎
   IH : subst (exts (exts σ)) (rename (ext ρ) N) ≡
          rename (ext ρ) (subst (exts σ) N)
   IH = commute-subst-rename{Γ , ★}{Δ , ★}{N}
           {exts σ}{ρ = ρ'} (λ {x} → H {x})

commute-subst-rename {M = L · M}{ρ = ρ} r =
   cong₂ _·_ (commute-subst-rename{M = L}{ρ = ρ} r)
             (commute-subst-rename{M = M}{ρ = ρ} r)
\end{code}


\begin{code}
subst-exts : ∀{Γ Δ Δ'}{A}{x : Γ , ★ ∋ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Δ'}
   → ((subst (exts σ₂)) ∘ (exts σ₁)) x ≡ exts ((subst σ₂) ∘ σ₁) x
subst-exts {x = Z} = refl
subst-exts {A = ★}{x = S x}{σ₁}{σ₂} = G
   where
   G : ((subst (exts σ₂)) ∘ exts σ₁) (S x) ≡ rename S_ (((subst σ₂) ∘ σ₁) x)
   G =
     begin
       ((subst (exts σ₂)) ∘ exts σ₁) (S x)
     ≡⟨⟩
       subst (exts σ₂) (rename S_ (σ₁ x))
     ≡⟨ commute-subst-rename{M = σ₁ x}{σ = σ₂}{ρ = S_} (λ {x₁} → refl) ⟩
       rename S_ (subst σ₂ (σ₁ x))
     ≡⟨⟩
       rename S_ (((subst σ₂) ∘ σ₁) x)
     ∎
\end{code}


\begin{code}
subst-subst : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ} 
            → ((subst σ₂) ∘ (subst σ₁)) M ≡ subst (subst σ₂ ∘ σ₁) M
subst-subst {M = ` x} = refl
subst-subst {Γ}{Δ}{Σ}{A}{ƛ N}{σ₁}{σ₂} = G
  where
  G : ((subst σ₂) ∘ subst σ₁) (ƛ N) ≡ (ƛ subst (exts ((subst σ₂) ∘ σ₁)) N)
  G =
     begin
      ((subst σ₂) ∘ subst σ₁) (ƛ N)
     ≡⟨⟩
      ƛ ((subst (exts σ₂)) ∘ (subst (exts σ₁))) N
     ≡⟨ cong ƛ_ (subst-subst{M = N}{σ₁ = exts σ₁}{σ₂ = exts σ₂}) ⟩
      ƛ subst ((subst (exts σ₂)) ∘ (exts σ₁)) N
     ≡⟨ cong ƛ_ (subst-equal{M = N} (λ {A}{x} → subst-exts{x = x})) ⟩
      (ƛ subst (exts ((subst σ₂) ∘ σ₁)) N)
     ∎
subst-subst {M = L · M} = cong₂ _·_ (subst-subst{M = L}) (subst-subst{M = M})
\end{code}


\begin{code}
rename-subst : ∀{Γ Δ Δ'}{M : Γ ⊢ ★}{ρ : Rename Γ Δ}{σ : Subst Δ Δ'}
             → ((subst σ) ∘ (rename ρ)) M ≡ subst (σ ∘ ρ) M
rename-subst {M = ` x} = refl
rename-subst {Γ}{Δ}{Δ'}{M = ƛ M}{ρ}{σ} =
  let ih : subst (exts σ) (rename (ext ρ) M)
           ≡ subst ((exts σ) ∘ ext ρ) M
      ih = rename-subst {M = M}{ρ = ext ρ}{σ = exts σ} in
  cong ƛ_ g
  where
        ss : same-subst ((exts σ) ∘ (ext ρ)) (exts (σ ∘ ρ))
        ss {A} {Z} = refl
        ss {A} {S x} = refl
        h : subst ((exts σ) ∘ (ext ρ)) M ≡ subst (exts (σ ∘ ρ)) M
        h = subst-equal{Γ , ★}{Δ = Δ' , ★}{σ = ((exts σ) ∘ (ext ρ))}
             {σ' = (exts (σ ∘ ρ))}{M = M} (λ {A} {x} → ss{A}{x})
        g : subst (exts σ) (rename (ext ρ) M)
           ≡ subst (exts (σ ∘ ρ)) M
        g =
           begin
             subst (exts σ) (rename (ext ρ) M)
           ≡⟨ rename-subst {M = M}{ρ = ext ρ}{σ = exts σ} ⟩
             subst ((exts σ) ∘ ext ρ) M
           ≡⟨ h ⟩
             subst (exts (σ ∘ ρ)) M
           ∎
rename-subst {M = L · M} =
   cong₂ _·_ (rename-subst{M = L}) (rename-subst{M = M})
\end{code}


\begin{code}
is-id-subst : ∀{Γ} → Subst Γ Γ → Set
is-id-subst {Γ} σ = ∀{A}{x : Γ ∋ A} → σ x ≡ ` x

is-id-exts : ∀{Γ} {σ : Subst Γ Γ}
           → is-id-subst σ
           → is-id-subst (exts σ {B = ★})
is-id-exts id {x = Z} = refl
is-id-exts{Γ}{σ} id {x = S x} rewrite id {x = x} = refl

subst-id : ∀{Γ : Context}{A : Type} {M : Γ ⊢ A} {σ : Subst Γ Γ}
         → is-id-subst σ
         → subst σ M ≡ M
subst-id {M = ` x} {σ} id = id
subst-id {M = ƛ M} {σ} id = cong ƛ_ (subst-id (is-id-exts id))
subst-id {M = L · M} {σ} id = cong₂ _·_ (subst-id id) (subst-id id)
\end{code}

