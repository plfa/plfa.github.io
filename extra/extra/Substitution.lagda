\begin{code}
module extra.Substitution where
\end{code}

## Imports

\begin{code}
open import plfa.Untyped
  using (Type; Context; _⊢_; ★; _∋_; ∅; _,_; Z; S_; `_; ƛ_; _·_; rename; subst;
         ext; exts; _[_]; subst-zero)
open import plfa.Denotational using (Rename)
open import plfa.Soundness using (Subst)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Function using (_∘_)
\end{code}

## Overview 

The primary purpose of this chapter is to prove that substitution
commutes with itself. Barendgredt (1984) refers to this
as the substitution lemma:
  
    M[x:=N][y:=L] = M [y:=L] [x:= N[y:=L] ]

In our setting, with de Bruijn indices for variables, the statement of
the lemma becomes:

    M [ N ] [ L ] ≡  M〔 L 〕[ N [ L ] ]

where the notation M 〔 L 〕 is for subsituting L for index 1 inside M.


Also, because our substitution is based on parallel substitution,
we have the following generalization, replacing the substitution
of L with an arbitrary parallel substitution σ.

    subst σ (M [ N ]) ≡ (subst (exts σ) M) [ subst σ N ]

The special case for renamings is also useful.

    rename ρ (M [ N ]) ≡ (rename (ext ρ) M) [ rename ρ N ]


The secondary purpose of this chapter is to define an algebra of
parallel substitution due to Abadi, Cardelli, Curien, and Levy
(1991). Not only do the equations of this algebra help us prove the
substitution lemma, but when applied from left to right, they form a
rewrite system that _decides_ whether two substitutions are equal.







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
rename-equal {ρ = ρ} {ρ' = ρ'} {M = ƛ N} s =
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

subst-equal : ∀{Γ Δ}{σ σ' : Subst Γ Δ}{A}{M : Γ ⊢ A}
            → same-subst σ σ' 
            → subst σ M ≡ subst σ' M
subst-equal {Γ} {Δ} {σ} {σ'} {A} {` x} ss = ss
subst-equal {Γ} {Δ} {σ} {σ'} {A} {ƛ M} ss =
   let ih = subst-equal {Γ = Γ , ★} {Δ = Δ , ★}
            {σ = exts σ}{σ' = exts σ'} {M = M}
            (λ {x}{A} → same-subst-ext {Γ}{Δ}{σ}{σ'} ss {x}{A}) in
   cong ƛ_ ih
subst-equal {Γ} {Δ} {σ} {σ'} {A} {L · M} ss =
   let ih1 = subst-equal {Γ} {Δ} {σ} {σ'} {A} {L} ss in
   let ih2 = subst-equal {Γ} {Δ} {σ} {σ'} {A} {M} ss in
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

\begin{code}
ids : ∀{Γ} → Subst Γ Γ
ids {A} x = ` x

cons : ∀{Γ Δ A} → (Δ ⊢ A) → Subst Γ Δ → Subst (Γ , A) Δ
cons {Γ} {Δ} {A} M σ {B} Z = M
cons {Γ} {Δ} {A} M σ {B} (S x) = σ x

seq : ∀{Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
seq σ τ = (subst τ) ∘ σ

ren : ∀{Γ Δ} → Rename Γ Δ → Subst Γ Δ
ren ρ = ids ∘ ρ

ren-ext : ∀ {Γ Δ}{B C : Type} {ρ : Rename Γ Δ} {x : Γ , B ∋ C}
        → (ren (ext ρ)) x ≡ exts (ren ρ) x
ren-ext {x = Z} = refl
ren-ext {x = S x} = refl

rename-seq-ren : ∀ {Γ Δ}{A} {ρ : Rename Γ Δ}{M : Γ ⊢ A}
               → rename ρ M ≡ subst (ren ρ) M
rename-seq-ren {M = ` x} = refl
rename-seq-ren {ρ = ρ}{M = ƛ N} =
  cong ƛ_ G
  where IH : rename (ext ρ) N ≡ subst (ren (ext ρ)) N
        IH = rename-seq-ren {ρ = ext ρ}{M = N} 

        G : rename (ext ρ) N ≡ subst (exts (ren ρ)) N
        G =
          begin
            rename (ext ρ) N
          ≡⟨ IH ⟩
            subst (ren (ext ρ)) N
          ≡⟨ subst-equal {M = N} ren-ext ⟩
            subst (exts (ren ρ)) N
          ∎
rename-seq-ren {M = L · M} = cong₂ _·_ rename-seq-ren rename-seq-ren


exts-cons-shift : ∀{Γ Δ : Context} {A : Type}{B : Type} {σ : Subst Γ Δ}{x}
    → exts σ {A}{B} x ≡ cons (` Z) (seq σ (ren S_)) x
exts-cons-shift {x = Z} = refl
exts-cons-shift {x = S x} = rename-seq-ren

ren-ext-cons-shift : ∀ {Γ Δ}{B C : Type} {ρ : Rename Γ Δ} {x : Γ , B ∋ C}
  → ren (ext ρ) x ≡ cons (` Z) (seq (ren ρ) (ren S_)) x
ren-ext-cons-shift{Γ}{Δ}{B}{C}{ρ}{x} =
   begin
       ren (ext ρ) x
     ≡⟨ ren-ext ⟩
       exts (ren ρ) x
     ≡⟨ exts-cons-shift{x = x} ⟩
       cons (` Z) (seq (ren ρ) (ren S_)) x
   ∎

subst-cons-Z : ∀{Γ Δ : Context}{A : Type}{M : Δ ⊢ A}{σ : Subst Γ Δ}
             → subst (cons M σ) (` Z) ≡ M
subst-cons-Z = refl

seq-inc-cons : ∀{Γ Δ : Context} {A B : Type} {M : Δ ⊢ A} {σ : Subst Γ Δ}
                {x : Γ ∋ B}
         → seq (ren S_) (cons M σ) x ≡ σ x
seq-inc-cons = refl

ids-id : ∀{Γ : Context}{A : Type} {M : Γ ⊢ A}
         → subst ids M ≡ M
ids-id = subst-id λ {A} {x} → refl

cons-ext : ∀{Γ Δ : Context} {A B : Type} {σ : Subst (Γ , A) Δ} {x : Γ , A ∋ B}
         → cons (subst σ (` Z)) (seq (ren S_) σ) x ≡ σ x
cons-ext {x = Z} = refl
cons-ext {x = S x} = refl

id-seq : ∀{Γ Δ : Context} {B : Type} {σ : Subst Γ Δ} {x : Γ ∋ B}
       → (seq ids σ) x ≡ σ x
id-seq = refl

seq-id : ∀{Γ Δ : Context} {B : Type} {σ : Subst Γ Δ} {x : Γ ∋ B}
       → (seq σ ids) x ≡ σ x
seq-id {Γ}{σ = σ}{x = x} =
          begin
            (seq σ ids) x
          ≡⟨⟩
            subst ids (σ x)
          ≡⟨ ids-id ⟩
            σ x
          ∎

seq-assoc : ∀{Γ Δ Σ Ψ : Context}{B} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
             {θ : Subst Σ Ψ} {x : Γ ∋ B}
          → seq (seq σ τ) θ x ≡ seq σ (seq τ θ) x
seq-assoc{Γ}{Δ}{Σ}{Ψ}{B}{σ}{τ}{θ}{x} =
          begin
            seq (seq σ τ) θ x
          ≡⟨⟩
            subst θ (subst τ (σ x))
          ≡⟨ subst-subst{M = σ x} ⟩
            (subst ((subst θ) ∘ τ)) (σ x)
          ≡⟨⟩
            seq σ (seq τ θ) x
          ∎

seq-cons :  ∀{Γ Δ Σ : Context} {A B} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
              {M : Δ ⊢ A} {x : Γ , A ∋ B}
         → seq (cons M σ) τ x ≡ cons (subst τ M) (seq σ τ) x
seq-cons {x = Z} = refl
seq-cons {x = S x} = refl

cons-zero-S : ∀{Γ}{A B}{x : Γ , A ∋ B} → cons (` Z) (ren S_) x ≡ ids x
cons-zero-S {x = Z} = refl
cons-zero-S {x = S x} = refl
\end{code}

\begin{code}
seq-congL : ∀{Γ Δ Σ : Context} {B} {σ σ' : Subst Γ Δ} {τ : Subst Δ Σ}
            {x : Γ ∋ B}
          → (∀{x : Γ ∋ B} → σ x ≡ σ' x)
          → seq σ τ x ≡ seq σ' τ x
seq-congL {τ = τ}{x = x} s = cong (subst τ) s

seq-congR : ∀{Γ Δ Σ : Context} {B} {σ : Subst Γ Δ} {τ τ' : Subst Δ Σ}
            {x : Γ ∋ B}
          → (∀{A}{x : Δ ∋ A} → τ x ≡ τ' x)
          → seq σ τ x ≡ seq σ τ' x
seq-congR {Γ}{Δ}{Σ}{B}{σ}{τ}{τ'}{x} s =
     begin
       seq σ τ x
     ≡⟨⟩
       subst τ (σ x)
     ≡⟨ subst-equal{M = σ x} s ⟩
       subst τ' (σ x)
     ≡⟨⟩
       seq σ τ' x
     ∎

cons-congL : ∀{Γ Δ : Context} {A B} {σ : Subst Γ Δ} {M M' : Δ ⊢ A}
            {x : Γ , A ∋ B}
           → M ≡ M'
           → cons M σ x ≡ cons M' σ x
cons-congL{σ = σ}{x = x} s = cong (λ z → cons z σ x) s

cons-congR : ∀{Γ Δ : Context} {A B} {σ τ : Subst Γ Δ} {M : Δ ⊢ A}
            {x : Γ , A ∋ B}
           → (∀{x : Γ ∋ B} → σ x ≡ τ x)
           → cons M σ x ≡ cons M τ x
cons-congR {x = Z} s = refl
cons-congR {x = S x} s = s
\end{code}

\begin{code}
subst-zero-cons-ids : ∀{Γ}{A B : Type}{M : Γ ⊢ B}{x : Γ , B ∋ A}
                    → subst-zero M x ≡ cons M ids x
subst-zero-cons-ids {x = Z} = refl
subst-zero-cons-ids {x = S x} = refl
\end{code}

\begin{code}
rename-subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {Γ}{Δ}{N}{M}{ρ} =
     begin
       (rename (ext ρ) N) [ rename ρ M ]
     ≡⟨⟩
       subst (subst-zero (rename ρ M)) (rename (ext ρ) N)
     ≡⟨ subst-equal{M = rename (ext ρ) N}
           (λ {A}{x} → subst-zero-cons-ids{x = x}) ⟩
       subst (cons (rename ρ M) ids) (rename (ext ρ) N)
     ≡⟨ (subst-equal{M = rename (ext ρ) N}
             λ{A}{x} → cons-congL {σ = ids}{x = x} rename-seq-ren) ⟩
       subst (cons (subst (ren ρ) M) ids) (rename (ext ρ) N)
     ≡⟨ cong (subst (cons (subst (ren ρ) M) ids))
           (rename-seq-ren{ρ = ext ρ}{M = N}) ⟩
       subst (cons (subst (ren ρ) M) ids) (subst (ren (ext ρ)) N)
     ≡⟨ subst-subst {M = N} ⟩
       subst (seq (ren (ext ρ)) (cons (subst (ren ρ) M) ids)) N
     ≡⟨ (subst-equal{M = N}
             λ{A}{x} → seq-congL{σ = ren (ext ρ)}
                         {σ' = (cons (` Z) (seq (ren ρ) (ren S_)))}{x = x}
             λ{x} → ren-ext-cons-shift{ρ = ρ}{x = x} ) ⟩
       subst (seq (cons (` Z) (seq (ren ρ) (ren S_)))
                  (cons (subst (ren ρ) M) ids)) N
     ≡⟨ (subst-equal{M = N} λ{A}{x} → seq-cons{x = x} ) ⟩
       subst (cons (subst (cons (subst (ren ρ) M) ids) (` Z))
           (seq (seq (ren ρ) (ren S_)) (cons (subst (ren ρ) M) ids))) N
     ≡⟨ subst-equal{M = N} (λ{A}{x} → cons-congL{x = x}
                (subst-cons-Z{σ = ids})) ⟩
       subst (cons (subst (ren ρ) M)
                   (seq (seq (ren ρ) (ren S_)) (cons (subst (ren ρ) M) ids))) N
     ≡⟨ subst-equal{M = N} (λ{A}{x} → cons-congR{x = x}
         (λ{x} → seq-assoc {σ = ren ρ} {τ = ren S_}
                           {θ = (cons (subst (ren ρ) M) ids)} {x = x})) ⟩
       subst (cons (subst (ren ρ) M)
                   (seq (ren ρ) (seq (ren S_) (cons (subst (ren ρ) M) ids)))) N
     ≡⟨ (subst-equal{M = N}λ{A}{x} → cons-congR{x = x}
            λ{x} → seq-congR {σ = ren ρ}
                             {τ = (seq (ren S_) (cons (subst (ren ρ) M) ids))}
                             {τ' = ids} {x = x}
            λ{A}{x} → seq-inc-cons {M = (subst (ren ρ) M)} {σ = ids} {x = x} ) ⟩
       subst (cons (subst (ren ρ) M) (seq (ren ρ) ids)) N
     ≡⟨ (subst-equal{M = N}λ{A}{x} → sym (seq-cons{x = x}) ) ⟩
       subst (seq (cons M ids) (ren ρ)) N
     ≡⟨ sym (subst-subst {M = N}) ⟩
       subst (ren ρ) (subst (cons M ids) N)
     ≡⟨ sym (rename-seq-ren) ⟩
       rename ρ (subst (cons M ids) N)
     ≡⟨ cong (rename ρ) (subst-equal{M = N}
           (λ {A}{x} → sym (subst-zero-cons-ids{x = x}))) ⟩
       rename ρ (subst (subst-zero M) N)
     ≡⟨⟩
       rename ρ (N [ M ])
     ∎
\end{code}

\begin{code}
subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{σ : Subst Γ Δ }
    → (subst (exts σ) N) [ subst σ M ] ≡ subst σ (N [ M ])
subst-commute {Γ}{Δ}{N}{M}{σ} =
     begin
       (subst (exts σ) N) [ subst σ M ]
     ≡⟨⟩
       subst (subst-zero (subst σ M)) (subst (exts σ) N)
     ≡⟨ subst-equal{M = subst (exts σ) N}
            (λ {A}{x} → subst-zero-cons-ids{A = A}{x = x}) ⟩
       subst (cons (subst σ M) ids) (subst (exts σ) N)
     ≡⟨ subst-subst{M = N} ⟩
       subst (seq (exts σ) (cons (subst σ M) ids)) N
     ≡⟨ subst-equal{M = N}
         (λ {A}{x} → seq-congL{σ = exts σ}{σ' = (cons (` Z) (seq σ (ren S_)))}
            {x = x} (λ {x} → exts-cons-shift{x = x}) ) ⟩
       subst (seq (cons (` Z) (seq σ (ren S_))) (cons (subst σ M) ids)) N
     ≡⟨ subst-equal{M = N} (λ {A}{x} → seq-cons{M = ` Z}{x = x}) ⟩
       subst (cons (subst (cons (subst σ M) ids) (` Z))
                   (seq (seq σ (ren S_)) (cons (subst σ M) ids))) N
     ≡⟨⟩
       subst (cons (subst σ M)
                   (seq (seq σ (ren S_)) (cons (subst σ M) ids))) N
     ≡⟨ subst-equal{M = N} (λ {A} {x} → cons-congR {x = x}
           λ {x} → seq-assoc{σ = σ}) ⟩
       subst (cons (subst σ M)
                   (seq σ (seq (ren S_) (cons (subst σ M) ids)))) N
     ≡⟨ (subst-equal{M = N} λ {A} {x} → cons-congR {x = x}
          λ {x} → seq-congR {σ = σ}
          λ {A}{x} → seq-inc-cons{M = subst σ M}{σ = ids}) ⟩
       subst (cons (subst σ M) (seq σ ids)) N
     ≡⟨ (subst-equal{M = N} λ {A} {x} → cons-congR{x = x} (seq-id{σ = σ})) ⟩
       subst (cons (subst σ M) σ) N
     ≡⟨ subst-equal{M = N} (λ {A}{x} → cons-congR{x = x} (id-seq{σ = σ})) ⟩
       subst (cons (subst σ M) (seq ids σ)) N
     ≡⟨ (subst-equal{M = N} λ {A}{x} → sym (seq-cons{x = x})) ⟩
       subst (seq (cons M ids) σ) N
     ≡⟨ sym (subst-subst{M = N}) ⟩
       subst σ (subst (cons M ids) N)
     ≡⟨ cong (subst σ) (sym (subst-equal{M = N}
          λ {A}{x} → subst-zero-cons-ids{x = x})) ⟩
       subst σ (N [ M ])
     ∎
\end{code}

\begin{code}
_〔_〕 : ∀ {Γ A B C}
        → Γ , B , C ⊢ A
        → Γ ⊢ B
          ---------
        → Γ , C ⊢ A
_〔_〕 {Γ} {A} {B} {C} N M =
   subst {Γ , B , C} {Γ , C} (exts (subst-zero M)) {A} N
\end{code}

\begin{code}
substitution : ∀{Γ}{M : Γ , ★ , ★ ⊢ ★}{N : Γ , ★ ⊢ ★}{L : Γ ⊢ ★}
    → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution{M = M}{N = N}{L = L} =
   sym (subst-commute{N = M}{M = N}{σ = subst-zero L})
\end{code}


## Notes

Most of the properties and proofs in this file are based on the paper
_Autosubst: Reasoning with de Bruijn Terms and Parallel Substitution_
by Schafer, Tebbi, and Smolka (ITP 2015).

