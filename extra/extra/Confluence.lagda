\begin{code}
module extra.Confluence where
\end{code}

## Imports

\begin{code}
open import extra.Substitution
open import plfa.Untyped
   renaming (_—→_ to _——→_; _—↠_ to _——↠_; begin_ to commence_; _∎ to _fini)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Function using (_∘_)
\end{code}

## Reduction without the restrictions

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ₁ : ∀ {Γ} {L L′ M : Γ ⊢ ★}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂ : ∀ {Γ} {L M M′ : Γ ⊢ ★}
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β : ∀ {Γ} {N : Γ , ★ ⊢ ★} {M : Γ ⊢ ★}
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  ζ : ∀ {Γ} {N N′ : Γ , ★ ⊢ ★}
    → N —→ N′
      -----------
    → ƛ N —→ ƛ N′
\end{code}

\begin{code}
infix  2 _—↠_
infix  1 start_
infixr 2 _—→⟨_⟩_
infix  3 _[]

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _[] : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

start_ : ∀ {Γ} {A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
start M—↠N = M—↠N
\end{code}

\begin{code}
—↠-trans : ∀{Γ}{L M N : Γ ⊢ ★}
         → L —↠ M
         → M —↠ N
         → L —↠ N
—↠-trans (M []) mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)
\end{code}

## Congruences

\begin{code}
abs-cong : ∀ {Γ} {N N' : Γ , ★ ⊢ ★}
         → N —↠ N'
           ----------
         → ƛ N —↠ ƛ N'
abs-cong (M []) = ƛ M []
abs-cong (L —→⟨ r ⟩ rs) = ƛ L —→⟨ ζ r ⟩ abs-cong rs

appL-cong : ∀ {Γ} {L L' M : Γ ⊢ ★}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong {Γ}{L}{L'}{M} (L []) = L · M []
appL-cong {Γ}{L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁ r ⟩ appL-cong rs

appR-cong : ∀ {Γ} {L M M' : Γ ⊢ ★}
         → M —↠ M'
           ---------------
         → L · M —↠ L · M'
appR-cong {Γ}{L}{M}{M'} (M []) = L · M []
appR-cong {Γ}{L}{M}{M'} (M —→⟨ r ⟩ rs) = L · M —→⟨ ξ₂ r ⟩ appR-cong rs
\end{code}

## Parallel Reduction

\begin{code}
infix 2 _⇒_

data _⇒_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  pvar : ∀{Γ A}{x : Γ ∋ A}
         ---------
       → (` x) ⇒ (` x)

  pabs : ∀{Γ}{N N' : Γ , ★ ⊢ ★}
       → N ⇒ N'
         ----------
       → ƛ N ⇒ ƛ N'

  papp : ∀{Γ}{L L' M M' : Γ ⊢ ★}
       → L ⇒ L'  →  M ⇒ M'
         -----------------
       → L · M ⇒ L' · M'

  pbeta : ∀{Γ}{N N'  : Γ , ★ ⊢ ★}{M M' : Γ ⊢ ★}
       → N ⇒ N'  →  M ⇒ M'
         -----------------------
       → (ƛ N) · M  ⇒  N' [ M' ]
\end{code}

## Proof of Confluence

\begin{code}
par-refl : ∀{Γ A}{M : Γ ⊢ A} → M ⇒ M
par-refl {Γ} {A} {` x} = pvar
par-refl {Γ} {★} {ƛ N} = pabs par-refl
par-refl {Γ} {★} {L · M} = papp par-refl par-refl
\end{code}

\begin{code}
beta-par : ∀{Γ A}{M N : Γ ⊢ A}
         → M —→ N
           ------
         → M ⇒ N
beta-par {Γ} {★} {L · M} (ξ₁ r) =
   papp (beta-par {M = L} r) par-refl
beta-par {Γ} {★} {L · M} (ξ₂ r) =
   papp par-refl (beta-par {M = M} r) 
beta-par {Γ} {★} {(ƛ N) · M} β =
   pbeta par-refl par-refl
beta-par {Γ} {★} {ƛ N} (ζ r) =
   pabs (beta-par r)
\end{code}

\begin{code}
par-beta : ∀{Γ A}{M N : Γ ⊢ A}
         → M ⇒ N
           ------
         → M —↠ N
par-beta {Γ} {A} {.(` _)} (pvar{x = x}) = (` x) []
par-beta {Γ} {★} {ƛ N} (pabs p) =
   abs-cong (par-beta p)
par-beta {Γ} {★} {L · M} (papp p₁ p₂) =
   —↠-trans (appL-cong{M = M} (par-beta p₁)) (appR-cong (par-beta p₂))
par-beta {Γ} {★} {(ƛ N) · M} (pbeta{N' = N'}{M' = M'} p₁ p₂) =
  let ih₁ = par-beta p₁ in
  let ih₂ = par-beta p₂ in
  let a : (ƛ N) · M —↠ (ƛ N') · M
      a = appL-cong{M = M} (abs-cong ih₁) in
  let b : (ƛ N') · M —↠ (ƛ N') · M'
      b = appR-cong{L = ƛ N'} ih₂ in
  let c = (ƛ N') · M' —→⟨ β ⟩ N' [ M' ] [] in
  —↠-trans (—↠-trans a b) c
\end{code}

\begin{code}
Rename : Context → Context → Set
Rename Γ Δ = ∀{A} → Γ ∋ A → Δ ∋ A
\end{code}

\begin{code}
Subst : Context → Context → Set
Subst Γ Δ = ∀{A} → Γ ∋ A → Δ ⊢ A
\end{code}

\begin{code}
par-subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
par-subst {Γ}{Δ} σ₁ σ₂ = ∀{A}{x : Γ ∋ A} → σ₁ x ⇒ σ₂ x
\end{code}

\begin{code}
rename-subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {Γ}{Δ}{N}{M}{ρ} =
   {!!}
\end{code}

\begin{code}
par-rename : ∀{Γ Δ A} {ρ : Rename Γ Δ} {M M' : Γ ⊢ A}
  → M ⇒ M'
    ------------------------
  → rename ρ M ⇒ rename ρ M'
par-rename pvar = pvar
par-rename (pabs p) = pabs (par-rename p)
par-rename (papp p₁ p₂) = papp (par-rename p₁) (par-rename p₂)
par-rename {Γ}{Δ}{A}{ρ} (pbeta{Γ}{N}{N'}{M}{M'} p₁ p₂)
     with pbeta (par-rename{ρ = ext ρ} p₁) (par-rename{ρ = ρ} p₂)
... | G rewrite rename-subst-commute{Γ}{Δ}{N'}{M'}{ρ} = G
\end{code}

\begin{code}
par-subst-ext : ∀{Γ Δ} {σ τ : Subst Γ Δ}
   → par-subst σ τ
   → par-subst (exts σ {B = ★}) (exts τ)
par-subst-ext s {x = Z} = pvar
par-subst-ext s {x = S x} = par-rename s
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
subst-zero-cons-ids : ∀{Γ}{A B : Type}{M : Γ ⊢ B}{x : Γ , B ∋ A}
                    → subst-zero M x ≡ cons M ids x
subst-zero-cons-ids {x = Z} = refl
subst-zero-cons-ids {x = S x} = refl
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
     ≡⟨ {!!} ⟩
       subst (seq (cons (` Z) (seq σ (ren S_))) (cons (subst σ M) ids)) N
     ≡⟨ {!!} ⟩
       subst (cons (subst (cons (subst σ M) ids) (` Z))
                   (seq (seq σ (ren S_)) (cons (subst σ M) ids))) N
     ≡⟨ {!!} ⟩
       subst (cons (subst σ M)
                   (seq (seq σ (ren S_)) (cons (subst σ M) ids))) N
     ≡⟨ {!!} ⟩
       subst (cons (subst σ M)
                   (seq σ (seq (ren S_) (cons (subst σ M) ids)))) N
     ≡⟨ {!!} ⟩
       subst (cons (subst σ M) (seq σ ids)) N
     ≡⟨ {!!} ⟩
       subst (cons (subst σ M) σ) N
     ≡⟨ {!!} ⟩
       subst (cons (subst σ M) (seq ids σ)) N
     ≡⟨ {!!} ⟩
       subst (seq (cons M ids) σ) N
     ≡⟨ sym (subst-subst{M = N}) ⟩
       subst σ (subst (cons M ids) N)
     ≡⟨ {!!} ⟩
       subst σ (N [ M ])
     ∎
\end{code}

\begin{code}
subst-par : ∀{Γ Δ A} {σ τ : Subst Γ Δ} {M M' : Γ ⊢ A}
   → par-subst σ τ  →  M ⇒ M'
     --------------------------
   → subst σ M ⇒ subst τ M'
subst-par {Γ} {Δ} {A} {σ} {τ} {` x} s pvar = s
subst-par {Γ} {Δ} {★} {σ} {τ} {ƛ N} s (pabs p) =
   pabs (subst-par {σ = exts σ} {τ = exts τ}
            (λ {A}{x} → par-subst-ext s {A}{x}) p)
subst-par {Γ} {Δ} {★} {σ} {τ} {L · M} s (papp p₁ p₂) =
   papp (subst-par s p₁) (subst-par s p₂)
subst-par {Γ} {Δ} {★} {σ} {τ} {(ƛ N) · M} s (pbeta{N' = N'}{M' = M'} p₁ p₂)
    with pbeta (subst-par{σ = exts σ}{τ = exts τ}{M = N}
                        (λ {A}{x} → par-subst-ext s {A}{x}) p₁)
               (subst-par (λ {A}{x} → s{A}{x}) p₂)
... | G rewrite subst-commute{N = N'}{M = M'}{σ = τ} =
    G
\end{code}
