\begin{code}
module extra.Confluence where
\end{code}

## Imports

\begin{code}
open import extra.Substitution
open import plfa.Untyped
   renaming (_—→_ to _——→_; _—↠_ to _——↠_; begin_ to start_; _∎ to _[])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app)
{- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎) -}
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
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
\end{code}

\begin{code}
—↠-trans : ∀{Γ}{L M N : Γ ⊢ ★}
         → L —↠ M
         → M —↠ N
         → L —↠ N
—↠-trans (M ∎) mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)
\end{code}

## Congruences

\begin{code}
abs-cong : ∀ {Γ} {N N' : Γ , ★ ⊢ ★}
         → N —↠ N'
           ----------
         → ƛ N —↠ ƛ N'
abs-cong (M ∎) = ƛ M ∎
abs-cong (L —→⟨ r ⟩ rs) = ƛ L —→⟨ ζ r ⟩ abs-cong rs

appL-cong : ∀ {Γ} {L L' M : Γ ⊢ ★}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong {Γ}{L}{L'}{M} (L ∎) = L · M ∎
appL-cong {Γ}{L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁ r ⟩ appL-cong rs

appR-cong : ∀ {Γ} {L M M' : Γ ⊢ ★}
         → M —↠ M'
           ---------------
         → L · M —↠ L · M'
appR-cong {Γ}{L}{M}{M'} (M ∎) = L · M ∎
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
par-beta {Γ} {A} {.(` _)} (pvar{x = x}) = (` x) ∎
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
  let c = (ƛ N') · M' —→⟨ β ⟩ N' [ M' ] ∎ in
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
{-
   let x = commute-subst-rename{σ = subst-zero M}{ρ = ρ} ? in
-}
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
subst-par : ∀{Γ Δ A} {σ₁ σ₂ : Subst Γ Δ} {M M' : Γ ⊢ A}
   → par-subst σ₁ σ₂  →  M ⇒ M'
     --------------------------
   → subst σ₁ M ⇒ subst σ₂ M'
subst-par {Γ} {Δ} {A} {σ₁} {σ₂} {` x} s pvar = s
subst-par {Γ} {Δ} {★} {σ₁} {σ₂} {ƛ N} s (pabs p) =
  let ih = subst-par {σ₁ = exts σ₁}{σ₂ = exts σ₂} {!!} p in
  pabs {!!}
  where
    H : par-subst (exts σ₁ {B = ★}) (exts σ₂)
    H {★} {Z} = pvar
    H {A} {S x} = {!!}

subst-par {Γ} {Δ} {★} {σ₁} {σ₂} {L · M} s (papp p p₁) = {!!}
subst-par {Γ} {Δ} {★} {σ₁} {σ₂} {(ƛ N) · M} s (pbeta p p₁) = {!!}
\end{code}
