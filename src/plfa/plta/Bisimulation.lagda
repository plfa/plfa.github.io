---
title     : "Bisimulation: Relating reduction systems"
layout    : page
permalink : /Bisimulation/
---

\begin{code}
module plta.Bisimulation where
\end{code}


## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import plta.More
\end{code}


## Bisimulation

\begin{code}
infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

data _~_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where

  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {Nₛ Nₜ : Γ , A ⊢ B}
    → Nₛ ~ Nₜ
      -----------
    → ƛ Nₛ ~ ƛ Nₜ

  _~·_ : ∀ {Γ A B} {Lₛ Lₜ : Γ ⊢ A ⇒ B} {Mₛ Mₜ : Γ ⊢ A}
    → Lₛ ~ Lₜ
    → Mₛ ~ Mₜ
      -----------------
    → Lₛ · Mₛ ~ Lₜ · Mₜ

  ~let : ∀ {Γ A B} {Mₛ Mₜ : Γ ⊢ A} {Nₛ Nₜ : Γ , A ⊢ B}
    → Mₛ ~ Mₜ
    → Nₛ ~ Nₜ
      ------------------------
    → `let Mₛ Nₛ ~ (ƛ Nₜ) · Mₜ
\end{code}

## Bisimulation commutes with values

\begin{code}
~val : ∀ {Γ A} {Vₛ Vₜ : Γ ⊢ A} 
  → Vₛ ~ Vₜ
  → Value Vₛ
    --------
  → Value Vₜ
~val ~`           ()
~val (~ƛ ~V)      V-ƛ  =  V-ƛ
~val (~L ~· ~M)   ()
~val (~let ~M ~N) ()
\end{code}


## Bisimulation commutes with renaming

\begin{code}
~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
    -------------------------------------------------------------
  → (∀ {A} {Mₛ Mₜ : Γ ⊢ A} → Mₛ ~ Mₜ → rename ρ Mₛ ~ rename ρ Mₜ)
~rename ρ (~` {x = x}) = ~`
~rename ρ (~ƛ ~N) = ~ƛ (~rename (ext ρ) ~N)
~rename ρ (~L ~· ~M) = (~rename ρ ~L) ~· (~rename ρ ~M)
~rename ρ (~let ~M ~N) = ~let (~rename ρ ~M) (~rename (ext ρ) ~N)
\end{code}

## Bisimulation commutes with substitution

\begin{code}
~exts : ∀ {Γ Δ}
  → {σₛ : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σₜ : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σₛ x ~ σₜ x)
    ---------------------------------------------------
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σₛ x ~ exts σₜ x)
~exts ~σ Z =  ~`
~exts ~σ (S x) =  ~rename S_ (~σ x)

~subst : ∀ {Γ Δ}
  → {σₛ : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σₜ : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σₛ x ~ σₜ x)
    -------------------------------------------------------------
  → (∀ {A} {Mₛ Mₜ : Γ ⊢ A} → Mₛ ~ Mₜ → subst σₛ Mₛ ~ subst σₜ Mₜ)
~subst ~σ (~` {x = x}) = ~σ x
~subst ~σ (~ƛ ~N) = ~ƛ (~subst (~exts ~σ) ~N)
~subst ~σ (~L ~· ~M) = (~subst ~σ ~L) ~· (~subst ~σ ~M)
~subst ~σ (~let ~M ~N) = ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)

~sub : ∀ {Γ A B} {Nₛ Nₜ : Γ , B ⊢ A} {Vₛ Vₜ : Γ ⊢ B} 
  → Nₛ ~ Nₜ
  → Vₛ ~ Vₜ
    -------------------------
  → (Nₛ [ Vₛ ]) ~ (Nₜ [ Vₜ ])
~sub {Γ} {A} {B} ~N ~V = ~subst {Γ , B} {Γ} ~σ {A} ~N
  where
  ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
  ~σ Z      =  ~V
  ~σ (S x)  =  ~`
\end{code}

## The given relation is a bisimulation

\begin{code}
data Bisim {Γ A} (Mₛ Mₜ Mₛ′ : Γ ⊢ A) : Set where

  bi : ∀ {Mₜ′ : Γ ⊢ A}
    → Mₛ′ ~ Mₜ′
    → Mₜ —→ Mₜ′
      ---------------
    → Bisim Mₛ Mₜ Mₛ′

bisim : ∀ {Γ A} {Mₛ Mₜ Mₛ′ : Γ ⊢ A}
  → Mₛ ~ Mₜ
  → Mₛ —→ Mₛ′
    ---------------
  → Bisim Mₛ Mₜ Mₛ′
bisim ~`              ()
bisim (~ƛ ~N)         ()
bisim (~L ~· ~M)      (ξ-·₁ L—→)
  with bisim ~L L—→
...  | bi ~L′ —→L′                   =  bi (~L′ ~· ~M)   (ξ-·₁ —→L′)
bisim (~V ~· ~M)      (ξ-·₂ VV M—→)
  with bisim ~M M—→
...  | bi ~M′ —→M′                   =  bi (~V ~· ~M′)   (ξ-·₂ (~val ~V VV) —→M′)
bisim ((~ƛ ~N) ~· ~V) (β-ƛ VV)       =  bi (~sub ~N ~V)  (β-ƛ (~val ~V VV))
bisim (~let ~M ~N)    (ξ-let M—→)
  with bisim ~M M—→
...  | bi ~M′ —→M′                   =  bi (~let ~M′ ~N) (ξ-·₂ V-ƛ —→M′)
bisim (~let ~V ~N)    (β-let VV)     =  bi (~sub ~N ~V)  (β-ƛ (~val ~V VV))
\end{code}
