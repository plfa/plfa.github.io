---
title     : "Bisimulation: Relating reduction systems"
layout    : page
permalink : /Bisimulation/
---

\begin{code}
module plfa.Bisimulation where
\end{code}

Some constructs can be defined in terms of other constructs.  In the
previous chapter, we saw how _let_ terms can be rewritten as an
application of an abstraction, and how two alternative formulations of
products — one with projections and one with case — can be formulated
in terms of each other.  In this chapter, we look at how to formalise
these claims.  In particular, we explain what it means to claim that
two different systems, with different terms and reduction rules, are
equivalent.

The relevant concept is _bisimulation_.  Consider two different
systems, let's call them _source_ and _target_.  Let `M`, `N` range
over terms of the source, and `M†`, `N†` range over terms of the
target.  We define a relation

    M ~ M†

between corresponding terms of the two systems. We have a
_simulation_ of the source by the target if every reduction
sequence in the source has a corresponding reduction sequence
in the target:

> For every `M`, `M†`, and `N`:
> If `M ~ M†` and `M —↠ N`
> then `M† —↠ N†` and `N ~ N†`
> for some `N†`.
        
Or, in a diagram:

    M  --- —↠ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —↠ --- N†

We are particularly interested in the situation where every
reduction sequence in the target also has a corresponding reduction
sequence in the source, a situation called a _bisimulation_.

Bisimulation is established by case analysis over all possible
reductions and all possible relations.  For each reduction step in the
source we must show a corresponding reduction sequence in the target
for a simulation, and also vice-versa for a bisimulation.

For instance, `S` might be lambda calculus with _let_
added, and `T` the same system with `let` translated out. 
The key rule defining our relation will be:

    M ~ M†
    N ~ N†
    ---------------------------------
    `let x `= M `in N ~ ((ƛ x ⇒ N) M)

All the other rules are congruences: variables relate to
themselves, and abstractions and applications relate if their
components relate.

    -----
    x ~ x

    N ~ N†
    ------------------
    ƛ x ⇒ N ~ ƛ x ⇒ N†

    L ~ L†
    M ~ M†
    ---------------
    L · M ~ L† · M†

Covering the other cases would add little to our exposition,
save length.

In this case, our relation can be specified by a function.

    (x) †              =  x
    (ƛ x ⇒ N) †        =  ƛ x ⇒ (N †)
    (L · M) †          =  (L †) · (M †)
    `let x `= M `in N  =  (ƛ x ⇒ (N †)) · (M †)

And we have

    M † ≡ N
    =======
    M ~ N   
    
where the double rule between the two formulas stands for
"if and only if".  But in general we may have only a relation,
rather than a function.

    


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
open import plfa.More
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

**Actually, I think this is just a simulation!**

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
