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
reduction sequence in the target also is a corresponding reduction
sequence in the source, a situation called a _bisimulation_.

Bisimulation is established by case analysis over all possible
reductions and all possible terms to which they are related.  For each
reduction step in the source we must show a corresponding reduction
sequence in the target for a simulation, and also vice-versa for a
bisimulation.

For instance, the source might be lambda calculus with _let_
added, and the target the same system with `let` translated out. 
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

Covering the other constructs of our language — for naturals,
fixpoints, products, and so on — would add little save length.


In this case, our relation can be specified by a function
from source to target.

    (x) †              =  x
    (ƛ x ⇒ N) †        =  ƛ x ⇒ (N †)
    (L · M) †          =  (L †) · (M †)
    `let x `= M `in N  =  (ƛ x ⇒ (N †)) · (M †)

And we have

    M † ≡ N
    -------
    M ~ N

But in general we may be given only the relation, without
any corresponding function.

Further, we also have a function from target to source.
In this case, it is trivial, since the source is a
subset of the target.

    (x) #              =  x
    (ƛ x ⇒ N) #        =  ƛ x ⇒ (N #)
    (L · M) #          =  (L #) · (M #)

And we have

    M ≡ N #
    -------
    M ~ N


    
    
## Reflection

In some cases, the relation can be specified by a pair of
functions, a _compiling_ function from the source to the
target, and a _decompiling_ function from the target to
the source.  Taking a transition in the source should be
equivalent to compiling, taking a transition in the source,
and decompiling.



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

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ---------------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ----------------------
    → `let M N ~ (ƛ N†) · M†
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
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    --------------------------------------------------
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~ exts σ† x)
~exts ~σ Z =  ~`
~exts ~σ (S x) =  ~rename S_ (~σ x)

~subst : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    -------------------------------------------------------------
  → (∀ {A} {Mₛ Mₜ : Γ ⊢ A} → Mₛ ~ Mₜ → subst σ Mₛ ~ subst σ† Mₜ)
~subst ~σ (~` {x = x}) = ~σ x
~subst ~σ (~ƛ ~N) = ~ƛ (~subst (~exts ~σ) ~N)
~subst ~σ (~L ~· ~M) = (~subst ~σ ~L) ~· (~subst ~σ ~M)
~subst ~σ (~let ~M ~N) = ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)

~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {V V† : Γ ⊢ B} 
  → N ~ N†
  → V ~ V†
    -----------------------
  → (N [ V ]) ~ (N† [ V† ])
~sub {Γ} {A} {B} ~N ~V = ~subst {Γ , B} {Γ} ~σ {A} ~N
  where
  ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
  ~σ Z      =  ~V
  ~σ (S x)  =  ~`
\end{code}

## The relation is a simulation, source to target

\begin{code}
data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

  leg : ∀ {N† : Γ ⊢ A}
    → N ~ N†
    → M† —→ N†
      --------
    → Leg M† N
\end{code}

\begin{code}
simul : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ M†
  → M —→ N
    ---------
  → Leg  M† N
simul ~`              ()
simul (~ƛ ~N)         ()
simul (~L ~· ~M)      (ξ-·₁ L—→)
  with simul ~L L—→
...  | leg ~L′ L†—→                   =  leg (~L′ ~· ~M)   (ξ-·₁ L†—→)
simul (~V ~· ~M)      (ξ-·₂ VV M—→)
  with simul ~M M—→
...  | leg ~M′ M†—→                   =  leg (~V ~· ~M′)   (ξ-·₂ (~val ~V VV) M†—→)
simul ((~ƛ ~N) ~· ~V) (β-ƛ VV)        =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
simul (~let ~M ~N)    (ξ-let M—→)
  with simul ~M M—→
...  | leg ~M′ M†—→                   =  leg (~let ~M′ ~N) (ξ-·₂ V-ƛ M†—→)
simul (~let ~V ~N)    (β-let VV)      =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
\end{code}

