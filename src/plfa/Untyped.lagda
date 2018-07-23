---
title     : "Untyped: Untyped lambda calculus with full normalisation"
layout    : page
permalink : /Untyped/
---

\begin{code}
module plfa.Untyped where
\end{code}

In this chapter we play with variations on a theme.

* Previous chapters consider inherently-typed calculi;
  here we consider one that is untyped but inherently scoped.

* Previous chapters consider call-by-value calculi;
  here we consider call-by-name.

* Previous chapters consider _weak head normal form_,
  where reduction stops at a lambda abstraction;
  here we consider _full normalisation_,
  where reduction continues underneath a lambda.

* Previous chapters consider reduction of _closed_ terms,
  those with no free variables;
  here we consider _open_ terms,
  those which may have free variables.

* Previous chapters consider lambda calculus extended
  with natural numbers and fixpoints;
  here we consider a tiny calculus with just variables,
  abstraction, and application.

In general, one may mix and match any of these features,
save that full normalisation requires open terms.
The aim of this chapter is to give some appreciation for
the range of different lambda calculi one may encounter.


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
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)
\end{code}


## Untyped is Uni-typed

Our development will be close to that in
Chapter [DeBruijn]({{ site.baseurl }}{% link out/plfa/DeBruijn.md %}),
save that every term will have exactly the same type, written `⋆`
and pronounced "any".
This matches a slogan introduced by Dana Scott
and echoed by Robert Harper: "Untyped is Uni-typed".
One consequence of this approach is that constructs which previously
had to be given separately (such as natural numbers and fixpoints)
can now be defined in the language itself.


## Syntax

First, we get all our infix declarations out of the way.

\begin{code}
{-
infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infixl 7  _·_
-}
\end{code}

## Types

We have just one type.
\begin{code}
data Type : Set where
  ⋆ : Type
\end{code}

#### Exercise (`Type≃⊤`)

Show that `Type` is isomorphic to `⊤`, the unit type.

## Contexts

As before, a context is a list of types, with the type of the
most recently bound variable on the right.
\begin{code}
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
\end{code}
We let `Γ` and `Δ` range over contexts.

#### Exercise (`Context≃ℕ`)

Show that `Context` is isomorphic to `ℕ`.

\begin{code}
{-
data Var : ℕ → Set where

  Z : ∀ {n}
     -----------
   → Var (suc n)

  S_ : ∀ {n}
    → Var n
      -----------
    → Var (suc n)
-}
\end{code}

\begin{code}
{-
data Term : ℕ → Set where

  ⌊_⌋ : ∀ {n}
    → Var n
      ------
    → Term n

  ƛ_  :  ∀ {n}
    → Term (suc n)
      ------------
    → Term n

  _·_ : ∀ {n}
    → Term n
    → Term n
      ------
    → Term n
-}
\end{code}

## Writing variables as numerals

\begin{code}
{-
#_ : ∀ {n} → ℕ → Term n
#_ {n} m  =  ⌊ h n m ⌋
  where
  h : ∀ n → ℕ → Var n
  h zero    _        =  ⊥-elim impossible
    where postulate impossible : ⊥
  h (suc n) 0        =  Z
  h (suc n) (suc m)  =  S (h n m)
-}
\end{code}

## Test examples

\begin{code}
{-
plus : ∀ {n} → Term n
plus = ƛ ƛ ƛ ƛ ⌊ S S S Z ⌋ · ⌊ S Z ⌋ · (⌊ S S Z ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)

two : ∀ {n} → Term n
two = ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)

four : ∀ {n} → Term n
four = ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))
-}
\end{code}

## Renaming

\begin{code}
{-
rename : ∀ {m n} → (Var m → Var n) → (Term m → Term n)
rename ρ ⌊ k ⌋            =  ⌊ ρ k ⌋
rename {m} {n} ρ (ƛ N)    =  ƛ (rename {suc m} {suc n} ρ′ N)
  where
  ρ′ : Var (suc m) → Var (suc n)
  ρ′ Z      =  Z
  ρ′ (S k)  =  S (ρ k)
rename ρ (L · M)           =  (rename ρ L) · (rename ρ M)
-}
\end{code}

## Substitution

\begin{code}
{-
subst : ∀ {m n} → (Var m → Term n) → (Term m → Term n)
subst ρ ⌊ k ⌋                =  ρ k
subst {m} {n} ρ (ƛ N)        =  ƛ (subst {suc m} {suc n} ρ′ N)
  where
  ρ′ : Var (suc m) → Term (suc n)
  ρ′ Z      =  ⌊ Z ⌋
  ρ′ (S k)  =  rename {n} {suc n} S_ (ρ k)
subst ρ (L · M)               =  (subst ρ L) · (subst ρ M)

_[_] : ∀ {n} → Term (suc n) → Term n → Term n
_[_] {n} N M  =  subst {suc n} {n} ρ N
  where
  ρ : Var (suc n) → Term n
  ρ Z      =  M
  ρ (S k)  =  ⌊ k ⌋
-}
\end{code}

## Normal

\begin{code}
{-
data Neutral : ∀ {n} → Term n → Set
data Normal  : ∀ {n} → Term n → Set

data Neutral where

  ⌊_⌋  : ∀ {n}
    → (x : Var n)
      -------------
    → Neutral ⌊ x ⌋

  _·_  : ∀ {n} {L : Term n} {M : Term n}
    → Neutral L
    → Normal M
      ---------------
    → Neutral (L · M)

data Normal where

  ƛ_  : ∀ {n} {N : Term (suc n)}
    → Normal N
      ------------
    → Normal (ƛ N)

  ⌈_⌉ : ∀ {n} {M : Term n}
    → Neutral M
      ---------
    → Normal M
-}
\end{code}

## Reduction step

\begin{code}
{-
infix 2 _⟶_

Application : ∀ {n} → Term n → Set
Application ⌊ _ ⌋    =  ⊥
Application (ƛ _)    =  ⊥
Application (_ · _)  =  ⊤

data _⟶_ : ∀ {n} → Term n → Term n → Set where

  ξ₁ : ∀ {n} {L L′ M : Term n}
    → Application L
    → L ⟶ L′
      ----------------
    → L · M ⟶ L′ · M

  ξ₂ : ∀ {n} {L M M′ : Term n}
    → Neutral L
    → M ⟶ M′
      ----------------
    → L · M ⟶ L · M′

  β : ∀ {n} {N : Term (suc n)} {M : Term n}
      -------------------------------------
    → (ƛ N) · M ⟶ N [ M ]

  ζ : ∀ {n} {N N′ : Term (suc n)}
    → N ⟶ N′
      -----------
    → ƛ N ⟶ ƛ N′
-}
\end{code}

## Reflexive and transitive closure

\begin{code}
{-
infix  2 _⟶*_
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3 _∎

data _⟶*_ : ∀ {n} → Term n → Term n → Set where

  _∎ : ∀ {n} (M : Term n)
      ---------------------
    → M ⟶* M

  _⟶⟨_⟩_ : ∀ {n} (L : Term n) {M N : Term n}
    → L ⟶ M
    → M ⟶* N
      ---------
    → L ⟶* N

begin_ : ∀ {n} {M N : Term n} → (M ⟶* N) → (M ⟶* N)
begin M⟶*N = M⟶*N
-}
\end{code}


## Example reduction sequences

\begin{code}
{-
id : Term zero
id = ƛ ⌊ Z ⌋

_ : id · id  ⟶* id
_ =
  begin
    (ƛ ⌊ Z ⌋) · (ƛ ⌊ Z ⌋)
  ⟶⟨ β ⟩
    ƛ ⌊ Z ⌋
  ∎

_ : plus {zero} · two · two ⟶* four
_ =
  begin
    plus · two · two
  ⟶⟨ ξ₁ tt β ⟩
    (ƛ ƛ ƛ two · ⌊ S Z ⌋ · (⌊ S (S Z) ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)) · two
  ⟶⟨ β ⟩
    ƛ ƛ two · ⌊ S Z ⌋ · (two · ⌊ S Z ⌋ · ⌊ Z ⌋)
  ⟶⟨ ζ (ζ (ξ₁ tt β)) ⟩
    ƛ ƛ (ƛ ⌊ S (S Z) ⌋ · (⌊ S (S Z) ⌋ · ⌊ Z ⌋)) · (two · ⌊ S Z ⌋ · ⌊ Z ⌋)
  ⟶⟨ ζ (ζ β) ⟩
    ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (two · ⌊ S Z ⌋ · ⌊ Z ⌋))
  ⟶⟨ ζ (ζ (ξ₂ ⌊ S Z ⌋ (ξ₂ ⌊ S Z ⌋ (ξ₁ tt β)))) ⟩
    ƛ ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ((ƛ ⌊ S (S Z) ⌋ · (⌊ S (S Z) ⌋ · ⌊ Z ⌋)) · ⌊ Z ⌋))
  ⟶⟨ ζ (ζ (ξ₂ ⌊ S Z ⌋ (ξ₂ ⌊ S Z ⌋ β))) ⟩
   ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))))
  ∎
-}
\end{code}


## Progress

\begin{code}
{-
data Progress {n} (M : Term n) : Set where

  step : ∀ {N : Term n}
    → M ⟶ N
      ----------
    → Progress M

  done :
      Normal M
      ----------
    → Progress M

progress : ∀ {n} → (M : Term n) → Progress M
progress ⌊ x ⌋                                 =  done ⌈ ⌊ x ⌋ ⌉
progress (ƛ N)  with  progress N
... | step N⟶N′                              =  step (ζ N⟶N′)
... | done Nⁿ                                  =  done (ƛ Nⁿ)
progress (⌊ x ⌋ · M) with progress M
... | step M⟶M′                              =  step (ξ₂ ⌊ x ⌋ M⟶M′)
... | done Mⁿ                                  =  done ⌈ ⌊ x ⌋ · Mⁿ ⌉
progress ((ƛ N) · M)                           =  step β
progress (L@(_ · _) · M) with progress L
... | step L⟶L′                              =  step (ξ₁ tt L⟶L′)
... | done ⌈ Lᵘ ⌉ with progress M
...    | step M⟶M′                           =  step (ξ₂ Lᵘ M⟶M′)
...    | done Mⁿ                               =  done ⌈ Lᵘ · Mⁿ ⌉
-}
\end{code}


## Normalise

\begin{code}
{-
Gas : Set
Gas = ℕ

data Normalise {n} (M : Term n) : Set where

  out-of-gas : ∀ {N : Term n}
    → M ⟶* N
      -------------
    → Normalise M

  normal : ∀ {N : Term n}
    → Gas
    → M ⟶* N
    → Normal N
     --------------
    → Normalise M

normalise : ∀ {n}
  → Gas
  → ∀ (M : Term n)
    -------------
  → Normalise M
normalise zero L                         =  out-of-gas (L ∎)
normalise (suc g) L with progress L
... | done Lⁿ                            =  normal (suc g) (L ∎) Lⁿ
... | step {M} L⟶M with normalise g M
...     | out-of-gas M⟶*N              =  out-of-gas (L ⟶⟨ L⟶M ⟩ M⟶*N)
...     | normal g′ M⟶*N Nⁿ            =  normal g′ (L ⟶⟨ L⟶M ⟩ M⟶*N) Nⁿ
-}
\end{code}

\begin{code}
{-
_ : normalise 100 (plus {zero} · two · two) ≡
  normal 94
  ((ƛ
    (ƛ
     (ƛ
      (ƛ ⌊ S (S (S Z)) ⌋ · ⌊ S Z ⌋ · (⌊ S (S Z) ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋)))))
   · (ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))
   · (ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))
   ⟶⟨ ξ₁ tt β ⟩
   (ƛ
    (ƛ
     (ƛ
      (ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))) · ⌊ S Z ⌋ ·
      (⌊ S (S Z) ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋))))
   · (ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))
   ⟶⟨ β ⟩
   ƛ
   (ƛ
    (ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))) · ⌊ S Z ⌋ ·
    ((ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))) · ⌊ S Z ⌋ · ⌊ Z ⌋))
   ⟶⟨ ζ (ζ (ξ₁ tt β)) ⟩
   ƛ
   (ƛ
    (ƛ ⌊ S (S Z) ⌋ · (⌊ S (S Z) ⌋ · ⌊ Z ⌋)) ·
    ((ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))) · ⌊ S Z ⌋ · ⌊ Z ⌋))
   ⟶⟨ ζ (ζ β) ⟩
   ƛ
   (ƛ
    ⌊ S Z ⌋ ·
    (⌊ S Z ⌋ ·
     ((ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))) · ⌊ S Z ⌋ · ⌊ Z ⌋)))
   ⟶⟨ ζ (ζ (ξ₂ ⌊ S Z ⌋ (ξ₂ ⌊ S Z ⌋ (ξ₁ tt β)))) ⟩
   ƛ
   (ƛ
    ⌊ S Z ⌋ ·
    (⌊ S Z ⌋ · ((ƛ ⌊ S (S Z) ⌋ · (⌊ S (S Z) ⌋ · ⌊ Z ⌋)) · ⌊ Z ⌋)))
   ⟶⟨ ζ (ζ (ξ₂ ⌊ S Z ⌋ (ξ₂ ⌊ S Z ⌋ β))) ⟩
   ƛ (ƛ ⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))) ∎)
  (ƛ
   (ƛ
    ⌈ ⌊ S Z ⌋ · ⌈ ⌊ S Z ⌋ · ⌈ ⌊ S Z ⌋ · ⌈ ⌊ S Z ⌋ · ⌈ ⌊ Z ⌋ ⌉ ⌉ ⌉ ⌉ ⌉))
_ = refl
-}
\end{code}
