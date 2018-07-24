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
save that every term will have exactly the same type, written `★`
and pronounced "any".
This matches a slogan introduced by Dana Scott
and echoed by Robert Harper: "Untyped is Uni-typed".
One consequence of this approach is that constructs which previously
had to be given separately (such as natural numbers and fixpoints)
can now be defined in the language itself.


## Syntax

First, we get all our infix declarations out of the way.

\begin{code}
infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infixl 7  _·_
\end{code}

## Types

We have just one type.
\begin{code}
data Type : Set where
  ★ : Type
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

## Variables and the lookup judgement

Inherently typed variables correspond to the lookup judgement.  The
rules are as before.
\begin{code}
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
     ---------
   → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
\end{code}
We could write the rules with all instances of `A` and `B`
replaced by `★`, but arguably it is clearer not to do so.

Because `★` is the only type, the judgement doesn't guarantee anything
useful about types.  But it does ensure that all variables are in
scope.  For instance, we cannot use `S S Z` in a context that only
binds two variables.


## Terms and the scoping judgement

Inherently typed terms correspond to the typing judgement, but with
`★` as the only type.  The result is that we check that terms are
well-scoped — that is, that all variables they mention are in scope —
but not that they are well-typed.
\begin{code}
data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  :  ∀ {Γ}
    → Γ , ★ ⊢ ★
      ---------
    → Γ ⊢ ★

  _·_ : ∀ {Γ}
    → Γ ⊢ ★
    → Γ ⊢ ★
      ------
    → Γ ⊢ ★
\end{code}
Now we have a tiny calculus, with only variables, abstraction, and
application.  Below we will see how to represent naturals and
fixpoints in this calculus.

## Writing variables as numerals

As before, we can convert a natural to the corresponding de Bruing
index.  We no longer need to lookup the type in the context, since
every variable has the same type.
\begin{code}
count : ∀ {Γ} → ℕ → Γ ∋ ★
count {Γ , ★} zero     =  Z
count {Γ , ★} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥
\end{code}

We can then introduce a convenient abbreviation for variables.
\begin{code}
#_ : ∀ {Γ} → ℕ → Γ ⊢ ★
# n  =  ` count n
\end{code}

## Test examples

Our only example is computing two plus two on Church numerals.
\begin{code}
twoᶜ : ∀ {Γ} → Γ ⊢ ★
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

fourᶜ : ∀ {Γ} → Γ ⊢ ★
fourᶜ = ƛ ƛ (# 1 · (# 1 · (# 1 · (# 1 · # 0))))

plusᶜ : ∀ {Γ} → Γ ⊢ ★
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

2+2ᶜ : ∅ ⊢ ★
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ
\end{code}
Before, reduction stopped when we reached a lambda term, so we had to
compute `` plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero `` to ensure we reduced
to a representation of the natural four.  Now, reduction continues
under lambda, so we don't need the extra arguments.  It is convenient
to define a term to represent four as a Church numeral, as well as
two.

## Renaming

Our definition of renaming is as before.  First, we need an extension lemma.
\begin{code}
ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
\end{code}
We could replace all instances of `A` and `B` by `★`, but arguably it is
clearer not to do so.

Now it is straighforward to define renaming.
\begin{code}
rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
\end{code}
This is exactly as before, save that there are fewer term forms.

## Simultaneous substitution

Our definition of substitution is also exactly as before.
First we need an extension lemma.
\begin{code}
exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)
\end{code}
Again, we could replace all instances of `A` and `B` by `★`.

Now it is straighforward to define substitution.
\begin{code}
subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
\end{code}
Again, this is exactly as before, save that there are fewer term forms.

## Single substitution

It is easy to define the special case of substitution for one free variable.
\begin{code}
_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B 
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x
\end{code}

## Neutral and normal terms

Reduction continues until a term is fully normalised.  Hence, instead
of values, we are now interested in _normal forms_.  Terms in normal
form are defined by mutual recursion with _neutral_ terms.

Neutral terms arise because we now consider reduction of open terms,
which may contain free variables.  A term that is just a variable
cannot reduce further, nor can a term of the form `x · M₁ · ... · Mₙ`

A term is
neutral if it is a variable or a neutral term applied to a normal
term.  A term is a normal form if it is neutral or an abstraction
where the body is a normal form.

CONTINUE FROM HERE

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

## Unicode

This chapter uses the following unicode.

    ★  U+2605  BLACK STAR (\st)

The `\st` command permits navigation among many different stars;
the one we use is number 7.
