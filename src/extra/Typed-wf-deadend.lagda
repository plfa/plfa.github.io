---
title     : "Typed: Typed Lambda term representation"
layout    : page
permalink : /Typed
---


## Imports

\begin{code}
module Typed where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; foldr; filter)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)
open import Collections

pattern [_]     x      =  x ∷ []
pattern [_,_]   x y    =  x ∷ y ∷ []
pattern [_,_,_] x y z  =  x ∷ y ∷ z ∷ []
\end{code}


## Syntax

\begin{code}
infix   4  _wf
infix   4  _∉_
infix   4  _∋_`:_
infix   4  _⊢_`:_
infixl  5  _,_`:_
infixr  6  _`→_
infix   6  `λ_`→_
infixl  7  `if0_then_else_
infix   8  `suc_ `pred_ `Y_
infixl  9  _·_
infix  10  S_

Id : Set
Id = String

data Type : Set where
  `ℕ   : Type
  _`→_ : Type → Type → Type

data Env : Set where
  ε      : Env
  _,_`:_ : Env → Id → Type → Env

data Term : Set where
  `_              : Id → Term
  `λ_`→_          : Id → Term → Term
  _·_             : Term → Term → Term
  `zero           : Term    
  `suc_           : Term → Term
  `pred_          : Term → Term
  `if0_then_else_ : Term → Term → Term → Term
  `Y_             : Term → Term

data _∋_`:_ : Env → Id → Type → Set where

  Z : ∀ {Γ A x}
      --------------------
    → Γ , x `: A ∋ x `: A

  S_ : ∀ {Γ A B x w}
    → Γ ∋ w `: B
      --------------------
    → Γ , x `: A ∋ w `: B

_∉_ : Id → Env → Set
x ∉ Γ = ∀ {A} → ¬ (Γ ∋ x `: A)

data _⊢_`:_ : Env → Term → Type → Set where

  Ax : ∀ {Γ A x}
    → Γ ∋ x `: A
      --------------
    → Γ ⊢ ` x `: A

  ⊢λ : ∀ {Γ x N A B}
    → x ∉ Γ
    → Γ , x `: A ⊢ N `: B
      --------------------------
    → Γ ⊢ (`λ x `→ N) `: A `→ B

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L `: A `→ B
    → Γ ⊢ M `: A
      ----------------
    → Γ ⊢ L · M `: B

  ⊢zero : ∀ {Γ}
      ----------------
    → Γ ⊢ `zero `: `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M `: `ℕ
      -----------------
    → Γ ⊢ `suc M `: `ℕ

  ⊢pred : ∀ {Γ M}
    → Γ ⊢ M `: `ℕ
      ------------------
    → Γ ⊢ `pred M `: `ℕ

  ⊢if0 : ∀ {Γ L M N A}
    → Γ ⊢ L `: `ℕ
    → Γ ⊢ M `: A
    → Γ ⊢ N `: A
      ------------------------------
    → Γ ⊢ `if0 L then M else N `: A

  ⊢Y : ∀ {Γ M A}
    → Γ ⊢ M `: A `→ A
      ----------------
    → Γ ⊢ `Y M `: A

data _wf : Env → Set where

  empty :
     -----
     ε wf

  extend : ∀ {Γ x A}
    → Γ wf
    → x ∉ Γ
      -------------------------
    → (Γ , x `: A) wf
\end{code}

## Test examples

\begin{code}
two : Term
two = `suc `suc `zero

⊢two : ε ⊢ two `: `ℕ
⊢two = (⊢suc (⊢suc ⊢zero))

plus : Term
plus = `Y (`λ "p" `→ `λ "m" `→ `λ "n" `→ `if0 ` "m" then ` "n" else ` "p" · (`pred ` "m") · ` "n")

⊢plus : ε ⊢ plus `: `ℕ `→ `ℕ `→ `ℕ
⊢plus = (⊢Y (⊢λ p∉ (⊢λ m∉ (⊢λ n∉
          (⊢if0 (Ax ⊢m) (Ax ⊢n) (Ax ⊢p · (⊢pred (Ax ⊢m)) · Ax ⊢n))))))
  where
  ⊢p = S S Z
  ⊢m = S Z
  ⊢n = Z
  Γ₀ = ε
  Γ₁ = Γ₀ , "p" `: `ℕ `→ `ℕ `→ `ℕ
  Γ₂ = Γ₁ , "m" `: `ℕ
  p∉ : "p" ∉ Γ₀
  p∉ ()
  m∉ : "m" ∉ Γ₁
  m∉ (S ())
  n∉ : "n" ∉ Γ₂
  n∉ (S S ())

four : Term
four = plus · two · two

⊢four : ε ⊢ four `: `ℕ
⊢four = ⊢plus · ⊢two · ⊢two

Ch : Type
Ch = (`ℕ `→ `ℕ) `→ `ℕ `→ `ℕ

twoCh : Term
twoCh = `λ "s" `→ `λ "z" `→ (` "s" · (` "s" · ` "z"))

⊢twoCh : ε ⊢ twoCh `: Ch
⊢twoCh = (⊢λ s∉ (⊢λ z∉ (Ax ⊢s · (Ax ⊢s · Ax ⊢z))))
  where
  ⊢s = S Z
  ⊢z = Z
  Γ₀ = ε
  Γ₁ = Γ₀ , "s" `: `ℕ `→ `ℕ
  s∉ : "s" ∉ ε
  s∉ ()
  z∉ : "z" ∉ Γ₁
  z∉ (S ())

plusCh : Term
plusCh = `λ "m" `→ `λ "n" `→ `λ "s" `→ `λ "z" `→
           ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

⊢plusCh : ε ⊢ plusCh `: Ch `→ Ch `→ Ch
⊢plusCh = (⊢λ m∉ (⊢λ n∉ (⊢λ s∉ (⊢λ z∉ (Ax ⊢m ·  Ax ⊢s · (Ax ⊢n · Ax ⊢s · Ax ⊢z))))))
  where
  ⊢m = S S S Z
  ⊢n = S S Z
  ⊢s = S Z
  ⊢z = Z
  Γ₀ = ε
  Γ₁ = Γ₀ , "m" `: Ch
  Γ₂ = Γ₁ , "n" `: Ch
  Γ₃ = Γ₂ , "s" `: `ℕ `→ `ℕ
  m∉ : "m" ∉ Γ₀
  m∉ ()
  n∉ : "n" ∉ Γ₁
  n∉ (S ())
  s∉ : "s" ∉ Γ₂
  s∉ (S S ())
  z∉ : "z" ∉ Γ₃
  z∉ (S S S ())

fromCh : Term
fromCh = `λ "m" `→ ` "m" · (`λ "s" `→ `suc ` "s") · `zero

⊢fromCh : ε ⊢ fromCh `: Ch `→ `ℕ
⊢fromCh = (⊢λ m∉ (Ax ⊢m · (⊢λ s∉ (⊢suc (Ax ⊢s))) · ⊢zero))
  where
  ⊢m = Z
  ⊢s = Z
  Γ₀ = ε
  Γ₁ = Γ₀ , "m" `: Ch
  m∉ : "m" ∉ Γ₀
  m∉ ()
  s∉ : "s" ∉ Γ₁
  s∉ (S ())

fourCh : Term
fourCh = fromCh · (plusCh · twoCh · twoCh)

⊢fourCh : ε ⊢ fourCh `: `ℕ
⊢fourCh = ⊢fromCh · (⊢plusCh · ⊢twoCh · ⊢twoCh)
\end{code}


## Erasure

\begin{code}
lookup : ∀ {Γ x A} → Γ ∋ x `: A → Id
lookup {Γ , x `: A} Z       =  x
lookup {Γ , x `: A} (S ⊢w)  =  lookup {Γ} ⊢w

erase : ∀ {Γ M A} → Γ ⊢ M `: A → Term
erase (Ax ⊢w)               =  ` lookup ⊢w
erase (⊢λ {x = x} x∉ ⊢N)    =  `λ x `→ erase ⊢N
erase (⊢L · ⊢M)             =  erase ⊢L · erase ⊢M
erase (⊢zero)               =  `zero
erase (⊢suc ⊢M)             =  `suc (erase ⊢M)
erase (⊢pred ⊢M)            =  `pred (erase ⊢M)
erase (⊢if0 ⊢L ⊢M ⊢N)       =  `if0 (erase ⊢L) then (erase ⊢M) else (erase ⊢N)
erase (⊢Y ⊢M)               =  `Y (erase ⊢M)
\end{code}

### Properties of erasure

\begin{code}
cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {s t u v x y} → 
                               s ≡ t → u ≡ v → x ≡ y → f s u x ≡ f t v y
cong₃ f refl refl refl = refl

lookup-lemma : ∀ {Γ x A} → (⊢x : Γ ∋ x `: A) → lookup ⊢x ≡ x
lookup-lemma Z       =  refl
lookup-lemma (S ⊢w)  =  lookup-lemma ⊢w

erase-lemma : ∀ {Γ M A} → (⊢M : Γ ⊢ M `: A) → erase ⊢M ≡ M
erase-lemma (Ax ⊢x)             =  cong `_ (lookup-lemma ⊢x)
erase-lemma (⊢λ {x = x} x∉ ⊢N)  =  cong (`λ x `→_) (erase-lemma ⊢N)
erase-lemma (⊢L · ⊢M)           =  cong₂ _·_ (erase-lemma ⊢L) (erase-lemma ⊢M)
erase-lemma (⊢zero)             =  refl
erase-lemma (⊢suc ⊢M)           =  cong `suc_ (erase-lemma ⊢M)
erase-lemma (⊢pred ⊢M)          =  cong `pred_ (erase-lemma ⊢M)
erase-lemma (⊢if0 ⊢L ⊢M ⊢N)     =  cong₃ `if0_then_else_
                                     (erase-lemma ⊢L) (erase-lemma ⊢M) (erase-lemma ⊢N)
erase-lemma (⊢Y ⊢M)             =  cong `Y_ (erase-lemma ⊢M)
\end{code}


## Substitution

### Lists as sets

\begin{code}
open Collections.CollectionDec (Id) (_≟_)
\end{code}

### Free variables

\begin{code}
free : Term → List Id
free (` x)                   =  [ x ]
free (`λ x `→ N)             =  free N \\ x
free (L · M)                 =  free L ++ free M
free (`zero)                 =  []
free (`suc M)                =  free M
free (`pred M)               =  free M
free (`if0 L then M else N)  =  free L ++ free M ++ free N
free (`Y M)                  =  free M
\end{code}

### Identifier maps

\begin{code}
∅ : Id → Term
∅ x = ` x

infixl 5 _,_↦_

_,_↦_ : (Id → Term) → Id → Term → (Id → Term)
(ρ , x ↦ M) w with w ≟ x
...               | yes _   =  M
...               | no  _   =  ρ w
\end{code}

### Substitution

\begin{code}
subst : (Id → Term) → Term → Term
subst ρ (` x)        =  ρ x
subst ρ (`λ x `→ N)  =  `λ x `→ subst (ρ , x ↦ ` x) N
subst ρ (L · M)      =  subst ρ L · subst ρ M
subst ρ (`zero)      =  `zero
subst ρ (`suc M)     =  `suc (subst ρ M)
subst ρ (`pred M)    =  `pred (subst ρ M)
subst ρ (`if0 L then M else N)
  =  `if0 (subst ρ L) then (subst ρ M) else (subst ρ N)
subst ρ (`Y M)       =  `Y (subst ρ M)  
                       
_[_:=_] : Term → Id → Term → Term
N [ x := M ]  =  subst (∅ , x ↦ M) N
\end{code}

### Testing substitution

\begin{code}
_ : (` "s" · ` "s" · ` "z") [ "z" := `zero ] ≡ (` "s" · ` "s" · `zero)
_ = refl

_ : (` "s" · ` "s" · ` "z") [ "s" := (`λ "m" `→ `suc ` "m") ] [ "z" := `zero ] 
      ≡ (`λ "m" `→ `suc ` "m") · (`λ "m" `→ `suc ` "m") · `zero
_ = refl

_ : (`λ "m" `→ ` "m" ·  ` "n") [ "n" := ` "p" · ` "q" ]
      ≡ `λ "m" `→ ` "m" · (` "p" · ` "q")
_ = refl

_ : subst (∅ , "m" ↦ ` "p" , "n" ↦ ` "q") (` "m" · ` "n")  ≡ (` "p" · ` "q")
_ = refl
\end{code}


## Values

\begin{code}
data Value : Term → Set where

  Zero :
      ----------
      Value `zero

  Suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)
      
  Fun : ∀ {x N}
      ---------------
    → Value (`λ x `→ N)
\end{code}

## Reduction

\begin{code}
infix 4 _⟶_

data _⟶_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L ⟶ L′
      -----------------
    → L · M ⟶ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M ⟶ M′
      -----------------
    → V · M ⟶ V · M′

  β-`→ : ∀ {x N V}
    → Value V
      ---------------------------------
    → (`λ x `→ N) · V ⟶ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M ⟶ M′
      -------------------
    → `suc M ⟶ `suc M′

  ξ-pred : ∀ {M M′}
    → M ⟶ M′
      ---------------------
    → `pred M ⟶ `pred M′

  β-pred-zero :
      ----------------------
      `pred `zero ⟶ `zero

  β-pred-suc : ∀ {V}
    → Value V
      ---------------------
    → `pred (`suc V) ⟶ V

  ξ-if0 : ∀ {L L′ M N}
    → L ⟶ L′
      -----------------------------------------------
    → `if0 L then M else N ⟶ `if0 L′ then M else N

  β-if0-zero : ∀ {M N}
      -------------------------------
    → `if0 `zero then M else N ⟶ M
  
  β-if0-suc : ∀ {V M N}
    → Value V
      ----------------------------------
    → `if0 (`suc V) then M else N ⟶ N

  ξ-Y : ∀ {M M′}
    → M ⟶ M′
      ---------------
    → `Y M ⟶ `Y M′

  β-Y : ∀ {V x N}
    → Value V
    → V ≡ `λ x `→ N
      -------------------------
    → `Y V ⟶ N [ x := `Y V ]
\end{code}

## Reflexive and transitive closure

\begin{code}
infix  2 _⟶*_
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3 _∎

data _⟶*_ : Term → Term → Set where

  _∎ : ∀ (M : Term)
      -------------
    → M ⟶* M

  _⟶⟨_⟩_ : ∀ (L : Term) {M N}
    → L ⟶ M
    → M ⟶* N
      ---------
    → L ⟶* N

begin_ : ∀ {M N} → (M ⟶* N) → (M ⟶* N)
begin M⟶*N = M⟶*N
\end{code}

## Canonical forms

\begin{code}
data Canonical : Term → Type → Set where

  Zero : 
      -------------------
      Canonical `zero `ℕ

  Suc : ∀ {V}
    → Canonical V `ℕ
      ----------------------
    → Canonical (`suc V) `ℕ
 
  Fun : ∀ {x N A B}
    → ε , x `: A ⊢ N `: B
      -------------------------------
    → Canonical (`λ x `→ N) (A `→ B)
\end{code}

## Canonical forms lemma

Every typed value is canonical.

\begin{code}
canonical : ∀ {V A}
  → ε ⊢ V `: A
  → Value V
    -------------
  → Canonical V A
canonical ⊢zero      Zero      =  Zero
canonical (⊢suc ⊢V)  (Suc VV)  =  Suc (canonical ⊢V VV)
canonical (⊢λ x∉ ⊢N) Fun       =  Fun ⊢N
\end{code}

Every canonical form has a type and a value.

\begin{code}
type : ∀ {V A}
  → Canonical V A
    --------------
  → ε ⊢ V `: A
type Zero              =  ⊢zero
type (Suc CV)          =  ⊢suc (type CV)
type (Fun {x = x} ⊢N)  =  ⊢λ x∉ ⊢N
  where
  x∉ : x ∉ ε
  x∉ ()

value : ∀ {V A}
  → Canonical V A
    -------------
  → Value V
value Zero         =  Zero
value (Suc CV)     =  Suc (value CV)
value (Fun ⊢N)     =  Fun
\end{code}
    
## Progress

\begin{code}
data Progress (M : Term) (A : Type) : Set where
  step : ∀ {N}
    → M ⟶ N
      ----------
    → Progress M A
  done :
      Canonical M A
      -------------
    → Progress M A

progress : ∀ {M A} → ε ⊢ M `: A → Progress M A
progress (Ax ())
progress (⊢λ x∉ ⊢N)                        =  done (Fun ⊢N)
progress (⊢L · ⊢M) with progress ⊢L
...    | step L⟶L′                       =  step (ξ-·₁ L⟶L′)
...    | done (Fun _) with progress ⊢M
...            | step M⟶M′               =  step (ξ-·₂ Fun M⟶M′)
...            | done CM                   =  step (β-`→ (value CM))
progress ⊢zero                             =  done Zero
progress (⊢suc ⊢M) with progress ⊢M
...    | step M⟶M′                       =  step (ξ-suc M⟶M′)
...    | done CM                           =  done (Suc CM)
progress (⊢pred ⊢M) with progress ⊢M
...    | step M⟶M′                       =  step (ξ-pred M⟶M′)
...    | done Zero                         =  step β-pred-zero
...    | done (Suc CM)                     =  step (β-pred-suc (value CM))
progress (⊢if0 ⊢L ⊢M ⊢N) with progress ⊢L
...    | step L⟶L′                       =  step (ξ-if0 L⟶L′)
...    | done Zero                         =  step β-if0-zero
...    | done (Suc CM)                     =  step (β-if0-suc (value CM))
progress (⊢Y ⊢M) with progress ⊢M
...    | step M⟶M′                       =  step (ξ-Y M⟶M′)
...    | done (Fun _)                      =  step (β-Y Fun refl)
\end{code}


## Preservation

### Domain of an environment

\begin{code}
{-
dom : Env → List Id
dom ε            =  []
dom (Γ , x `: A)  =  x ∷ dom Γ

dom-lemma : ∀ {Γ y B} → Γ ∋ y `: B → y ∈ dom Γ
dom-lemma Z           =  here
dom-lemma (S x≢y ⊢y)  =  there (dom-lemma ⊢y)

free-lemma : ∀ {Γ M A} → Γ ⊢ M `: A → free M ⊆ dom Γ
free-lemma (Ax ⊢x) w∈ with w∈
...                      | here         =  dom-lemma ⊢x
...                      | there ()   
free-lemma {Γ} (⊢λ {N = N} ⊢N)          =  ∷-to-\\ (free-lemma ⊢N)
free-lemma (⊢L · ⊢M) w∈ with ++-to-⊎ w∈
...                        | inj₁ ∈L    = free-lemma ⊢L ∈L
...                        | inj₂ ∈M    = free-lemma ⊢M ∈M
free-lemma ⊢zero ()
free-lemma (⊢suc ⊢M) w∈                 = free-lemma ⊢M w∈
free-lemma (⊢pred ⊢M) w∈                = free-lemma ⊢M w∈
free-lemma (⊢if0 ⊢L ⊢M ⊢N) w∈
        with ++-to-⊎ w∈
...         | inj₁ ∈L                   = free-lemma ⊢L ∈L
...         | inj₂ ∈MN with ++-to-⊎ ∈MN
...                       | inj₁ ∈M     = free-lemma ⊢M ∈M
...                       | inj₂ ∈N     = free-lemma ⊢N ∈N
free-lemma (⊢Y ⊢M) w∈                   = free-lemma ⊢M w∈       
-}
\end{code}

### Renaming

Let's try an example.  The result I want to prove is:

    ⊢subst : ∀ {Γ Δ ρ}
      → (∀ {x A} →  Γ ∋ x `: A  →  Δ ⊢ ρ x `: A)
        -----------------------------------------------
      → (∀ {M A} →  Γ ⊢ M `: A  →  Δ ⊢ subst ρ M `: A)

For this to work, I need to know that neither `Δ` or any of the
bound variables in `ρ x` will collide with any bound variable in `M`.
How can I establish this?

In particular, I need to check that the conditions for ordinary
substitution are sufficient to establish the required invariants.
In that case we have:

    ⊢substitution : ∀ {Γ x A N B M} →
      Γ , x `: A ⊢ N `: B →
      Γ ⊢ M `: A →
      --------------------
      Γ ⊢ N [ x := M ] `: B

Here, since `N` is well-typed, none of it's bound variables collide
with `Γ`, and hence cannot collide with any free variable of `M`.
*But* we can't make a similar guarantee for the *bound* variables
of `M`, so substitution may break the invariants. Here are examples:

      (`λ "x" `→ `λ "y" `→ ` "x") (`λ "y" `→ ` "y")
    ⟶
      (`λ "y" → (`λ "y" `→ ` "y"))

      ε , "z" `: `ℕ ⊢ (`λ "x" `→ `λ "y" → ` "x" · ` "y" · ` "z") (`λ "y" `→ ` "y" · ` "z")
    ⟶
      ε , "z" `: `ℕ ⊢ (`λ "y" → (`λ "y" `→ ` "y" · ` "z") · ` "y" · ` "z")

This doesn't maintain the invariant, but doesn't break either.
But I don't know how to prove it never breaks. Maybe I can come
up with an example that does break after a few steps.  Or, maybe
I don't need the nested variables to be unique. Maybe all I need
is for the free variables in each `ρ x` to be distinct from any
of the bound variables in `N`. But this requires every bound
variable in `N` to not appear in `Γ`. Not clear how to maintain
such a condition without the invariant, so I don't know how
the proof works. Bugger!

Consider a term with free variables, where every bound
variable of the term is distinct from any free variable.
(This is trivially true for a closed term.) Question: if
I never reduce under lambda, do I ever need
to perform renaming?

It's easy to come up with a counter-example if I allow
reduction under lambda.

    (λ y → (λ x → λ y → x y) y) ⟶ (λ y → (λ y′ → y y′))

The above requires renaming. But if I remove the outer lambda

    (λ x → λ y → x y) y ⟶ (λ y → (λ y′ → y y′))

then the term on the left violates the condition on free
variables, and any term I can think of that causes problems
also violates the condition. So I may be able to do something
here.


\begin{code}
{-
⊢rename : ∀ {Γ Δ xs}
  → (∀ {x A} → Γ ∋ x `: A  →  Δ ∋ x `: A)
    --------------------------------------------------
  → (∀ {M A} → Γ ⊢ M `: A  →  Δ ⊢ M `: A)
⊢rename ⊢σ (Ax ⊢x)     =  Ax (⊢σ ⊢x)
⊢rename {Γ} {Δ} ⊢σ (⊢λ {x = x} {N = N} {A = A} x∉Γ ⊢N)
                           =  ⊢λ x∉Δ (⊢rename {Γ′} {Δ′} ⊢σ′ ⊢N)
  where
  Γ′   =  Γ , x `: A
  Δ′   =  Δ , x `: A
  xs′  =  x ∷ xs

  ⊢σ′ : ∀ {w B} → w ∈ xs′ → Γ′ ∋ w `: B → Δ′ ∋ w `: B
  ⊢σ′ w∈′ Z          =  Z
  ⊢σ′ w∈′ (S w≢ ⊢w)  =  S w≢ (⊢σ ∈w ⊢w)
    where
    ∈w  =  there⁻¹ w∈′ w≢

  ⊆xs′ : free N ⊆ xs′
  ⊆xs′ = \\-to-∷ ⊆xs
⊢rename ⊢σ ⊆xs (⊢L · ⊢M)   =  ⊢rename ⊢σ L⊆ ⊢L · ⊢rename ⊢σ M⊆ ⊢M
  where
  L⊆ = trans-⊆ ⊆-++₁ ⊆xs
  M⊆ = trans-⊆ ⊆-++₂ ⊆xs
⊢rename ⊢σ ⊆xs (⊢zero)     =  ⊢zero
⊢rename ⊢σ ⊆xs (⊢suc ⊢M)   =  ⊢suc (⊢rename ⊢σ ⊆xs ⊢M)
⊢rename ⊢σ ⊆xs (⊢pred ⊢M)  =  ⊢pred (⊢rename ⊢σ ⊆xs ⊢M)
⊢rename ⊢σ ⊆xs (⊢if0 {L = L} ⊢L ⊢M ⊢N)
  = ⊢if0 (⊢rename ⊢σ L⊆ ⊢L) (⊢rename ⊢σ M⊆ ⊢M) (⊢rename ⊢σ N⊆ ⊢N)
    where
    L⊆ = trans-⊆ ⊆-++₁ ⊆xs
    M⊆ = trans-⊆ ⊆-++₁ (trans-⊆ (⊆-++₂ {free L}) ⊆xs)
    N⊆ = trans-⊆ ⊆-++₂ (trans-⊆ (⊆-++₂ {free L}) ⊆xs)
⊢rename ⊢σ ⊆xs (⊢Y ⊢M)     =  ⊢Y (⊢rename ⊢σ ⊆xs ⊢M)
-}
\end{code}


### Substitution preserves types

\begin{code}
{-
⊢subst : ∀ {Γ Δ xs ys ρ}
  → (∀ {x}   → x ∈ xs      →  free (ρ x) ⊆ ys)
  → (∀ {x A} → x ∈ xs      →  Γ ∋ x `: A  →  Δ ⊢ ρ x `: A)
    -------------------------------------------------------------
  → (∀ {M A} → free M ⊆ xs →  Γ ⊢ M `: A  →  Δ ⊢ subst ys ρ M `: A)
⊢subst Σ ⊢ρ ⊆xs (Ax ⊢x)
    =  ⊢ρ (⊆xs here) ⊢x
⊢subst {Γ} {Δ} {xs} {ys} {ρ} Σ ⊢ρ ⊆xs (⊢λ {x = x} {N = N} {A = A} ⊢N)
    = ⊢λ {x = y} {A = A} (⊢subst {Γ′} {Δ′} {xs′} {ys′} {ρ′} Σ′ ⊢ρ′ ⊆xs′ ⊢N)
  where
  y   =  fresh ys
  Γ′  =  Γ , x `: A
  Δ′  =  Δ , y `: A
  xs′ =  x ∷ xs
  ys′ =  y ∷ ys
  ρ′  =  ρ , x ↦ ` y

  Σ′ : ∀ {w} → w ∈ xs′ →  free (ρ′ w) ⊆ ys′
  Σ′ {w} w∈′ with w ≟ x
  ...            | yes refl    =  ⊆-++₁
  ...            | no  w≢      =  ⊆-++₂ ∘ Σ (there⁻¹ w∈′ w≢)
  
  ⊆xs′ :  free N ⊆ xs′
  ⊆xs′ =  \\-to-∷ ⊆xs

  ⊢σ : ∀ {w C} → w ∈ ys → Δ ∋ w `: C → Δ′ ∋ w `: C
  ⊢σ w∈ ⊢w  =  S (fresh-lemma w∈) ⊢w

  ⊢ρ′ : ∀ {w C} → w ∈ xs′ → Γ′ ∋ w `: C → Δ′ ⊢ ρ′ w `: C
  ⊢ρ′ {w} _ Z with w ≟ x
  ...         | yes _             =  Ax Z
  ...         | no  w≢            =  ⊥-elim (w≢ refl)
  ⊢ρ′ {w} w∈′ (S w≢ ⊢w) with w ≟ x
  ...         | yes refl          =  ⊥-elim (w≢ refl)
  ...         | no  _             =  ⊢rename {Δ} {Δ′} {ys} ⊢σ (Σ w∈) (⊢ρ w∈ ⊢w)
              where
              w∈  =  there⁻¹ w∈′ w≢

⊢subst Σ ⊢ρ ⊆xs (⊢L · ⊢M)
    =  ⊢subst Σ ⊢ρ L⊆ ⊢L · ⊢subst Σ ⊢ρ M⊆ ⊢M
  where
  L⊆ = trans-⊆ ⊆-++₁ ⊆xs
  M⊆ = trans-⊆ ⊆-++₂ ⊆xs
⊢subst Σ ⊢ρ ⊆xs ⊢zero            =  ⊢zero
⊢subst Σ ⊢ρ ⊆xs (⊢suc ⊢M)        =  ⊢suc (⊢subst Σ ⊢ρ ⊆xs ⊢M)
⊢subst Σ ⊢ρ ⊆xs (⊢pred ⊢M)       =  ⊢pred (⊢subst Σ ⊢ρ ⊆xs ⊢M)
⊢subst Σ ⊢ρ ⊆xs (⊢if0 {L = L} ⊢L ⊢M ⊢N)
    =  ⊢if0 (⊢subst Σ ⊢ρ L⊆ ⊢L) (⊢subst Σ ⊢ρ M⊆ ⊢M) (⊢subst Σ ⊢ρ N⊆ ⊢N)
    where
    L⊆ = trans-⊆ ⊆-++₁ ⊆xs
    M⊆ = trans-⊆ ⊆-++₁ (trans-⊆ (⊆-++₂ {free L}) ⊆xs)
    N⊆ = trans-⊆ ⊆-++₂ (trans-⊆ (⊆-++₂ {free L}) ⊆xs)
⊢subst Σ ⊢ρ ⊆xs (⊢Y ⊢M)          =  ⊢Y (⊢subst Σ ⊢ρ ⊆xs ⊢M)    

⊢substitution : ∀ {Γ x A N B M} →
  Γ , x `: A ⊢ N `: B →
  Γ ⊢ M `: A →
  --------------------
  Γ ⊢ N [ x := M ] `: B
⊢substitution {Γ} {x} {A} {N} {B} {M} ⊢N ⊢M =
  ⊢subst {Γ′} {Γ} {xs} {ys} {ρ} Σ ⊢ρ {N} {B} ⊆xs ⊢N
  where
  Γ′     =  Γ , x `: A
  xs     =  free N
  ys     =  free M ++ (free N \\ x)
  ρ      =  ∅ , x ↦ M

  Σ : ∀ {w} → w ∈ xs → free (ρ w) ⊆ ys
  Σ {w} w∈ y∈ with w ≟ x
  ...            | yes _                   =  ⊆-++₁ y∈
  ...            | no w≢ rewrite ∈-[_] y∈  =  ⊆-++₂ (∈-≢-to-\\ w∈ w≢)
  
  ⊢ρ : ∀ {w B} → w ∈ xs → Γ′ ∋ w `: B → Γ ⊢ ρ w `: B
  ⊢ρ {w} w∈ Z         with w ≟ x
  ...                    | yes _     =  ⊢M
  ...                    | no  w≢    =  ⊥-elim (w≢ refl)
  ⊢ρ {w} w∈ (S w≢ ⊢w) with w ≟ x
  ...                    | yes refl  =  ⊥-elim (w≢ refl)
  ...                    | no  _     =  Ax ⊢w

  ⊆xs : free N ⊆ xs
  ⊆xs x∈ = x∈
-}
\end{code}

### Preservation

\begin{code}
{-
preservation : ∀ {Γ M N A}
  →  Γ ⊢ M `: A
  →  M ⟶ N
     ---------
  →  Γ ⊢ N `: A
preservation (Ax ⊢x) ()
preservation (⊢λ ⊢N) ()
preservation (⊢L · ⊢M)              (ξ-·₁ L⟶)    =  preservation ⊢L L⟶ · ⊢M
preservation (⊢V · ⊢M)              (ξ-·₂ _ M⟶)  =  ⊢V · preservation ⊢M M⟶
preservation ((⊢λ ⊢N) · ⊢W)         (β-`→ _)       =  ⊢substitution ⊢N ⊢W
preservation (⊢zero)                ()
preservation (⊢suc ⊢M)              (ξ-suc M⟶)   =  ⊢suc (preservation ⊢M M⟶)
preservation (⊢pred ⊢M)             (ξ-pred M⟶)  =  ⊢pred (preservation ⊢M M⟶)
preservation (⊢pred ⊢zero)          (β-pred-zero)  =  ⊢zero
preservation (⊢pred (⊢suc ⊢M))      (β-pred-suc _) =  ⊢M
preservation (⊢if0 ⊢L ⊢M ⊢N)        (ξ-if0 L⟶)   =  ⊢if0 (preservation ⊢L L⟶) ⊢M ⊢N
preservation (⊢if0 ⊢zero ⊢M ⊢N)     β-if0-zero     =  ⊢M
preservation (⊢if0 (⊢suc ⊢V) ⊢M ⊢N) (β-if0-suc _)  =  ⊢N
preservation (⊢Y ⊢M)                (ξ-Y M⟶)     =  ⊢Y (preservation ⊢M M⟶)
preservation (⊢Y (⊢λ ⊢N))           (β-Y _ refl)   =  ⊢substitution ⊢N (⊢Y (⊢λ ⊢N))
-}
\end{code}

## Normalise

\begin{code}
{-
data Normalise {M A} (⊢M : ε ⊢ M `: A) : Set where
  out-of-gas : ∀ {N} → M ⟶* N → ε ⊢ N `: A → Normalise ⊢M
  normal     : ∀ {V} → ℕ → Canonical V A → M ⟶* V → Normalise ⊢M

normalise : ∀ {L A} → ℕ → (⊢L : ε ⊢ L `: A) → Normalise ⊢L
normalise {L} zero    ⊢L                   =  out-of-gas (L ∎) ⊢L
normalise {L} (suc m) ⊢L with progress ⊢L
...  | done CL                             =  normal (suc m) CL (L ∎)
...  | step L⟶M with preservation ⊢L L⟶M
...      | ⊢M with normalise m ⊢M
...          | out-of-gas M⟶*N ⊢N        =  out-of-gas (L ⟶⟨ L⟶M ⟩ M⟶*N) ⊢N
...          | normal n CV M⟶*V          =  normal n CV (L ⟶⟨ L⟶M ⟩ M⟶*V)
-}
\end{code}

