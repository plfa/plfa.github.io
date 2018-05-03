---
title     : "Typed: Raw terms with types (broken)"
layout    : page
permalink : /Typed
---

This version uses raw terms. Substitution presumes that no
generation of fresh names is required.

The substitution algorithm is based on one by McBride.
It is given a map from names to terms. Say the mapping of a
name is trivial if it takes a name to a term consisting of
just the variable with that name. No fresh names are required
if the mapping on each variable is either trivial or to a
closed term. However, the proof of correctness currently
contains a hole, and may be difficult to repair.

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
infix   4  _∋_`:_
infix   4  _⊢_`:_
infixl  5  _,_`:_
infixr  6  _`→_
infix   6  `λ_`→_
infixl  7  `if0_then_else_
infix   8  `suc_ `pred_ `Y_
infixl  9  _·_

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

  S : ∀ {Γ A B x w}
    → w ≢ x
    → Γ ∋ w `: B
      --------------------
    → Γ , x `: A ∋ w `: B

data _⊢_`:_ : Env → Term → Type → Set where

  Ax : ∀ {Γ A x}
    → Γ ∋ x `: A
      --------------
    → Γ ⊢ ` x `: A

  ⊢λ : ∀ {Γ x N A B}
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
\end{code}

## Test examples

\begin{code}
s≢z : "s" ≢ "z"
s≢z ()

n≢z : "n" ≢ "z"
n≢z ()

n≢s : "n" ≢ "s"
n≢s ()

m≢z : "m" ≢ "z"
m≢z ()

m≢s : "m" ≢ "s"
m≢s ()

m≢n : "m" ≢ "n"
m≢n ()

p≢n : "p" ≢ "n"
p≢n ()

p≢m : "p" ≢ "m"
p≢m ()

two : Term
two = `suc `suc `zero

⊢two : ε ⊢ two `: `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

plus : Term
plus = `Y (`λ "p" `→ `λ "m" `→ `λ "n" `→
            `if0 ` "m" then ` "n" else `suc (` "p" · (`pred (` "m")) · ` "n"))

⊢plus : ε ⊢ plus `: `ℕ `→ `ℕ `→ `ℕ
⊢plus = (⊢Y (⊢λ (⊢λ (⊢λ (⊢if0 (Ax ⊢m) (Ax ⊢n) (⊢suc (Ax ⊢p · (⊢pred (Ax ⊢m)) · Ax ⊢n)))))))
  where
  ⊢p = S p≢n (S p≢m Z)
  ⊢m = S m≢n Z
  ⊢n = Z

four : Term
four = plus · two · two

⊢four : ε ⊢ four `: `ℕ
⊢four = ⊢plus · ⊢two · ⊢two

Ch : Type
Ch = (`ℕ `→ `ℕ) `→ `ℕ `→ `ℕ

twoCh : Term
twoCh = `λ "s" `→ `λ "z" `→ (` "s" · (` "s" · ` "z"))

⊢twoCh : ε ⊢ twoCh `: Ch
⊢twoCh = (⊢λ (⊢λ (Ax ⊢s · (Ax ⊢s · Ax ⊢z))))
  where
  ⊢s = S s≢z Z
  ⊢z = Z

plusCh : Term
plusCh = `λ "m" `→ `λ "n" `→ `λ "s" `→ `λ "z" `→
           ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

⊢plusCh : ε ⊢ plusCh `: Ch `→ Ch `→ Ch
⊢plusCh = (⊢λ (⊢λ (⊢λ (⊢λ (Ax ⊢m ·  Ax ⊢s · (Ax ⊢n · Ax ⊢s · Ax ⊢z))))))
  where
  ⊢m = S m≢z (S m≢s (S m≢n Z))
  ⊢n = S n≢z (S n≢s Z)
  ⊢s = S s≢z Z
  ⊢z = Z

fromCh : Term
fromCh = `λ "m" `→ ` "m" · (`λ "s" `→ `suc ` "s") · `zero

⊢fromCh : ε ⊢ fromCh `: Ch `→ `ℕ
⊢fromCh = (⊢λ (Ax ⊢m · (⊢λ (⊢suc (Ax ⊢s))) · ⊢zero))
  where
  ⊢m = Z
  ⊢s = Z

fourCh : Term
fourCh = fromCh · (plusCh · twoCh · twoCh)

⊢fourCh : ε ⊢ fourCh `: `ℕ
⊢fourCh = ⊢fromCh · (⊢plusCh · ⊢twoCh · ⊢twoCh)
\end{code}


## Erasure

\begin{code}
lookup : ∀ {Γ x A} → Γ ∋ x `: A → Id
lookup {Γ , x `: A} Z          =  x
lookup {Γ , x `: A} (S w≢ ⊢w)  =  lookup {Γ} ⊢w

erase : ∀ {Γ M A} → Γ ⊢ M `: A → Term
erase (Ax ⊢w)           =  ` lookup ⊢w
erase (⊢λ {x = x} ⊢N)   =  `λ x `→ erase ⊢N
erase (⊢L · ⊢M)         =  erase ⊢L · erase ⊢M
erase (⊢zero)           =  `zero
erase (⊢suc ⊢M)         =  `suc (erase ⊢M)
erase (⊢pred ⊢M)        =  `pred (erase ⊢M)
erase (⊢if0 ⊢L ⊢M ⊢N)   =  `if0 (erase ⊢L) then (erase ⊢M) else (erase ⊢N)
erase (⊢Y ⊢M)           =  `Y (erase ⊢M)
\end{code}

### Properties of erasure

\begin{code}
cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {s t u v x y} → 
                               s ≡ t → u ≡ v → x ≡ y → f s u x ≡ f t v y
cong₃ f refl refl refl = refl

lookup-lemma : ∀ {Γ x A} → (⊢x : Γ ∋ x `: A) → lookup ⊢x ≡ x
lookup-lemma Z          =  refl
lookup-lemma (S w≢ ⊢w)  =  lookup-lemma ⊢w

erase-lemma : ∀ {Γ M A} → (⊢M : Γ ⊢ M `: A) → erase ⊢M ≡ M
erase-lemma (Ax ⊢x)          =  cong `_ (lookup-lemma ⊢x)
erase-lemma (⊢λ {x = x} ⊢N)  =  cong (`λ x `→_) (erase-lemma ⊢N)
erase-lemma (⊢L · ⊢M)        =  cong₂ _·_ (erase-lemma ⊢L) (erase-lemma ⊢M)
erase-lemma (⊢zero)          =  refl
erase-lemma (⊢suc ⊢M)        =  cong `suc_ (erase-lemma ⊢M)
erase-lemma (⊢pred ⊢M)       =  cong `pred_ (erase-lemma ⊢M)
erase-lemma (⊢if0 ⊢L ⊢M ⊢N)  =  cong₃ `if0_then_else_
                                  (erase-lemma ⊢L) (erase-lemma ⊢M) (erase-lemma ⊢N)
erase-lemma (⊢Y ⊢M)          =  cong `Y_ (erase-lemma ⊢M)
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

_ : subst (∅ , "m" ↦ two , "n" ↦ four) (` "m" · ` "n")  ≡ (two · four)
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

  β-→ : ∀ {x N V}
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

  β-Y : ∀ {F x N}
    → F ≡ `λ x `→ N
      -------------------------
    → `Y F ⟶ N [ x := `Y F ]
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

## Sample execution

\begin{code}
_ : plus · two · two ⟶* (`suc (`suc (`suc (`suc `zero))))
_ = 
  begin
    plus · two · two
  ⟶⟨ ξ-·₁ (ξ-·₁ (β-Y refl)) ⟩
    (`λ "m" `→ (`λ "n" `→ `if0 ` "m" then ` "n" else
      `suc (plus · (`pred (` "m")) · (` "n"))))  · two · two
  ⟶⟨ ξ-·₁ (β-→ (Suc (Suc Zero))) ⟩
    (`λ "n" `→ `if0 two then ` "n" else
      `suc (plus · (`pred two) · (` "n"))) · two
  ⟶⟨ β-→ (Suc (Suc Zero)) ⟩
   `if0 two then two else
     `suc (plus · (`pred two) · two)
  ⟶⟨ β-if0-suc (Suc Zero) ⟩
   `suc (plus · (`pred two) · two)
  ⟶⟨ ξ-suc (ξ-·₁ (ξ-·₁ (β-Y refl))) ⟩
   `suc ((`λ "m" `→ (`λ "n" `→ `if0 ` "m" then ` "n" else
     `suc (plus · (`pred (` "m")) · (` "n")))) · (`pred two) · two)
  ⟶⟨ ξ-suc (ξ-·₁ (ξ-·₂ Fun (β-pred-suc (Suc Zero)))) ⟩
   `suc ((`λ "m" `→ (`λ "n" `→ `if0 ` "m" then ` "n" else
     `suc (plus · (`pred (` "m")) · (` "n")))) · (`suc `zero) · two)
  ⟶⟨ ξ-suc (ξ-·₁ (β-→ (Suc Zero))) ⟩
   `suc ((`λ "n" `→ `if0 `suc `zero then ` "n" else
     `suc (plus · (`pred (`suc `zero)) · (` "n")))) · two
  ⟶⟨ ξ-suc (β-→ (Suc (Suc Zero))) ⟩
   `suc (`if0 `suc `zero then two else
     `suc (plus · (`pred (`suc `zero)) · two))
  ⟶⟨ ξ-suc (β-if0-suc Zero) ⟩
   `suc (`suc (plus · (`pred (`suc `zero)) · two))
  ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ (β-Y refl)))) ⟩
   `suc (`suc ((`λ "m" `→ (`λ "n" `→ `if0 ` "m" then ` "n" else 
     `suc (plus · (`pred (` "m")) · (` "n")))) · (`pred (`suc `zero)) · two))
  ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₂ Fun (β-pred-suc Zero)))) ⟩
   `suc (`suc ((`λ "m" `→ (`λ "n" `→ `if0 ` "m" then ` "n" else
     `suc (plus · (`pred (` "m")) · (` "n")))) · `zero · two))
  ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (β-→ Zero))) ⟩
   `suc (`suc ((`λ "n" `→ `if0 `zero then ` "n" else
     `suc (plus · (`pred `zero) · (` "n"))) · two))
  ⟶⟨ ξ-suc (ξ-suc (β-→ (Suc (Suc Zero)))) ⟩
   `suc (`suc (`if0 `zero then two else
     `suc (plus · (`pred `zero) · two)))
  ⟶⟨ ξ-suc (ξ-suc β-if0-zero) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎
\end{code}

## Values do not reduce

Values do not reduce.
\begin{code}
Val-⟶ : ∀ {M N} → Value M → ¬ (M ⟶ N)
Val-⟶ Fun ()
Val-⟶ Zero ()
Val-⟶ (Suc VM) (ξ-suc M⟶N)  =  Val-⟶ VM M⟶N
\end{code}

As a corollary, terms that reduce are not values.
\begin{code}
⟶-Val : ∀ {M N} → (M ⟶ N) → ¬ Value M
⟶-Val M⟶N VM  =  Val-⟶ VM M⟶N
\end{code}

## Reduction is deterministic

\begin{code}
det : ∀ {M M′ M″}
  → (M ⟶ M′)
  → (M ⟶ M″)
    ----------
  → M′ ≡ M″
det (ξ-·₁ L⟶L′) (ξ-·₁ L⟶L″) =  cong₂ _·_ (det L⟶L′ L⟶L″) refl
det (ξ-·₁ L⟶L′) (ξ-·₂ VL _) = ⊥-elim (Val-⟶ VL L⟶L′)
det (ξ-·₁ L⟶L′) (β-→ _) = ⊥-elim (Val-⟶ Fun L⟶L′)
det (ξ-·₂ VL _) (ξ-·₁ L⟶L″) = ⊥-elim (Val-⟶ VL L⟶L″)
det (ξ-·₂ _ M⟶M′) (ξ-·₂ _ M⟶M″) = cong₂ _·_ refl (det M⟶M′ M⟶M″)
det (ξ-·₂ _ M⟶M′) (β-→ VM) = ⊥-elim (Val-⟶ VM M⟶M′)
det (β-→ VM) (ξ-·₁ L⟶L″) = ⊥-elim (Val-⟶ Fun L⟶L″)
det (β-→ VM) (ξ-·₂ _ M⟶M″) = ⊥-elim (Val-⟶ VM M⟶M″)
det (β-→ _) (β-→ _) = refl
det (ξ-suc M⟶M′) (ξ-suc M⟶M″) = cong `suc_ (det M⟶M′ M⟶M″)
det (ξ-pred M⟶M′) (ξ-pred M⟶M″) = cong `pred_ (det M⟶M′ M⟶M″)
det (ξ-pred M⟶M′) β-pred-zero = ⊥-elim (Val-⟶ Zero M⟶M′)
det (ξ-pred M⟶M′) (β-pred-suc VM) = ⊥-elim (Val-⟶ (Suc VM) M⟶M′)
det β-pred-zero (ξ-pred M⟶M′) = ⊥-elim (Val-⟶ Zero M⟶M′)
det β-pred-zero β-pred-zero = refl
det (β-pred-suc VM) (ξ-pred M⟶M′) = ⊥-elim (Val-⟶ (Suc VM) M⟶M′)
det (β-pred-suc _) (β-pred-suc _) = refl
det (ξ-if0 L⟶L′) (ξ-if0 L⟶L″) = cong₃ `if0_then_else_ (det L⟶L′ L⟶L″) refl refl
det (ξ-if0 L⟶L′) β-if0-zero = ⊥-elim (Val-⟶ Zero L⟶L′)
det (ξ-if0 L⟶L′) (β-if0-suc VL) = ⊥-elim (Val-⟶ (Suc VL) L⟶L′)
det β-if0-zero (ξ-if0 L⟶L″) = ⊥-elim (Val-⟶ Zero L⟶L″)
det β-if0-zero β-if0-zero = refl
det (β-if0-suc VL) (ξ-if0 L⟶L″) = ⊥-elim (Val-⟶ (Suc VL) L⟶L″)
det (β-if0-suc _) (β-if0-suc _) = refl
det (ξ-Y M⟶M′) (ξ-Y M⟶M″) = cong `Y_ (det M⟶M′ M⟶M″)
det (ξ-Y M⟶M′) (β-Y refl) = ⊥-elim (Val-⟶ Fun M⟶M′)
det (β-Y refl) (ξ-Y M⟶M″) = ⊥-elim (Val-⟶ Fun M⟶M″)
det (β-Y refl) (β-Y refl) = refl
\end{code}

Almost half the lines in the above proof are redundant, for example

    det (ξ-·₁ L⟶L′) (ξ-·₂ VL _) = ⊥-elim (Val-⟶ VL L⟶L′)
    det (ξ-·₂ VL _) (ξ-·₁ L⟶L″) = ⊥-elim (Val-⟶ VL L⟶L″)
 
are essentially identical. What we might like to do is delete the
redundant lines and add

    det M⟶M′ M⟶M″ = sym (det M⟶M″ M⟶M′)

to the bottom of the proof. But this does not work. The termination
checker complains, because the arguments have merely switched order
and neither is smaller.

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
canonical (⊢λ ⊢N)    Fun       =  Fun ⊢N
\end{code}

Every canonical form has a type and a value.

\begin{code}
type : ∀ {V A}
  → Canonical V A
    --------------
  → ε ⊢ V `: A
type Zero              =  ⊢zero
type (Suc CV)          =  ⊢suc (type CV)
type (Fun {x = x} ⊢N)  =  ⊢λ ⊢N

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
progress (⊢λ ⊢N)                           =  done (Fun ⊢N)
progress (⊢L · ⊢M) with progress ⊢L
...    | step L⟶L′                       =  step (ξ-·₁ L⟶L′)
...    | done (Fun _) with progress ⊢M
...            | step M⟶M′               =  step (ξ-·₂ Fun M⟶M′)
...            | done CM                   =  step (β-→ (value CM))
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
...    | done (Fun _)                      =  step (β-Y refl)
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

\begin{code}
⊢rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x `: A  →  Δ ∋ x `: A)
    --------------------------------------------------
  → (∀ {M A} → Γ ⊢ M `: A  →  Δ ⊢ M `: A)
⊢rename ⊢σ (Ax ⊢x)          =  Ax (⊢σ ⊢x)
⊢rename {Γ} {Δ} ⊢σ (⊢λ {x = x} {N = N} {A = A} ⊢N)
                            =  ⊢λ (⊢rename {Γ′} {Δ′} ⊢σ′ ⊢N)
  where
  Γ′   =  Γ , x `: A
  Δ′   =  Δ , x `: A

  ⊢σ′ : ∀ {w B} → Γ′ ∋ w `: B → Δ′ ∋ w `: B
  ⊢σ′ Z          =  Z
  ⊢σ′ (S w≢ ⊢w)  =  S w≢ (⊢σ ⊢w)

⊢rename ⊢σ (⊢L · ⊢M)        =  ⊢rename ⊢σ ⊢L · ⊢rename ⊢σ ⊢M
⊢rename ⊢σ (⊢zero)          =  ⊢zero
⊢rename ⊢σ (⊢suc ⊢M)        =  ⊢suc (⊢rename ⊢σ ⊢M)
⊢rename ⊢σ (⊢pred ⊢M)       =  ⊢pred (⊢rename ⊢σ ⊢M)
⊢rename ⊢σ (⊢if0 ⊢L ⊢M ⊢N)
  = ⊢if0 (⊢rename ⊢σ ⊢L) (⊢rename ⊢σ ⊢M) (⊢rename ⊢σ ⊢N)
⊢rename ⊢σ (⊢Y ⊢M)          =  ⊢Y (⊢rename ⊢σ ⊢M)
\end{code}


### Substitution preserves types

\begin{code}
⊢subst : ∀ {Γ Δ ρ}
  → (∀ {x A} → Γ ∋ x `: A  →  Δ ⊢ ρ x `: A)
    -------------------------------------------------
  → (∀ {M A} → Γ ⊢ M `: A  →  Δ ⊢ subst ρ M `: A)
⊢subst ⊢ρ (Ax ⊢x)                =  ⊢ρ ⊢x
⊢subst {Γ} {Δ} {ρ} ⊢ρ (⊢λ {x = x} {N = N} {A = A} ⊢N)
    = ⊢λ {x = x} {A = A} (⊢subst {Γ′} {Δ′} {ρ′} ⊢ρ′ ⊢N)
  where
  Γ′  =  Γ , x `: A
  Δ′  =  Δ , x `: A
  ρ′  =  ρ , x ↦ ` x

  ⊢σ : ∀ {w C} → Δ ∋ w `: C → Δ′ ∋ w `: C
  ⊢σ ⊢w  =  S {!!} ⊢w

  ⊢ρ′ : ∀ {w C} → Γ′ ∋ w `: C → Δ′ ⊢ ρ′ w `: C
  ⊢ρ′ {w} Z with w ≟ x
  ...         | yes _             =  Ax Z
  ...         | no  w≢            =  ⊥-elim (w≢ refl)
  ⊢ρ′ {w} (S w≢ ⊢w) with w ≟ x
  ...         | yes refl          =  ⊥-elim (w≢ refl)
  ...         | no  _             =  ⊢rename {Δ} {Δ′} ⊢σ (⊢ρ ⊢w)

⊢subst ⊢ρ (⊢L · ⊢M)              =  ⊢subst ⊢ρ ⊢L · ⊢subst ⊢ρ ⊢M
⊢subst ⊢ρ ⊢zero                  =  ⊢zero
⊢subst ⊢ρ (⊢suc ⊢M)              =  ⊢suc (⊢subst ⊢ρ ⊢M)
⊢subst ⊢ρ (⊢pred ⊢M)             =  ⊢pred (⊢subst ⊢ρ ⊢M)
⊢subst ⊢ρ (⊢if0 ⊢L ⊢M ⊢N)
    =  ⊢if0 (⊢subst ⊢ρ ⊢L) (⊢subst ⊢ρ ⊢M) (⊢subst ⊢ρ ⊢N)
⊢subst ⊢ρ (⊢Y ⊢M)                =  ⊢Y (⊢subst ⊢ρ ⊢M)
\end{code}

Let's look at examples.  Assume `M` is closed.  Example 1.

    subst (∅ , "x" ↦ M) (`λ "y" `→ ` "x")  ≡  `λ "y" `→ M

Example 2.

      subst (∅ , "y" ↦ ` "y" , "x" ↦ M) (`λ "y" `→ ` "x" · ` "y")
    ≡
      `λ "y" `→ subst (∅ , "y" ↦ ` "y" , "x" ↦ M , "y" ↦ ` "y") (` "x" · ` "y")
    ≡
      `λ "y" `→ (M · ` "y")

The hypotheses of the theorem appear to be violated. Drat!

\begin{code}
⊢substitution : ∀ {Γ x A N B M}
  → Γ , x `: A ⊢ N `: B
  → Γ ⊢ M `: A
    ----------------------
  → Γ ⊢ N [ x := M ] `: B
⊢substitution {Γ} {x} {A} {N} {B} {M} ⊢N ⊢M =
  ⊢subst {Γ′} {Γ} {ρ} ⊢ρ {N} {B} ⊢N
  where
  Γ′     =  Γ , x `: A
  ρ      =  ∅ , x ↦ M
  ⊢ρ : ∀ {w B} → Γ′ ∋ w `: B → Γ ⊢ ρ w `: B
  ⊢ρ {w} Z         with w ≟ x
  ...                 | yes _     =  ⊢M
  ...                 | no  w≢    =  ⊥-elim (w≢ refl)
  ⊢ρ {w} (S w≢ ⊢w) with w ≟ x
  ...                 | yes refl  =  ⊥-elim (w≢ refl)
  ...                 | no  _     =  Ax ⊢w
\end{code}

### Preservation

\begin{code}
preservation : ∀ {Γ M N A}
  →  Γ ⊢ M `: A
  →  M ⟶ N
     ---------
  →  Γ ⊢ N `: A
preservation (Ax ⊢x) ()
preservation (⊢λ ⊢N) ()
preservation (⊢L · ⊢M)              (ξ-·₁ L⟶)    =  preservation ⊢L L⟶ · ⊢M
preservation (⊢V · ⊢M)              (ξ-·₂ _ M⟶)  =  ⊢V · preservation ⊢M M⟶
preservation ((⊢λ ⊢N) · ⊢W)         (β-→ _)       =  ⊢substitution ⊢N ⊢W
preservation (⊢zero)                ()
preservation (⊢suc ⊢M)              (ξ-suc M⟶)   =  ⊢suc (preservation ⊢M M⟶)
preservation (⊢pred ⊢M)             (ξ-pred M⟶)  =  ⊢pred (preservation ⊢M M⟶)
preservation (⊢pred ⊢zero)          (β-pred-zero)  =  ⊢zero
preservation (⊢pred (⊢suc ⊢M))      (β-pred-suc _) =  ⊢M
preservation (⊢if0 ⊢L ⊢M ⊢N)        (ξ-if0 L⟶)   =  ⊢if0 (preservation ⊢L L⟶) ⊢M ⊢N
preservation (⊢if0 ⊢zero ⊢M ⊢N)     β-if0-zero     =  ⊢M
preservation (⊢if0 (⊢suc ⊢V) ⊢M ⊢N) (β-if0-suc _)  =  ⊢N
preservation (⊢Y ⊢M)                (ξ-Y M⟶)     =  ⊢Y (preservation ⊢M M⟶)
preservation (⊢Y (⊢λ ⊢N))           (β-Y refl)     =  ⊢substitution ⊢N (⊢Y (⊢λ ⊢N))
\end{code}

## Normalise

\begin{code}
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
\end{code}

