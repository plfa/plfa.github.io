---
title     : "TypedFresh: Fresh variables in substitution"
layout    : page
permalink : /TypedFresh
---

This version uses raw terms. Substitution generates
a fresh name whenever substituting for a lambda term.


## Imports

\begin{code}
module TypedFresh where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; foldr; filter; concat)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _⊔_; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; 1+n≰n)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)
import Collections

pattern [_]       w        =  w ∷ []
pattern [_,_]     w x      =  w ∷ x ∷ []
pattern [_,_,_]   w x y    =  w ∷ x ∷ y ∷ []
pattern [_,_,_,_] w x y z  =  w ∷ x ∷ y ∷ z ∷ []
\end{code}


## Syntax

\begin{code}
infixr 5 _⇒_
infixl 5 _,_⦂_
infix  4 _∋_⦂_
infix  4 _⊢_⦂_
infix  5 ƛ_⇒_
infixl 6 `if0_then_else_
infix  7 `suc_ `pred_ `Y_
infixl 8 _·_

Id : Set
Id = ℕ

data Type : Set where
  `ℕ  : Type
  _⇒_ : Type → Type → Type

data Env : Set where
  ε     : Env
  _,_⦂_ : Env → Id → Type → Env

data Term : Set where
  ⌊_⌋              : Id → Term
  ƛ_⇒_            : Id → Term → Term
  _·_             : Term → Term → Term
  `zero           : Term    
  `suc_           : Term → Term
  `pred_          : Term → Term
  `if0_then_else_ : Term → Term → Term → Term
  `Y_             : Term → Term

data _∋_⦂_ : Env → Id → Type → Set where

  Z : ∀ {Γ A x}
      -----------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ A B x w}
    → w ≢ x
    → Γ ∋ w ⦂ B
      -----------------
    → Γ , x ⦂ A ∋ w ⦂ B

data _⊢_⦂_ : Env → Term → Type → Set where

  Ax : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
      ---------------------
    → Γ ⊢ ⌊ x ⌋ ⦂ A

  ⊢λ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      ------------------------
    → Γ ⊢ (ƛ x ⇒ N) ⦂ A ⇒ B

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      --------------
    → Γ ⊢ L · M ⦂ B

  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  ⊢pred : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ----------------
    → Γ ⊢ `pred M ⦂ `ℕ

  ⊢if0 : ∀ {Γ L M N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ ⊢ N ⦂ A
      ----------------------------
    → Γ ⊢ `if0 L then M else N ⦂ A

  ⊢Y : ∀ {Γ M A}
    → Γ ⊢ M ⦂ A ⇒ A
      ---------------
    → Γ ⊢ `Y M ⦂ A
\end{code}

## Test examples

\begin{code}
m n s z : Id
p = 0
m = 1
n = 2
s = 3
z = 4

s≢z : s ≢ z
s≢z ()

n≢z : n ≢ z
n≢z ()

n≢s : n ≢ s
n≢s ()

m≢z : m ≢ z
m≢z ()

m≢s : m ≢ s
m≢s ()

m≢n : m ≢ n
m≢n ()

p≢n : p ≢ n
p≢n ()

p≢m : p ≢ m
p≢m ()

two : Term
two = `suc `suc `zero

⊢two : ε ⊢ two ⦂ `ℕ
⊢two = (⊢suc (⊢suc ⊢zero))

plus : Term
plus = `Y (ƛ p ⇒ ƛ m ⇒ ƛ n ⇒ `if0 ⌊ m ⌋ then ⌊ n ⌋ else `suc (⌊ p ⌋ · (`pred ⌊ m ⌋) · ⌊ n ⌋))

⊢plus : ε ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = (⊢Y (⊢λ (⊢λ (⊢λ (⊢if0 (Ax ⊢m) (Ax ⊢n) (⊢suc (Ax ⊢p · (⊢pred (Ax ⊢m)) · Ax ⊢n)))))))
  where
  ⊢p = S p≢n (S p≢m Z)
  ⊢m = S m≢n Z
  ⊢n = Z

four : Term
four = plus · two · two

⊢four : ε ⊢ four ⦂ `ℕ
⊢four = ⊢plus · ⊢two · ⊢two

Ch : Type
Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

twoCh : Term
twoCh = ƛ s ⇒ ƛ z ⇒ (⌊ s ⌋ · (⌊ s ⌋ · ⌊ z ⌋))

⊢twoCh : ε ⊢ twoCh ⦂ Ch
⊢twoCh = (⊢λ (⊢λ (Ax ⊢s · (Ax ⊢s · Ax ⊢z))))
  where
  ⊢s = S s≢z Z
  ⊢z = Z

plusCh : Term
plusCh = ƛ m ⇒ ƛ n ⇒ ƛ s ⇒ ƛ z ⇒ ⌊ m ⌋ · ⌊ s ⌋ · (⌊ n ⌋ · ⌊ s ⌋ · ⌊ z ⌋)

⊢plusCh : ε ⊢ plusCh ⦂ Ch ⇒ Ch ⇒ Ch
⊢plusCh = (⊢λ (⊢λ (⊢λ (⊢λ (Ax ⊢m ·  Ax ⊢s · (Ax ⊢n · Ax ⊢s · Ax ⊢z))))))
  where
  ⊢m = S m≢z (S m≢s (S m≢n Z))
  ⊢n = S n≢z (S n≢s Z)
  ⊢s = S s≢z Z
  ⊢z = Z

fromCh : Term
fromCh = ƛ m ⇒ ⌊ m ⌋ · (ƛ s ⇒ `suc ⌊ s ⌋) · `zero

⊢fromCh : ε ⊢ fromCh ⦂ Ch ⇒ `ℕ
⊢fromCh = (⊢λ (Ax ⊢m · (⊢λ (⊢suc (Ax ⊢s))) · ⊢zero))
  where
  ⊢m = Z
  ⊢s = Z

fourCh : Term
fourCh = fromCh · (plusCh · twoCh · twoCh)

⊢fourCh : ε ⊢ fourCh ⦂ `ℕ
⊢fourCh = ⊢fromCh · (⊢plusCh · ⊢twoCh · ⊢twoCh)
\end{code}


## Erasure

\begin{code}
lookup : ∀ {Γ x A} → Γ ∋ x ⦂ A → Id
lookup {Γ , x ⦂ A} Z         =  x
lookup {Γ , x ⦂ A} (S _ ⊢w)  =  lookup {Γ} ⊢w

erase : ∀ {Γ M A} → Γ ⊢ M ⦂ A → Term
erase (Ax ⊢w)           =  ⌊ lookup ⊢w ⌋
erase (⊢λ {x = x} ⊢N)   =  ƛ x ⇒ erase ⊢N
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

lookup-lemma : ∀ {Γ x A} → (⊢x : Γ ∋ x ⦂ A) → lookup ⊢x ≡ x
lookup-lemma Z         =  refl
lookup-lemma (S _ ⊢w)  =  lookup-lemma ⊢w

erase-lemma : ∀ {Γ M A} → (⊢M : Γ ⊢ M ⦂ A) → erase ⊢M ≡ M
erase-lemma (Ax ⊢x)          =  cong ⌊_⌋ (lookup-lemma ⊢x)
erase-lemma (⊢λ {x = x} ⊢N)  =  cong (ƛ x ⇒_) (erase-lemma ⊢N)
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
open Collections (Id) (_≟_)
\end{code}

### Free variables

\begin{code}
free : Term → List Id
free (⌊ x ⌋)                  =  [ x ]
free (ƛ x ⇒ N)               =  free N \\ x
free (L · M)                 =  free L ++ free M
free (`zero)                 =  []
free (`suc M)                =  free M
free (`pred M)               =  free M
free (`if0 L then M else N)  =  free L ++ free M ++ free N
free (`Y M)                  =  free M
\end{code}

### Fresh identifier

\begin{code}
fresh : List Id → Id
fresh = foldr _⊔_ 0 ∘ map suc

⊔-lemma : ∀ {w xs} → w ∈ xs → suc w ≤ fresh xs
⊔-lemma {_} {_ ∷ xs} here        =  m≤m⊔n _ (fresh xs)
⊔-lemma {w} {x ∷ xs} (there x∈)  =  ≤-trans (⊔-lemma {w} {xs} x∈) (n≤m⊔n (suc x) (fresh xs))

fresh-lemma : ∀ {x xs} → x ∈ xs → x ≢ fresh xs
fresh-lemma x∈ refl =  1+n≰n (⊔-lemma x∈)
\end{code}

### Identifier maps

\begin{code}
∅ : Id → Term
∅ x = ⌊ x ⌋

infixl 5 _,_↦_

_,_↦_ : (Id → Term) → Id → Term → (Id → Term)
(ρ , x ↦ M) w with w ≟ x
...               | yes _   =  M
...               | no  _   =  ρ w
\end{code}

### Substitution

\begin{code}
subst : List Id → (Id → Term) → Term → Term
subst ys ρ (⌊ x ⌋)     =  ρ x
subst ys ρ (ƛ x ⇒ N)  =  ƛ y ⇒ subst (y ∷ ys) (ρ , x ↦ ⌊ y ⌋) N
  where
  y = fresh ys
subst ys ρ (L · M)     =  subst ys ρ L · subst ys ρ M
subst ys ρ (`zero)     =  `zero
subst ys ρ (`suc M)    =  `suc (subst ys ρ M)
subst ys ρ (`pred M)   =  `pred (subst ys ρ M)
subst ys ρ (`if0 L then M else N)
  =  `if0 (subst ys ρ L) then (subst ys ρ M) else (subst ys ρ N)
subst ys ρ (`Y M)      =  `Y (subst ys ρ M)  
                       
_[_:=_] : Term → Id → Term → Term
N [ x := M ]  =  subst (free M ++ (free N \\ x)) (∅ , x ↦ M) N
\end{code}

### Testing substitution

\begin{code}
_ : (⌊ s ⌋ · ⌊ s ⌋ · ⌊ z ⌋) [ z := `zero ] ≡ (⌊ s ⌋ · ⌊ s ⌋ · `zero)
_ = refl

_ : (⌊ s ⌋ · ⌊ s ⌋ · ⌊ z ⌋)[ s := (ƛ m ⇒ `suc ⌊ m ⌋) ] [ z := `zero ] 
     ≡ ((ƛ p ⇒ `suc ⌊ p ⌋) · (ƛ p ⇒ `suc ⌊ p ⌋) · `zero)
_ = refl

_ : (ƛ m ⇒ ⌊ m ⌋ · ⌊ n ⌋) [ n := ⌊ m ⌋ ] ≡  (ƛ n ⇒ ⌊ n ⌋ · ⌊ m ⌋)
_ = refl

_ : subst [ m , n ] (∅ , m ↦ ⌊ n ⌋ , n ↦ ⌊ m ⌋) (⌊ m ⌋ · ⌊ n ⌋)  ≡  (⌊ n ⌋ · ⌊ m ⌋)
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
    → Value (ƛ x ⇒ N)
\end{code}

## Reduction

\begin{code}
infix 4 _⟶_

data _⟶_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L ⟶ L′
      ----------------
    → L · M ⟶ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M ⟶ M′
      ----------------
    → V · M ⟶ V · M′

  β-⇒ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V ⟶ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M ⟶ M′
      ------------------
    → `suc M ⟶ `suc M′

  ξ-pred : ∀ {M M′}
    → M ⟶ M′
      --------------------
    → `pred M ⟶ `pred M′

  β-pred-zero :
      ---------------------
      `pred `zero ⟶ `zero

  β-pred-suc : ∀ {V}
    → Value V
      --------------------
    → `pred (`suc V) ⟶ V

  ξ-if0 : ∀ {L L′ M N}
    → L ⟶ L′
      ----------------------------------------------
    → `if0 L then M else N ⟶ `if0 L′ then M else N

  β-if0-zero : ∀ {M N}
      ------------------------------
    → `if0 `zero then M else N ⟶ M
  
  β-if0-suc : ∀ {V M N}
    → Value V
      ---------------------------------
    → `if0 (`suc V) then M else N ⟶ N

  ξ-Y : ∀ {M M′}
    → M ⟶ M′
      --------------
    → `Y M ⟶ `Y M′

  β-Y : ∀ {V x N}
    → Value V
    → V ≡ ƛ x ⇒ N
      ------------------------
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
      ------------------
      Canonical `zero `ℕ

  Suc : ∀ {V}
    → Canonical V `ℕ
      ---------------------
    → Canonical (`suc V) `ℕ
 
  Fun : ∀ {x N A B}
    → ε , x ⦂ A ⊢ N ⦂ B
      ------------------------------
    → Canonical (ƛ x ⇒ N) (A ⇒ B)
\end{code}

## Canonical forms lemma

Every typed value is canonical.

\begin{code}
canonical : ∀ {V A}
  → ε ⊢ V ⦂ A
  → Value V
    -------------
  → Canonical V A
canonical ⊢zero     Zero      =  Zero
canonical (⊢suc ⊢V) (Suc VV)  =  Suc (canonical ⊢V VV)
canonical (⊢λ ⊢N)   Fun       =  Fun ⊢N
\end{code}

Every canonical form has a type and a value.

\begin{code}
type : ∀ {V A}
  → Canonical V A
    -------------
  → ε ⊢ V ⦂ A
type Zero         =  ⊢zero
type (Suc CV)     =  ⊢suc (type CV)
type (Fun ⊢N)     =  ⊢λ ⊢N

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

progress : ∀ {M A} → ε ⊢ M ⦂ A → Progress M A
progress (Ax ())
progress (⊢λ ⊢N)                           =  done (Fun ⊢N)
progress (⊢L · ⊢M) with progress ⊢L
...    | step L⟶L′                       =  step (ξ-·₁ L⟶L′)
...    | done (Fun _) with progress ⊢M
...            | step M⟶M′               =  step (ξ-·₂ Fun M⟶M′)
...            | done CM                   =  step (β-⇒ (value CM))
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

### Lemmas about free variables

\begin{code}
id : ∀ {X : Set} → X → X
id x = x

fr-⌊⌋ : ∀ {x} → x ∈ free ⌊ x ⌋
fr-⌊⌋ = here

fr-ƛ : ∀ {x N xs} → free (ƛ x ⇒ N) ⊆ xs → free N ⊆ x ∷ xs
fr-ƛ = \\-to-∷

{-
fr-ƛ : ∀ {x N} → free (ƛ x ⇒ N) ⊆ free N
fr-ƛ = proj₁ ∘ \\-to-∈-≢

fr-ƛ-≢ : ∀ {w x N} → w ∈ free (ƛ x ⇒ N) → w ≢ x
fr-ƛ-≢ {w} {x} {N} = proj₂ ∘ \\-to-∈-≢ {w} {x} {free N}
-}

fr-·₁ : ∀ {L M xs Γ A B} → Γ ⊢ L ⦂ A ⇒ B → Γ ⊢ M ⦂ A → free (L · M) ⊆ xs → free L ⊆ xs
fr-·₁ ⊢L ⊢M ⊆xs = ⊆xs ∘ ⊆-++₁

fr-·₂ : ∀ {L M xs Γ A B} → Γ ⊢ L ⦂ A ⇒ B → Γ ⊢ M ⦂ A → free (L · M) ⊆ xs → free M ⊆ xs
fr-·₂ ⊢L ⊢M ⊆xs = ⊆xs ∘ ⊆-++₂

fr-suc : ∀ {M} → free M ⊆ free (`suc M)
fr-suc = id

fr-pred : ∀ {M} → free M ⊆ free (`pred M)
fr-pred = id

fr-if0₁ : ∀ {L M N xs Γ A} → Γ ⊢ L ⦂ `ℕ → Γ ⊢ M ⦂ A → Γ ⊢ N ⦂ A
            → free (`if0 L then M else N) ⊆ xs → free L ⊆ xs
fr-if0₁ ⊢L ⊢M ⊢N ⊆xs = ⊆xs ∘ ⊆-++₁

fr-if0₂ : ∀ {L M N xs Γ A} → Γ ⊢ L ⦂ `ℕ → Γ ⊢ M ⦂ A → Γ ⊢ N ⦂ A
            → free (`if0 L then M else N) ⊆ xs → free M ⊆ xs
fr-if0₂ {L} ⊢L ⊢M ⊢N ⊆xs = ⊆xs ∘ ⊆-++₂ {free L} ∘ ⊆-++₁

fr-if0₃ : ∀ {L M N xs Γ A} → Γ ⊢ L ⦂ `ℕ → Γ ⊢ M ⦂ A → Γ ⊢ N ⦂ A
            → free (`if0 L then M else N) ⊆ xs → free N ⊆ xs
fr-if0₃ {L} ⊢L ⊢M ⊢N ⊆xs = ⊆xs ∘ ⊆-++₂ {free L} ∘ ⊆-++₂

fr-Y : ∀ {M} → free M ⊆ free (`Y M)
fr-Y = id
\end{code}

### Domain of an environment

\begin{code}
dom : Env → List Id
dom ε            =  []
dom (Γ , x ⦂ A)  =  x ∷ dom Γ

dom-lemma : ∀ {Γ y B} → Γ ∋ y ⦂ B → y ∈ dom Γ
dom-lemma Z           =  here
dom-lemma (S x≢y ⊢y)  =  there (dom-lemma ⊢y)

free-lemma : ∀ {Γ M A} → Γ ⊢ M ⦂ A → free M ⊆ dom Γ
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
\end{code}

### Renaming

\begin{code}
⊢rename : ∀ {Γ Δ xs}
  → (∀ {x A} → x ∈ xs      →  Γ ∋ x ⦂ A  →  Δ ∋ x ⦂ A)
    --------------------------------------------------
  → (∀ {M A} → free M ⊆ xs →  Γ ⊢ M ⦂ A  →  Δ ⊢ M ⦂ A)
⊢rename ⊢σ ⊆xs (Ax ⊢x)     =  Ax (⊢σ ∈xs ⊢x)
  where
  ∈xs = ⊆xs fr-⌊⌋
⊢rename {Γ} {Δ} {xs} ⊢σ ⊆xs (⊢λ {x = x} {N = N} {A = A} ⊢N)
                           =  ⊢λ (⊢rename {Γ′} {Δ′} {xs′} ⊢σ′ ⊆xs′ ⊢N)
  where
  Γ′   =  Γ , x ⦂ A
  Δ′   =  Δ , x ⦂ A
  xs′  =  x ∷ xs

  ⊢σ′ : ∀ {w B} → w ∈ xs′ → Γ′ ∋ w ⦂ B → Δ′ ∋ w ⦂ B
  ⊢σ′ w∈′ Z          =  Z
  ⊢σ′ w∈′ (S w≢ ⊢w)  =  S w≢ (⊢σ ∈w ⊢w)
    where
    ∈w  =  there⁻¹ w∈′ w≢

  ⊆xs′ : free N ⊆ xs′
  ⊆xs′ =  fr-ƛ {x} {N} ⊆xs
⊢rename ⊢σ ⊆xs (⊢L · ⊢M)  =  ⊢rename ⊢σ L⊆ ⊢L · ⊢rename ⊢σ M⊆ ⊢M
  where
  L⊆ = fr-·₁ ⊢L ⊢M ⊆xs
  M⊆ = fr-·₂ ⊢L ⊢M ⊆xs
⊢rename ⊢σ ⊆xs (⊢zero)     =  ⊢zero
⊢rename ⊢σ ⊆xs (⊢suc ⊢M)   =  ⊢suc (⊢rename ⊢σ ⊆xs ⊢M)
⊢rename ⊢σ ⊆xs (⊢pred ⊢M)  =  ⊢pred (⊢rename ⊢σ ⊆xs ⊢M)
⊢rename ⊢σ ⊆xs (⊢if0 ⊢L ⊢M ⊢N)
  = ⊢if0 (⊢rename ⊢σ L⊆ ⊢L) (⊢rename ⊢σ M⊆ ⊢M) (⊢rename ⊢σ N⊆ ⊢N)
    where
    L⊆ = fr-if0₁ ⊢L ⊢M ⊢N ⊆xs
    M⊆ = fr-if0₂ ⊢L ⊢M ⊢N ⊆xs
    N⊆ = fr-if0₃ ⊢L ⊢M ⊢N ⊆xs 
⊢rename ⊢σ ⊆xs (⊢Y ⊢M)     =  ⊢Y (⊢rename ⊢σ ⊆xs ⊢M)
\end{code}


### Substitution preserves types

\begin{code}
⊢subst : ∀ {Γ Δ xs ys ρ}
  → (∀ {x}   → x ∈ xs      →  free (ρ x) ⊆ ys)
  → (∀ {x A} → x ∈ xs      →  Γ ∋ x ⦂ A  →  Δ ⊢ ρ x ⦂ A)
    -------------------------------------------------------------
  → (∀ {M A} → free M ⊆ xs →  Γ ⊢ M ⦂ A  →  Δ ⊢ subst ys ρ M ⦂ A)
⊢subst Σ ⊢ρ ⊆xs (Ax ⊢x)
    =  ⊢ρ (⊆xs here) ⊢x
⊢subst {Γ} {Δ} {xs} {ys} {ρ} Σ ⊢ρ ⊆xs (⊢λ {x = x} {N = N} {A = A} ⊢N)
    = ⊢λ {x = y} {A = A} (⊢subst {Γ′} {Δ′} {xs′} {ys′} {ρ′} Σ′ ⊢ρ′ ⊆xs′ ⊢N)
  where
  y   =  fresh ys
  Γ′  =  Γ , x ⦂ A
  Δ′  =  Δ , y ⦂ A
  xs′ =  x ∷ xs
  ys′ =  y ∷ ys
  ρ′  =  ρ , x ↦ ⌊ y ⌋

  Σ′ : ∀ {w} → w ∈ xs′ →  free (ρ′ w) ⊆ ys′
  Σ′ {w} w∈′ with w ≟ x
  ...            | yes refl    =  ⊆-++₁
  ...            | no  w≢      = (there {x = y}) ∘ Σ (there⁻¹ w∈′ w≢) 
                                  -- (⊆-++₂ {[ y ]} {ys}) ∘ Σ (there⁻¹ w∈′ w≢)
  
  ⊆xs′ :  free N ⊆ xs′
  ⊆xs′ =  \\-to-∷ ⊆xs

  ⊢σ : ∀ {w C} → w ∈ ys → Δ ∋ w ⦂ C → Δ′ ∋ w ⦂ C
  ⊢σ w∈ ⊢w  =  S (fresh-lemma w∈) ⊢w

  ⊢ρ′ : ∀ {w C} → w ∈ xs′ → Γ′ ∋ w ⦂ C → Δ′ ⊢ ρ′ w ⦂ C
  ⊢ρ′ {w} _ Z with w ≟ x
  ...         | yes _             =  Ax Z
  ...         | no  w≢            =  ⊥-elim (w≢ refl)
  ⊢ρ′ {w} w∈′ (S w≢ ⊢w) with w ≟ x
  ...         | yes refl          =  ⊥-elim (w≢ refl)
  ...         | no  _             =  ⊢rename {Δ} {Δ′} {ys} ⊢σ (Σ w∈) (⊢ρ w∈ ⊢w)
              where
              w∈  =  there⁻¹ w∈′ w≢

⊢subst Σ ⊢ρ ⊆xs (_·_ {L = L} {M = M} ⊢L ⊢M)
    =  ⊢subst Σ ⊢ρ L⊆ ⊢L · ⊢subst Σ ⊢ρ M⊆ ⊢M
  where
  L⊆ = trans-⊆ ⊆-++₁ ⊆xs
  M⊆ = trans-⊆ (⊆-++₂ {free L} {free M}) ⊆xs
⊢subst Σ ⊢ρ ⊆xs ⊢zero            =  ⊢zero
⊢subst Σ ⊢ρ ⊆xs (⊢suc ⊢M)        =  ⊢suc (⊢subst Σ ⊢ρ ⊆xs ⊢M)
⊢subst Σ ⊢ρ ⊆xs (⊢pred ⊢M)       =  ⊢pred (⊢subst Σ ⊢ρ ⊆xs ⊢M)
⊢subst Σ ⊢ρ ⊆xs (⊢if0 {L = L} {M = M} {N = N} ⊢L ⊢M ⊢N)
    =  ⊢if0 (⊢subst Σ ⊢ρ L⊆ ⊢L) (⊢subst Σ ⊢ρ M⊆ ⊢M) (⊢subst Σ ⊢ρ N⊆ ⊢N)
    where
    L⊆ = trans-⊆ ⊆-++₁ ⊆xs
    M⊆ = trans-⊆ ⊆-++₁ (trans-⊆ (⊆-++₂ {free L}) ⊆xs)
    N⊆ = trans-⊆ (⊆-++₂ {free M} {free N}) (trans-⊆ (⊆-++₂ {free L}) ⊆xs)
⊢subst Σ ⊢ρ ⊆xs (⊢Y ⊢M)          =  ⊢Y (⊢subst Σ ⊢ρ ⊆xs ⊢M)    

⊢substitution : ∀ {Γ x A N B M} →
  Γ , x ⦂ A ⊢ N ⦂ B →
  Γ ⊢ M ⦂ A →
  --------------------
  Γ ⊢ N [ x := M ] ⦂ B
⊢substitution {Γ} {x} {A} {N} {B} {M} ⊢N ⊢M =
  ⊢subst {Γ′} {Γ} {xs} {ys} {ρ} Σ ⊢ρ {N} {B} ⊆xs ⊢N
  where
  Γ′     =  Γ , x ⦂ A
  xs     =  free N
  ys     =  free M ++ (free N \\ x)
  ρ      =  ∅ , x ↦ M

  Σ : ∀ {w} → w ∈ xs → free (ρ w) ⊆ ys
  Σ {w} w∈ y∈ with w ≟ x
  ...            | yes _                   =  ⊆-++₁ y∈
  ...            | no w≢ rewrite ∈-[_] y∈  =  ⊆-++₂ {free M} {(free N) \\ x} (∈-≢-to-\\ w∈ w≢)
  
  ⊢ρ : ∀ {w B} → w ∈ xs → Γ′ ∋ w ⦂ B → Γ ⊢ ρ w ⦂ B
  ⊢ρ {w} w∈ Z         with w ≟ x
  ...                    | yes _     =  ⊢M
  ...                    | no  w≢    =  ⊥-elim (w≢ refl)
  ⊢ρ {w} w∈ (S w≢ ⊢w) with w ≟ x
  ...                    | yes refl  =  ⊥-elim (w≢ refl)
  ...                    | no  _     =  Ax ⊢w

  ⊆xs : free N ⊆ xs
  ⊆xs x∈ = x∈
\end{code}

### Preservation

\begin{code}
preservation : ∀ {Γ M N A}
  →  Γ ⊢ M ⦂ A
  →  M ⟶ N
     ---------
  →  Γ ⊢ N ⦂ A
preservation (Ax ⊢x) ()
preservation (⊢λ ⊢N) ()
preservation (⊢L · ⊢M)              (ξ-·₁ L⟶)    =  preservation ⊢L L⟶ · ⊢M
preservation (⊢V · ⊢M)              (ξ-·₂ _ M⟶)  =  ⊢V · preservation ⊢M M⟶
preservation ((⊢λ ⊢N) · ⊢W)         (β-⇒ _)       =  ⊢substitution ⊢N ⊢W
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
\end{code}

## Normalise

\begin{code}
data Normalise {M A} (⊢M : ε ⊢ M ⦂ A) : Set where
  out-of-gas : ∀ {N} → M ⟶* N → ε ⊢ N ⦂ A → Normalise ⊢M
  normal     : ∀ {V} → ℕ → Canonical V A → M ⟶* V → Normalise ⊢M

normalise : ∀ {L A} → ℕ → (⊢L : ε ⊢ L ⦂ A) → Normalise ⊢L
normalise {L} zero    ⊢L                   =  out-of-gas (L ∎) ⊢L
normalise {L} (suc m) ⊢L with progress ⊢L
...  | done CL                             =  normal (suc m) CL (L ∎)
...  | step L⟶M with preservation ⊢L L⟶M
...      | ⊢M with normalise m ⊢M
...          | out-of-gas M⟶*N ⊢N        =  out-of-gas (L ⟶⟨ L⟶M ⟩ M⟶*N) ⊢N
...          | normal n CV M⟶*V          =  normal n CV (L ⟶⟨ L⟶M ⟩ M⟶*V)
\end{code}

## Test case

\begin{code}
_ : plus · two · two ⟶* (`suc (`suc (`suc (`suc `zero))))
_ =
  (`Y
    (ƛ 0 ⇒
     (ƛ 1 ⇒
      (ƛ 2 ⇒
       `if0 ⌊ 1 ⌋ then ⌊ 2 ⌋ else `suc ⌊ 0 ⌋ · (`pred ⌊ 1 ⌋) · ⌊ 2 ⌋))))
   · (`suc (`suc `zero))
   · (`suc (`suc `zero))
   ⟶⟨ ξ-·₁ (ξ-·₁ (β-Y Fun refl)) ⟩
   (ƛ 0 ⇒
    (ƛ 1 ⇒
     `if0 ⌊ 0 ⌋ then ⌊ 1 ⌋ else
     `suc
     (`Y
      (ƛ 0 ⇒
       (ƛ 1 ⇒
        (ƛ 2 ⇒
         `if0 ⌊ 1 ⌋ then ⌊ 2 ⌋ else `suc ⌊ 0 ⌋ · (`pred ⌊ 1 ⌋) · ⌊ 2 ⌋))))
     · (`pred ⌊ 0 ⌋)
     · ⌊ 1 ⌋))
   · (`suc (`suc `zero))
   · (`suc (`suc `zero))
   ⟶⟨ ξ-·₁ (β-⇒ (Suc (Suc Zero))) ⟩
   (ƛ 0 ⇒
    `if0 `suc (`suc `zero) then ⌊ 0 ⌋ else
    `suc
    (`Y
     (ƛ 1 ⇒
      (ƛ 2 ⇒
       (ƛ 3 ⇒
        `if0 ⌊ 2 ⌋ then ⌊ 3 ⌋ else `suc ⌊ 1 ⌋ · (`pred ⌊ 2 ⌋) · ⌊ 3 ⌋))))
    · (`pred (`suc (`suc `zero)))
    · ⌊ 0 ⌋)
   · (`suc (`suc `zero))
   ⟶⟨ β-⇒ (Suc (Suc Zero)) ⟩
   `if0 `suc (`suc `zero) then `suc (`suc `zero) else
   `suc
   (`Y
    (ƛ 0 ⇒
     (ƛ 1 ⇒
      (ƛ 2 ⇒
       `if0 ⌊ 1 ⌋ then ⌊ 2 ⌋ else `suc ⌊ 0 ⌋ · (`pred ⌊ 1 ⌋) · ⌊ 2 ⌋))))
   · (`pred (`suc (`suc `zero)))
   · (`suc (`suc `zero))
   ⟶⟨ β-if0-suc (Suc Zero) ⟩
   `suc
   (`Y
    (ƛ 0 ⇒
     (ƛ 1 ⇒
      (ƛ 2 ⇒
       `if0 ⌊ 1 ⌋ then ⌊ 2 ⌋ else `suc ⌊ 0 ⌋ · (`pred ⌊ 1 ⌋) · ⌊ 2 ⌋))))
   · (`pred (`suc (`suc `zero)))
   · (`suc (`suc `zero))
   ⟶⟨ ξ-suc (ξ-·₁ (ξ-·₁ (β-Y Fun refl))) ⟩
   `suc
   (ƛ 0 ⇒
    (ƛ 1 ⇒
     `if0 ⌊ 0 ⌋ then ⌊ 1 ⌋ else
     `suc
     (`Y
      (ƛ 0 ⇒
       (ƛ 1 ⇒
        (ƛ 2 ⇒
         `if0 ⌊ 1 ⌋ then ⌊ 2 ⌋ else `suc ⌊ 0 ⌋ · (`pred ⌊ 1 ⌋) · ⌊ 2 ⌋))))
     · (`pred ⌊ 0 ⌋)
     · ⌊ 1 ⌋))
   · (`pred (`suc (`suc `zero)))
   · (`suc (`suc `zero))
   ⟶⟨ ξ-suc (ξ-·₁ (ξ-·₂ Fun (β-pred-suc (Suc Zero)))) ⟩
   `suc
   (ƛ 0 ⇒
    (ƛ 1 ⇒
     `if0 ⌊ 0 ⌋ then ⌊ 1 ⌋ else
     `suc
     (`Y
      (ƛ 0 ⇒
       (ƛ 1 ⇒
        (ƛ 2 ⇒
         `if0 ⌊ 1 ⌋ then ⌊ 2 ⌋ else `suc ⌊ 0 ⌋ · (`pred ⌊ 1 ⌋) · ⌊ 2 ⌋))))
     · (`pred ⌊ 0 ⌋)
     · ⌊ 1 ⌋))
   · (`suc `zero)
   · (`suc (`suc `zero))
   ⟶⟨ ξ-suc (ξ-·₁ (β-⇒ (Suc Zero))) ⟩
   `suc
   (ƛ 0 ⇒
    `if0 `suc `zero then ⌊ 0 ⌋ else
    `suc
    (`Y
     (ƛ 1 ⇒
      (ƛ 2 ⇒
       (ƛ 3 ⇒
        `if0 ⌊ 2 ⌋ then ⌊ 3 ⌋ else `suc ⌊ 1 ⌋ · (`pred ⌊ 2 ⌋) · ⌊ 3 ⌋))))
    · (`pred (`suc `zero))
    · ⌊ 0 ⌋)
   · (`suc (`suc `zero))
   ⟶⟨ ξ-suc (β-⇒ (Suc (Suc Zero))) ⟩
   `suc
   (`if0 `suc `zero then `suc (`suc `zero) else
    `suc
    (`Y
     (ƛ 0 ⇒
      (ƛ 1 ⇒
       (ƛ 2 ⇒
        `if0 ⌊ 1 ⌋ then ⌊ 2 ⌋ else `suc ⌊ 0 ⌋ · (`pred ⌊ 1 ⌋) · ⌊ 2 ⌋))))
    · (`pred (`suc `zero))
    · (`suc (`suc `zero)))
   ⟶⟨ ξ-suc (β-if0-suc Zero) ⟩
   `suc
   (`suc
    (`Y
     (ƛ 0 ⇒
      (ƛ 1 ⇒
       (ƛ 2 ⇒
        `if0 ⌊ 1 ⌋ then ⌊ 2 ⌋ else `suc ⌊ 0 ⌋ · (`pred ⌊ 1 ⌋) · ⌊ 2 ⌋))))
    · (`pred (`suc `zero))
    · (`suc (`suc `zero)))
   ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ (β-Y Fun refl)))) ⟩
   `suc
   (`suc
    (ƛ 0 ⇒
     (ƛ 1 ⇒
      `if0 ⌊ 0 ⌋ then ⌊ 1 ⌋ else
      `suc
      (`Y
       (ƛ 0 ⇒
        (ƛ 1 ⇒
         (ƛ 2 ⇒
          `if0 ⌊ 1 ⌋ then ⌊ 2 ⌋ else `suc ⌊ 0 ⌋ · (`pred ⌊ 1 ⌋) · ⌊ 2 ⌋))))
      · (`pred ⌊ 0 ⌋)
      · ⌊ 1 ⌋))
    · (`pred (`suc `zero))
    · (`suc (`suc `zero)))
   ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₂ Fun (β-pred-suc Zero)))) ⟩
   `suc
   (`suc
    (ƛ 0 ⇒
     (ƛ 1 ⇒
      `if0 ⌊ 0 ⌋ then ⌊ 1 ⌋ else
      `suc
      (`Y
       (ƛ 0 ⇒
        (ƛ 1 ⇒
         (ƛ 2 ⇒
          `if0 ⌊ 1 ⌋ then ⌊ 2 ⌋ else `suc ⌊ 0 ⌋ · (`pred ⌊ 1 ⌋) · ⌊ 2 ⌋))))
      · (`pred ⌊ 0 ⌋)
      · ⌊ 1 ⌋))
    · `zero
    · (`suc (`suc `zero)))
   ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (β-⇒ Zero))) ⟩
   `suc
   (`suc
    (ƛ 0 ⇒
     `if0 `zero then ⌊ 0 ⌋ else
     `suc
     (`Y
      (ƛ 1 ⇒
       (ƛ 2 ⇒
        (ƛ 3 ⇒
         `if0 ⌊ 2 ⌋ then ⌊ 3 ⌋ else `suc ⌊ 1 ⌋ · (`pred ⌊ 2 ⌋) · ⌊ 3 ⌋))))
     · (`pred `zero)
     · ⌊ 0 ⌋)
    · (`suc (`suc `zero)))
   ⟶⟨ ξ-suc (ξ-suc (β-⇒ (Suc (Suc Zero)))) ⟩
   `suc
   (`suc
    (`if0 `zero then `suc (`suc `zero) else
     `suc
     (`Y
      (ƛ 0 ⇒
       (ƛ 1 ⇒
        (ƛ 2 ⇒
         `if0 ⌊ 1 ⌋ then ⌊ 2 ⌋ else `suc ⌊ 0 ⌋ · (`pred ⌊ 1 ⌋) · ⌊ 2 ⌋))))
     · (`pred `zero)
     · (`suc (`suc `zero))))
   ⟶⟨ ξ-suc (ξ-suc β-if0-zero) ⟩
     `suc (`suc (`suc (`suc `zero)))
   ∎
\end{code}


### Discussion




I can remove the `ys` argument from `subst` by always
computing it as `frees ρ M`. As I step into an abstraction,
this will automatically add the renaming of the bound
variable, since the bound variable gets added to `M` and
its renaming gets added to `ρ`.

A possible new version.
Simpler to state, is it simpler to prove?

What may be tricky to establish is that sufficient
renaming occurs to justify the `≢` term added to `S`.

It may be hard to establish because we use it
when we instantiate `⊢rename′ {Δ} {Δ , y ⦂ A} (S w≢y)`
and the problem is that `w≢y` for every `w` in
`free (ρ x)`, but there may be other `w` in `Δ`.
Bugger. But I think the theorems are true despite
this problem in the proof, so there may be a way
around it.

    frees : (Id → Term) → Term → List Id
    frees ρ M  =  concat (map (free ∘ ρ) (free M))

    subst′ : (Id → Term) → Term → Term 
    subst′ ρ M = subst (frees ρ M) ρ M

    ⊢rename′ : ∀ {Γ Δ M A}
      → (∀ {w B} → Γ ∋ w ⦂ B → Δ ∋ w ⦂ B)
      → Γ ⊢ M ⦂ A
        ----------------------------------
      → Δ ⊢ M ⦂ A
    ⊢rename′ = {!!}  

    ⊢subst′ : ∀ {Γ Δ ρ M A}
      → (∀ {w B} → Γ ∋ w ⦂ B → Δ ⊢ ρ w ⦂ B)
      → Γ ⊢ M ⦂ A
        ------------------------------------
      → Δ ⊢ subst′ ρ M ⦂ A
    ⊢subst′ = {!!}

I expect `⊢rename′` is easy to show.

I think `⊢subst′` is true but hard to show.
The difficult part is to establish the argument to `⊢rename′`,
since I can only create a variable that is fresh with regard to
names in frees, not all names in the domain of `Δ`.

Can I establish a counter-example, or convince myself that
`⊢subst′` is true anyway? The latter is easily seen to be true,
since the simpler formulations are immediate consequences of
what I have already proved.

Stepping into a subterm, just need to precompose `ρ` with a
lemma stating that the free variables of the subterm are
a subset of the free variables of the term.
