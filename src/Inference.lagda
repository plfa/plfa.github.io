---
title     : "Inference: Bidirectional type inference"
layout    : page
permalink : /Inference
---

## Imports

\begin{code}
module Inference where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; foldr; filter; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.String using (String; _≟_; _++_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
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


## Identifiers

\begin{code}
Id : Set
Id = String
\end{code}

## Syntax

\begin{code}
infix   4  _∋_`:_
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_`:_
infix   6  `λ_`→_
infix   6  `μ_`→_
infix   7  _↓_
infix   7  _↑
infixr  8  _`→_
infixl  9  _·_

data Type : Set where
  `ℕ   : Type
  _`→_ : Type → Type → Type

data Ctx : Set where
  ε      : Ctx
  _,_`:_ : Ctx → Id → Type → Ctx
\end{code}  

Terms that synthesize `Term⁺` and inherit `Term⁻` their types.
\begin{code}
data Term⁺ : Set 
data Term⁻ : Set

data Term⁺ where
  ⌊_⌋                        : Id → Term⁺
  _·_                       : Term⁺ → Term⁻ → Term⁺
  _↓_                       : Term⁻ → Type → Term⁺

data Term⁻ where
  `λ_`→_                     : Id → Term⁻ → Term⁻
  `zero                      : Term⁻
  `suc                       : Term⁻ → Term⁻
  `case_[`zero`→_|`suc_`→_]  : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
  `μ_`→_                     : Id → Term⁻ → Term⁻
  _↑                         : Term⁺ → Term⁻
\end{code}

## Example terms

\begin{code}
two : Term⁻
two = `suc (`suc `zero)

plus : Term⁺
plus = (`μ "p" `→ `λ "m" `→ `λ "n" `→
          `case ⌊ "m" ⌋ [`zero`→ ⌊ "n" ⌋ ↑
                        |`suc "m" `→ `suc (⌊ "p" ⌋ · (⌊ "m" ⌋ ↑) · (⌊ "n" ⌋ ↑) ↑) ])
            ↓ `ℕ `→ `ℕ `→ `ℕ

four : Term⁺
four = plus · two · two

Ch : Type
Ch = (`ℕ `→ `ℕ) `→ `ℕ `→ `ℕ

twoCh : Term⁻
twoCh = (`λ "s" `→ `λ "z" `→ ⌊ "s" ⌋ · (⌊ "s" ⌋ · (⌊ "z" ⌋ ↑) ↑) ↑)

plusCh : Term⁺
plusCh = (`λ "m" `→ `λ "n" `→ `λ "s" `→ `λ "z" `→
           ⌊ "m" ⌋ · (⌊ "s" ⌋ ↑) · (⌊ "n" ⌋ · (⌊ "s" ⌋ ↑) · (⌊ "z" ⌋ ↑) ↑) ↑)
             ↓ Ch `→ Ch `→ Ch

fromCh : Term⁺
fromCh = (`λ "m" `→ ⌊ "m" ⌋ · (`λ "x" `→ `suc (⌊ "x" ⌋ ↑)) · `zero ↑)
           ↓ Ch `→ `ℕ

fourCh : Term⁺
fourCh = fromCh · (plusCh · twoCh · twoCh ↑)
\end{code}
## Bidirectional type checking

\begin{code}
data _∋_`:_ : Ctx → Id → Type → Set where

  Z : ∀ {Γ x A}
      --------------------
    → Γ , x `: A ∋ x `: A

  S : ∀ {Γ w x A B}
    → w ≢ x
    → Γ ∋ w `: B
      --------------------
    → Γ , x `: A ∋ w `: B

data _⊢_↑_ : Ctx → Term⁺ → Type → Set
data _⊢_↓_ : Ctx → Term⁻ → Type → Set

data _⊢_↑_ where

  Ax : ∀ {Γ A x}
    → Γ ∋ x `: A
      --------------
    → Γ ⊢ ⌊ x ⌋ ↑ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑ A `→ B
    → Γ ⊢ M ↓ A
      ---------------
    → Γ ⊢ L · M ↑ B

  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
      -----------------
    → Γ ⊢ (M ↓ A) ↑ A

data _⊢_↓_ where

  ⊢λ : ∀ {Γ x N A B}
    → Γ , x `: A ⊢ N ↓ B
      -----------------------
    → Γ ⊢ `λ x `→ N ↓ A `→ B

  ⊢zero : ∀ {Γ}
      ---------------
    → Γ ⊢ `zero ↓ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ↓ `ℕ
      ----------------
    → Γ ⊢ `suc M ↓ `ℕ

  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ↑ `ℕ
    → Γ ⊢ M ↓ A
    → Γ , x `: `ℕ ⊢ N ↓ A
      ------------------------------------------
    → Γ ⊢ `case L [`zero`→ M |`suc x `→ N ] ↓ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x `: A ⊢ N ↓ A
      -----------------------
    → Γ ⊢ `μ x `→ N ↓ A

  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≡ B
      --------------
    → Γ ⊢ (M ↑) ↓ B
\end{code}

## Type checking monad

\begin{code}
Msg : Set
Msg = String

data TC (A : Set) : Set where
  error⁺  : Msg → Term⁺ → List Type → TC A
  error⁻  : Msg → Term⁻ → List Type → TC A
  return : A → TC A

_>>=_ : ∀ {A B : Set} → TC A → (A → TC B) → TC B
error⁺ msg M As >>= k  =  error⁺ msg M As
error⁻ msg M As >>= k  =  error⁻ msg M As
return v        >>= k  =  k v
\end{code}

## Decide type equality

\begin{code}
_≟Tp_ : (A B : Type) → Dec (A ≡ B)
`ℕ         ≟Tp `ℕ         =  yes refl
`ℕ         ≟Tp (A `→ B)   =  no (λ())
(A  `→ B ) ≟Tp `ℕ         =  no (λ())
(A₀ `→ B₀) ≟Tp (A₁ `→ B₁) with A₀ ≟Tp A₁ | B₀ ≟Tp B₁
... | no A≢    | _         =  no (λ{refl → A≢ refl})
... | yes _    | no B≢     =  no (λ{refl → B≢ refl})
... | yes refl | yes refl  =  yes refl
\end{code}

## Lookup type of a variable in the context

\begin{code}
lookup : ∀ (Γ : Ctx) (x : Id) → TC (∃[ A ](Γ ∋ x `: A))
lookup ε x  =
  error⁺ "variable not bound" ⌊ x ⌋ []
lookup (Γ , x `: A) w with w ≟ x
... | yes refl =
  return ⟨ A , Z ⟩
... | no w≢ =
  do ⟨ A , ⊢x ⟩ ← lookup Γ w
     return ⟨ A , S w≢ ⊢x ⟩
\end{code}
  
## Synthesize and inherit types

\begin{code}
synthesize : ∀ (Γ : Ctx) (M : Term⁺) → TC (∃[ A ](Γ ⊢ M ↑ A))
inherit : ∀ (Γ : Ctx) (M : Term⁻) (A : Type) → TC (Γ ⊢ M ↓ A)

synthesize Γ ⌊ x ⌋ =
  do ⟨ A , ⊢x ⟩ ← lookup Γ x
     return ⟨ A , Ax ⊢x ⟩
synthesize Γ (L · M) =
  do ⟨ A `→ B , ⊢L ⟩ ← synthesize Γ L
       where ⟨ `ℕ , _ ⟩ → error⁺ "must apply function" (L · M) []
     ⊢M ← inherit Γ M A
     return ⟨ B , ⊢L · ⊢M ⟩
synthesize Γ (M ↓ A) =
  do ⊢M ← inherit Γ M A
     return ⟨ A , ⊢↓ ⊢M ⟩

inherit Γ (`λ x `→ N) (A `→ B) =
  do ⊢N ← inherit (Γ , x `: A) N B
     return (⊢λ ⊢N)
inherit Γ (`λ x `→ N) `ℕ =
  error⁻ "lambda cannot be of type natural" (`λ x `→ N) []
inherit Γ `zero `ℕ =
  return ⊢zero
inherit Γ `zero (A `→ B) =
  error⁻ "zero cannot be function" `zero [ A `→ B ]
inherit Γ (`suc M) `ℕ =
  do ⊢M ← inherit Γ M `ℕ
     return (⊢suc ⊢M)
inherit Γ (`suc M) (A `→ B) =
  error⁻ "suc cannot be function" (`suc M) [ A `→ B ]
inherit Γ (`case L [`zero`→ M |`suc x `→ N ]) A =
  do ⟨ `ℕ , ⊢L ⟩ ← synthesize Γ L
       where ⟨ B `→ C , _ ⟩ → error⁻ "cannot case on function"
                                    (`case L [`zero`→ M |`suc x `→ N ])
                                    [ B `→ C ]
     ⊢M ← inherit Γ M A
     ⊢N ← inherit (Γ , x `: `ℕ) N A
     return (⊢case ⊢L ⊢M ⊢N)
inherit Γ (`μ x `→ M) A =
  do ⊢M ← inherit (Γ , x `: A) M A
     return (⊢μ ⊢M)
inherit Γ (M ↑) B =
  do ⟨ A , ⊢M ⟩ ← synthesize Γ M
     yes A≡B ← return (A ≟Tp B)
       where no _ → error⁺ "inheritance and synthesis conflict" M [ A , B ]
     return (⊢↑ ⊢M A≡B)
\end{code}

## Test Cases

\begin{code}
_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y  with x ≟ y
...       | no  x≢y  =  x≢y
...       | yes _    =  ⊥-elim impossible
  where postulate impossible : ⊥

_ : synthesize ε four ≡
  return
    ⟨ `ℕ ,
     (⊢↓
      (⊢μ
       (⊢λ
        (⊢λ
         (⊢case (Ax (S (_≠_ "m" "n") Z)) (⊢↑ (Ax Z) refl)
          (⊢suc
           (⊢↑
            (Ax
             (S (_≠_ "p" "m")
              (S (_≠_ "p" "n")
               (S (_≠_ "p" "m") Z)))
             · ⊢↑ (Ax Z) refl
             · ⊢↑ (Ax (S (_≠_ "n" "m") Z)) refl)
            refl))))))
      · ⊢suc (⊢suc ⊢zero)
      · ⊢suc (⊢suc ⊢zero)) ⟩
_ = refl

_ : synthesize ε fourCh ≡
  return
    ⟨ `ℕ ,
     (⊢↓ (⊢λ (⊢↑ (Ax Z · ⊢λ (⊢suc (⊢↑ (Ax Z) refl)) · ⊢zero) refl)) ·
      ⊢↑
      (⊢↓
       (⊢λ
        (⊢λ
         (⊢λ
          (⊢λ
           (⊢↑
            (Ax
             (S (_≠_ "m" "z")
              (S (_≠_ "m" "s")
               (S (_≠_ "m" "n") Z)))
             · ⊢↑ (Ax (S (_≠_ "s" "z") Z)) refl
             ·
             ⊢↑
             (Ax
              (S (_≠_ "n" "z")
               (S (_≠_ "n" "s") Z))
              · ⊢↑ (Ax (S (_≠_ "s" "z") Z)) refl
              · ⊢↑ (Ax Z) refl)
             refl)
            refl)))))
       ·
       ⊢λ
       (⊢λ
        (⊢↑
         (Ax (S (_≠_ "s" "z") Z) ·
          ⊢↑ (Ax (S (_≠_ "s" "z") Z) · ⊢↑ (Ax Z) refl)
          refl)
         refl))
       ·
       ⊢λ
       (⊢λ
        (⊢↑
         (Ax (S (_≠_ "s" "z") Z) ·
          ⊢↑ (Ax (S (_≠_ "s" "z") Z) · ⊢↑ (Ax Z) refl)
          refl)
         refl)))
      refl) ⟩
_ = refl
\end{code}

## Testing all possible errors

\begin{code}
_ : synthesize ε ((`λ "x" `→ ⌊ "y" ⌋ ↑) ↓ `ℕ `→ `ℕ) ≡
  error⁺ "variable not bound" ⌊ "y" ⌋ []
_ = refl

_ : synthesize ε ((two ↓ `ℕ) · two) ≡
  error⁺ "must apply function"
    ((`suc (`suc `zero) ↓ `ℕ) · `suc (`suc `zero)) []
_ = refl

_ : synthesize ε (twoCh ↓ `ℕ) ≡
  error⁻ "lambda cannot be of type natural"
    (`λ "s" `→ (`λ "z" `→ ⌊ "s" ⌋ · (⌊ "s" ⌋ · (⌊ "z" ⌋ ↑) ↑) ↑)) []
_ = refl 

_ : synthesize ε (`zero ↓ `ℕ `→ `ℕ) ≡
  error⁻ "zero cannot be function" `zero [ `ℕ `→ `ℕ ]
_ = refl 

_ : synthesize ε (two ↓ `ℕ `→ `ℕ) ≡
  error⁻ "suc cannot be function" (`suc (`suc `zero)) [ `ℕ `→ `ℕ ]
_ = refl 

_ : synthesize ε
      ((`case (twoCh ↓ Ch) [`zero`→ `zero |`suc "x" `→ ⌊ "x" ⌋ ↑ ] ↓ `ℕ) ) ≡
  error⁻ "cannot case on function"
    `case (`λ "s" `→ (`λ "z" `→ ⌊ "s" ⌋ · (⌊ "s" ⌋ · (⌊ "z" ⌋ ↑) ↑) ↑))
          ↓ (`ℕ `→ `ℕ) `→ `ℕ `→ `ℕ [`zero`→ `zero |`suc "x" `→ ⌊ "x" ⌋ ↑ ]
    [ (`ℕ `→ `ℕ) `→ `ℕ `→ `ℕ ]
_ = refl 

_ : synthesize ε (((`λ "x" `→ ⌊ "x" ⌋ ↑) ↓ `ℕ `→ (`ℕ `→ `ℕ))) ≡
  error⁺ "inheritance and synthesis conflict" ⌊ "x" ⌋ [ `ℕ , `ℕ `→ `ℕ ]
_ = refl 
\end{code}


