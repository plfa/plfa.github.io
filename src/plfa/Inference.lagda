---
title     : "Inference: Bidirectional type inference"
layout    : page
permalink : /Inference/
---

\begin{code}
module plfa.Inference where
\end{code}


## Imports

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
open import plta.DeBruijn as DB using (Type; `ℕ; _⇒_)

pattern [_]       w        =  w ∷ []
pattern [_,_]     w x      =  w ∷ x ∷ []
pattern [_,_,_]   w x y    =  w ∷ x ∷ y ∷ []
pattern [_,_,_,_] w x y z  =  w ∷ x ∷ y ∷ z ∷ []
\end{code}


## Syntax

\begin{code}
infix   4  _∋_⦂_
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_⦂_
infix   5  ƛ_⇒_
infix   5  μ_⇒_
infix   6  _↓_
infix   6  _↑
infixl  7  _·_
infix   8  `suc_
infix   9  `_
\end{code}

These should get imported from Typed (or Fresh, or Raw).

\begin{code}
Id : Set
Id = String

data Ctx : Set where
  ∅      : Ctx
  _,_⦂_ : Ctx → Id → Type → Ctx
\end{code}

Terms that synthesize `Term⁺` and inherit `Term⁻` their types.
\begin{code}
data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  `_                        : Id → Term⁺
  _·_                       : Term⁺ → Term⁻ → Term⁺
  _↓_                       : Term⁻ → Type → Term⁺

data Term⁻ where
  ƛ_⇒_                     : Id → Term⁻ → Term⁻
  `zero                    : Term⁻
  `suc_                    : Term⁻ → Term⁻
  `case_[zero⇒_|suc_⇒_]    : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
  μ_⇒_                     : Id → Term⁻ → Term⁻
  _↑                       : Term⁺ → Term⁻
\end{code}

## Example terms

\begin{code}
two : Term⁻
two = `suc (`suc `zero)

plus : Term⁺
plus = (μ "p" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          `case (` "m") [zero⇒ ` "n" ↑
                        |suc "m" ⇒ `suc (` "p" · (` "m" ↑) · (` "n" ↑) ↑) ])
            ↓ `ℕ ⇒ `ℕ ⇒ `ℕ

Ch : Type
Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

twoᶜ : Term⁻
twoᶜ = (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)

plusᶜ : Term⁺
plusᶜ = (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
           ` "m" · (` "s" ↑) · (` "n" · (` "s" ↑) · (` "z" ↑) ↑) ↑)
             ↓ Ch ⇒ Ch ⇒ Ch

sucᶜ : Term⁻
sucᶜ = ƛ "x" ⇒ `suc (` "x" ↑)
\end{code}


## Bidirectional type checking

\begin{code}
data _∋_⦂_ : Ctx → Id → Type → Set where

  Z : ∀ {Γ x A}
      --------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ w x A B}
    → w ≢ x
    → Γ ∋ w ⦂ B
      --------------------
    → Γ , x ⦂ A ∋ w ⦂ B

data _⊢_↑_ : Ctx → Term⁺ → Type → Set
data _⊢_↓_ : Ctx → Term⁻ → Type → Set

data _⊢_↑_ where

  Ax : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
      --------------
    → Γ ⊢ ` x ↑ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑ A ⇒ B
    → Γ ⊢ M ↓ A
      ---------------
    → Γ ⊢ L · M ↑ B

  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
      -----------------
    → Γ ⊢ (M ↓ A) ↑ A

data _⊢_↓_ where

  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ↓ B
      -----------------------
    → Γ ⊢ ƛ x ⇒ N ↓ A ⇒ B

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
    → Γ , x ⦂ `ℕ ⊢ N ↓ A
      ------------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x ⦂ A ⊢ N ↓ A
      -----------------------
    → Γ ⊢ μ x ⇒ N ↓ A

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
`ℕ         ≟Tp (A ⇒ B)   =  no (λ())
(A  ⇒ B ) ≟Tp `ℕ         =  no (λ())
(A₀ ⇒ B₀) ≟Tp (A₁ ⇒ B₁) with A₀ ≟Tp A₁ | B₀ ≟Tp B₁
... | no A≢    | _         =  no (λ{refl → A≢ refl})
... | yes _    | no B≢     =  no (λ{refl → B≢ refl})
... | yes refl | yes refl  =  yes refl
\end{code}

## Lookup type of a variable in the context

\begin{code}
lookup : ∀ (Γ : Ctx) (x : Id) → TC (∃[ A ](Γ ∋ x ⦂ A))
lookup ∅ x  =
  error⁺ "variable not bound" (` x) []
lookup (Γ , x ⦂ A) w with w ≟ x
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

synthesize Γ (` x) =
  do ⟨ A , ⊢x ⟩ ← lookup Γ x
     return ⟨ A , Ax ⊢x ⟩
synthesize Γ (L · M) =
  do ⟨ A ⇒ B , ⊢L ⟩ ← synthesize Γ L
       where ⟨ `ℕ , _ ⟩ → error⁺ "must apply function" (L · M) []
     ⊢M ← inherit Γ M A
     return ⟨ B , ⊢L · ⊢M ⟩
synthesize Γ (M ↓ A) =
  do ⊢M ← inherit Γ M A
     return ⟨ A , ⊢↓ ⊢M ⟩

inherit Γ (ƛ x ⇒ N) (A ⇒ B) =
  do ⊢N ← inherit (Γ , x ⦂ A) N B
     return (⊢ƛ ⊢N)
inherit Γ (ƛ x ⇒ N) `ℕ =
  error⁻ "lambda cannot be of type natural" (ƛ x ⇒ N) []
inherit Γ `zero `ℕ =
  return ⊢zero
inherit Γ `zero (A ⇒ B) =
  error⁻ "zero cannot be function" `zero [ A ⇒ B ]
inherit Γ (`suc M) `ℕ =
  do ⊢M ← inherit Γ M `ℕ
     return (⊢suc ⊢M)
inherit Γ (`suc M) (A ⇒ B) =
  error⁻ "suc cannot be function" (`suc M) [ A ⇒ B ]
inherit Γ (`case L [zero⇒ M |suc x ⇒ N ]) A =
  do ⟨ `ℕ , ⊢L ⟩ ← synthesize Γ L
       where ⟨ B ⇒ C , _ ⟩ → error⁻ "cannot case on function"
                                    (`case L [zero⇒ M |suc x ⇒ N ])
                                    [ B ⇒ C ]
     ⊢M ← inherit Γ M A
     ⊢N ← inherit (Γ , x ⦂ `ℕ) N A
     return (⊢case ⊢L ⊢M ⊢N)
inherit Γ (μ x ⇒ M) A =
  do ⊢M ← inherit (Γ , x ⦂ A) M A
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

2+2 : Term⁺
2+2 = plus · two · two

⊢2+2 : ∅ ⊢ 2+2 ↑ `ℕ
⊢2+2 =
  (⊢↓
   (⊢μ
    (⊢ƛ
     (⊢ƛ
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
   · ⊢suc (⊢suc ⊢zero))

_ : synthesize ∅ 2+2 ≡ return ⟨ `ℕ , ⊢2+2 ⟩
_ = refl

2+2ᶜ : Term⁺
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

⊢2+2ᶜ : ∅ ⊢ 2+2ᶜ ↑ `ℕ
⊢2+2ᶜ =
  ⊢↓
  (⊢ƛ
   (⊢ƛ
    (⊢ƛ
     (⊢ƛ
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
  ⊢ƛ
  (⊢ƛ
   (⊢↑
    (Ax (S (_≠_ "s" "z") Z) ·
     ⊢↑ (Ax (S (_≠_ "s" "z") Z) · ⊢↑ (Ax Z) refl)
     refl)
    refl))
  ·
  ⊢ƛ
  (⊢ƛ
   (⊢↑
    (Ax (S (_≠_ "s" "z") Z) ·
     ⊢↑ (Ax (S (_≠_ "s" "z") Z) · ⊢↑ (Ax Z) refl)
     refl)
    refl))
  · ⊢ƛ (⊢suc (⊢↑ (Ax Z) refl))
  · ⊢zero

_ : synthesize ∅ 2+2ᶜ ≡ return ⟨ `ℕ , ⊢2+2ᶜ ⟩
_ = refl
\end{code}

## Testing all possible errors

\begin{code}
_ : synthesize ∅ ((ƛ "x" ⇒ ` "y" ↑) ↓ `ℕ ⇒ `ℕ) ≡
  error⁺ "variable not bound" (` "y") []
_ = refl

_ : synthesize ∅ ((two ↓ `ℕ) · two) ≡
  error⁺ "must apply function"
    ((`suc (`suc `zero) ↓ `ℕ) · `suc (`suc `zero)) []
_ = refl

_ : synthesize ∅ (twoᶜ ↓ `ℕ) ≡
  error⁻ "lambda cannot be of type natural"
    (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)) []
_ = refl

_ : synthesize ∅ (`zero ↓ `ℕ ⇒ `ℕ) ≡
  error⁻ "zero cannot be function" `zero [ `ℕ ⇒ `ℕ ]
_ = refl

_ : synthesize ∅ (two ↓ `ℕ ⇒ `ℕ) ≡
  error⁻ "suc cannot be function" (`suc (`suc `zero)) [ `ℕ ⇒ `ℕ ]
_ = refl

_ : synthesize ∅
      ((`case (twoᶜ ↓ Ch) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡
  error⁻ "cannot case on function"
    `case (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑))
          ↓ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ]
    [ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ]
_ = refl

_ : synthesize ∅ (((ƛ "x" ⇒ ` "x" ↑) ↓ `ℕ ⇒ (`ℕ ⇒ `ℕ))) ≡
  error⁺ "inheritance and synthesis conflict" (` "x") [ `ℕ , `ℕ ⇒ `ℕ ]
_ = refl
\end{code}


## Erasure

\begin{code}
∥_∥Γ : Ctx → DB.Ctx
∥ ∅ ∥Γ = DB.∅
∥ Γ , x ⦂ A ∥Γ = ∥ Γ ∥Γ DB., A

∥_∥∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ∥ Γ ∥Γ DB.∋ A
∥ Z ∥∋ =  DB.Z
∥ S w≢ ⊢w ∥∋ =  DB.S ∥ ⊢w ∥∋

∥_∥⁺ : ∀ {Γ M A} → Γ ⊢ M ↑ A → ∥ Γ ∥Γ DB.⊢ A
∥_∥⁻ : ∀ {Γ M A} → Γ ⊢ M ↓ A → ∥ Γ ∥Γ DB.⊢ A

∥ Ax ⊢x ∥⁺ =  DB.` ∥ ⊢x ∥∋
∥ ⊢L · ⊢M ∥⁺ =  ∥ ⊢L ∥⁺ DB.· ∥ ⊢M ∥⁻
∥ ⊢↓ ⊢M ∥⁺ =  ∥ ⊢M ∥⁻

∥ ⊢ƛ ⊢N ∥⁻ =  DB.ƛ ∥ ⊢N ∥⁻
∥ ⊢zero ∥⁻ =  DB.`zero
∥ ⊢suc ⊢M ∥⁻ =  DB.`suc ∥ ⊢M ∥⁻
∥ ⊢case ⊢L ⊢M ⊢N ∥⁻ =  DB.`case ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁻ ∥ ⊢N ∥⁻
∥ ⊢μ ⊢M ∥⁻ =  DB.μ ∥ ⊢M ∥⁻
∥ ⊢↑ ⊢M refl ∥⁻ =  ∥ ⊢M ∥⁺
\end{code}

Testing erasure

\begin{code}
_ : ∥ ⊢2+2 ∥⁺ ≡ DB.2+2
_ = refl

_ : ∥ ⊢2+2ᶜ ∥⁺ ≡ DB.2+2ᶜ
_ = refl
\end{code}
