## DeBruijn encodings in Agda

\begin{code}
module DeBruijn where
\end{code}

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
\end{code}

## Representation

\begin{code}
data Type : Set where
  `ℕ : Type
  _`→_ : Type → Type → Type

data Env : Set where
  ε : Env
  _,_ : Env → Type → Env

data Var : Env → Type → Set where
  zero : ∀ {Γ : Env} {A : Type} → Var (Γ , A) A
  suc : ∀ {Γ : Env} {A B : Type} → Var Γ B → Var (Γ , A) B

data Exp : Env → Type → Set where
  var : ∀ {Γ : Env} {A : Type} → Var Γ A → Exp Γ A
  abs : ∀ {Γ : Env} {A B : Type} → Exp (Γ , A) B → Exp Γ (A `→ B)
  app : ∀ {Γ : Env} {A B : Type} → Exp Γ (A `→ B) → Exp Γ A → Exp Γ B

type : Type → Set
type `ℕ = ℕ
type (A `→ B) = type A → type B

env : Env → Set
env ε = ⊤
env (Γ , A) = env Γ × type A

lookup : ∀ {Γ : Env} {A : Type} → Var Γ A → env Γ → type A
lookup zero ⟨ ρ , v ⟩ = v
lookup (suc n) ⟨ ρ , v ⟩ = lookup n ρ

eval : ∀ {Γ : Env} {A : Type} → Exp Γ A → env Γ → type A
eval (var n) ρ  = lookup n ρ
eval (abs N) ρ  = λ{ v → eval N ⟨ ρ , v ⟩ }
eval (app L M) ρ  =  eval L ρ (eval M ρ)
\end{code}
