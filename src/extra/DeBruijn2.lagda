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
infixr 4 _,_

data TEnv : Set where
  ε : TEnv
  _,* : TEnv → TEnv

data Type : TEnv → Set where
  `ℕ : ∀ {Δ : TEnv} → Type Δ
  _`→_ : ∀ {Δ : TEnv} → Type Δ → Type Δ → Type Δ
  `∀ : ∀ {Δ : TEnv} → Type (Δ ,*) → Type Δ

data Env : TEnv → Set where
  ε : {Δ : TEnv} → Env Δ
  _,_ : {Δ : TEnv} → Env Δ → Type Δ → Env Δ

data TVar : TEnv → Set where
  zero : ∀ {Δ : TEnv} → TVar (Δ ,*)
  suc : ∀ {Δ : TEnv} → TVar Δ → TVar (Δ ,*)

data Var : (Δ : TEnv) → Env Δ → Type Δ → Set where
  zero : ∀ {Δ : TEnv} {Γ : Env Δ} {A : Type Δ} → Var Δ (Γ , A) A
  suc : ∀ {Δ : TEnv} {Γ : Env Δ} {A B : Type Δ} → Var Δ Γ B → Var Δ (Γ , A) B

sub : ∀ {Δ : TEnv} → Type (Δ ,*) → TVar (Δ ,*) → Type Δ → Type Δ
sub = ?

data Exp : (Δ : TEnv) → Env Δ → Type Δ → Set where
  var : ∀ {Δ : TEnv} {Γ : Env Δ} {A : Type Δ} → Var Δ Γ A → Exp Δ Γ A
  abs : ∀ {Δ : TEnv} {Γ : Env Δ} {A B : Type Δ} → Exp Δ (Γ , A) B → Exp Δ Γ (A `→ B)
  app : ∀ {Δ : TEnv} {Γ : Env Δ} {A B : Type Δ} → Exp Δ Γ (A `→ B) → Exp Δ Γ A → Exp Δ Γ B
  tabs : ∀ {Δ : TEnv} {Γ : Env Δ} {B : Type Δ} → Exp (Δ ,*) Γ B → Exp Δ Γ (`∀ B)
  tapp : ∀ {Δ : TEnv} {Γ : Env Δ} {B : Type Δ} → Exp Δ Γ (`∀ B) → (A : Type Δ) → Exp Δ Γ (sub B zero A)

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
