## DeBruijn encodings in Agda

\begin{code}
module DeBruijn where
\end{code}

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
\end{code}

## Syntax

\begin{code}
infixr 4 _⇒_

data Type : Set where
  o : Type
  _⇒_ : Type → Type → Type

data Env : Set where
  ε : Env
  _,_ : Env → Type → Env

data Var : Env → Type → Set where
  zero : ∀ {Γ : Env} {A : Type} → Var (Γ , A) A
  suc : ∀ {Γ : Env} {A B : Type} → Var Γ B → Var (Γ , A) B

data Exp : Env → Type → Set where
  var : ∀ {Γ : Env} {A : Type} → Var Γ A → Exp Γ A
  abs : ∀ {Γ : Env} {A B : Type} → Exp (Γ , A) B → Exp Γ (A ⇒ B)
  app : ∀ {Γ : Env} {A B : Type} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B

type : Type → Set
type o = ℕ
type (A ⇒ B) = type A → type B

env : Env → Set
env ε = ⊤
env (Γ , A) = env Γ × type A
\end{code}

# Test code

\begin{code}
Church : Type
Church = (o ⇒ o) ⇒ o ⇒ o

plus : Exp ε (Church ⇒ Church ⇒ Church)
plus =  (abs (abs (abs (abs (app (app (var (suc (suc (suc zero)))) (var (suc zero))) (app (app (var (suc (suc zero))) (var (suc zero))) (var zero)))))))

one : Exp ε Church
one =  (abs (abs (app (var (suc zero)) (var zero))))

two : Exp ε Church
two = (app (app plus one) one)

four : Exp ε Church
four = (app (app plus two) two)
\end{code}


# Denotational semantics

\begin{code}
lookup : ∀ {Γ : Env} {A : Type} → Var Γ A → env Γ → type A
lookup zero ⟨ ρ , v ⟩ = v
lookup (suc n) ⟨ ρ , v ⟩ = lookup n ρ

eval : ∀ {Γ : Env} {A : Type} → Exp Γ A → env Γ → type A
eval (var n) ρ  =  lookup n ρ
eval (abs N) ρ  =  λ{ v → eval N ⟨ ρ , v ⟩ }
eval (app L M) ρ  =  eval L ρ (eval M ρ)

ex : eval four tt suc 0 ≡ 4
ex = refl
\end{code}

# Operational semantics

## Substitution

\begin{code}
extr : ∀ {Γ Δ : Env} {B : Type} → (∀ {A : Type} → Var Γ A → Var Δ A) → Var Δ B → (∀ {A : Type} → Var (Γ , B) A → Var Δ A)
extr ρ v zero     =  v
extr ρ v (suc k)  =  ρ k

ren : ∀ {Γ Δ : Env} → (∀ {A : Type} → Var Γ A → Var Δ A) → (∀ {A : Type} → Exp Γ A → Exp Δ A)
ren ρ (var n)    =  var (ρ n)
ren ρ (app L M)  =  app (ren ρ L) (ren ρ M)
ren ρ (abs N)    =  abs (ren (extr (suc ∘ ρ) zero) N)
\end{code}

\begin{code}
ext :  ∀ {Γ Δ : Env} {B : Type} → (∀ {A : Type} → Var Γ A → Exp Δ A) → Exp Δ B → (∀ {A : Type} → Var (Γ , B) A → Exp Δ A)
ext ρ v zero     =  v
ext ρ v (suc k)  =  ρ k

emp : ∀ {Γ : Env} → (∀ {A : Type} → Var Γ A → Exp Γ A)
emp k = var k

sub : ∀ {Γ Δ : Env} → (∀ {A : Type} → Var Γ A → Exp Δ A) → (∀ {A : Type} → Exp Γ A → Exp Δ A)
sub ρ (var n)    =  ρ n
sub ρ (app L M)  =  app (sub ρ L) (sub ρ M)
sub ρ (abs N)    =  abs (sub (ext (ren suc ∘ ρ) (var zero)) N)

subst : ∀ {Γ : Env} {A B : Type} → Exp (Γ , A) B → Exp Γ A → Exp Γ B
subst N M =  sub (ext emp M) N 
\end{code}

## Reduction step

\begin{code}
data Val : {Γ : Env} {A : Type} → Exp Γ A → Set where

data Step : {Γ : Env} {A : Type} → Exp Γ A → Exp Γ A → Set where
  beta : ∀ {Γ : Env} {A B : Type} {N : Exp (Γ , A) B} {M : Exp Γ A} → Step (app (abs N) M) (subst N M) 
\end{code}
