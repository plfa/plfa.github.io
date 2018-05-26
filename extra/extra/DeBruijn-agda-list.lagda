The typed DeBruijn representation is well known, as are typed PHOAS
and untyped DeBruijn.  It is easy to convert PHOAS to untyped
DeBruijn.  Is it known how to convert PHOAS to typed DeBruijn?

Yours, -- P


## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
\end{code}

## Typed DeBruijn

\begin{code}
infixr 4 _⇒_

data Type : Set where
  o : Type
  _⇒_ : Type → Type → Type

data Env : Set where
  ε : Env
  _,_ : Env → Type → Env

data Var : Env → Type → Set where
  Z : ∀ {Γ : Env} {A : Type} → Var (Γ , A) A
  S : ∀ {Γ : Env} {A B : Type} → Var Γ B → Var (Γ , A) B

data Exp : Env → Type → Set where
  var : ∀ {Γ : Env} {A : Type} → Var Γ A → Exp Γ A
  abs : ∀ {Γ : Env} {A B : Type} → Exp (Γ , A) B → Exp Γ (A ⇒ B)
  app : ∀ {Γ : Env} {A B : Type} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B
\end{code}

## Untyped DeBruijn

\begin{code}
data DB : Set where
  var : ℕ → DB
  abs : DB → DB
  app : DB → DB → DB
\end{code}

# PHOAS

\begin{code}
data PH (X : Type → Set) : Type → Set where
  var : ∀ {A : Type} → X A → PH X A
  abs : ∀ {A B : Type} → (X A → PH X B) → PH X (A ⇒ B)
  app : ∀ {A B : Type} → PH X (A ⇒ B) → PH X A → PH X B
\end{code}

# Convert PHOAS to DB

\begin{code}
PH→DB : ∀ {A} → (∀ {X} → PH X A) → DB
PH→DB M = h M 0
  where
  K : Type → Set
  K A = ℕ

  h : ∀ {A} → PH K A → ℕ → DB
  h (var k) j    =  var (j ∸ k)
  h (abs N) j    =  abs (h (N (j + 1)) (j + 1))
  h (app L M) j  =  app (h L j) (h M j)
\end{code}

# Test examples

\begin{code}
Church : Type
Church = (o ⇒ o) ⇒ o ⇒ o

twoExp : Exp ε Church
twoExp = (abs (abs (app (var (S Z)) (app (var (S Z)) (var Z)))))

twoPH : ∀ {X} → PH X Church
twoPH = (abs (λ f → (abs (λ x → (app (var f) (app (var f) (var x)))))))

twoDB : DB
twoDB = (abs (abs (app (var 1) (app (var 1) (var 0)))))

ex : PH→DB twoPH ≡ twoDB
ex = refl
\end{code}

