Many thanks to Nils and Roman.

Attached find an implementation along the lines sketched by Roman;
I found it after I sent my request and before Roman sent his helpful
reply.

One thing I note, in both Roman's code and mine, is that the code to
decide whether two contexts are equal is lengthy (_≟T_ and _≟_,
below).  Is there a better way to do it?  Does Agda offer an
equivalent of Haskell's derivable for equality?

Cheers, -- P

[Version using Ulf's prelude to derive equality]

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
\end{code}

## Typed DeBruijn

\begin{code}
infixr 5 _⇒_

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
  h (var k) j    =  var (j ∸ (k + 1))
  h (abs N) j    =  abs (h (N j) (j + 1))
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

## Decide whether environments and types are equal

\begin{code}
-- These two imports are from agda-prelude (https://github.com/UlfNorell/agda-prelude)
open import Tactic.Deriving.Eq using (deriveEq)
import Prelude

instance
  unquoteDecl EqType = deriveEq EqType (quote Type)
  unquoteDecl EqEnv  = deriveEq EqEnv  (quote Env)

⊥To⊥ : Prelude.⊥ → ⊥
⊥To⊥ ()

decToDec : ∀ {a} {A : Set a} → Prelude.Dec A → Dec A
decToDec (Prelude.yes x) = yes x
decToDec (Prelude.no nx) = no (⊥To⊥ ∘ nx)

_≟T_ : ∀ (A B : Type) → Dec (A ≡ B)
A ≟T B = decToDec (A Prelude.== B)

_≟_ : ∀ (Γ Δ : Env) → Dec (Γ ≡ Δ)
Γ ≟ Δ = decToDec (Γ Prelude.== Δ)
\end{code}

[Old version, no longer needed]

_≟T_ : ∀ (A B : Type) → Dec (A ≡ B)
o ≟T o = yes refl
o ≟T (A′ ⇒ B′) = no (λ())
(A ⇒ B) ≟T o = no (λ())
(A ⇒ B) ≟T (A′ ⇒ B′) = map (equivalence obv1 obv2) ((A ≟T A′) ×-dec (B ≟T B′))
  where
  obv1 : ∀ {A B A′ B′ : Type} → (A ≡ A′) × (B ≡ B′) → A ⇒ B ≡ A′ ⇒ B′
  obv1 ⟨ refl , refl ⟩ = refl
  obv2 : ∀ {A B A′ B′ : Type} → A ⇒ B ≡ A′ ⇒ B′ → (A ≡ A′) × (B ≡ B′)
  obv2 refl = ⟨ refl , refl ⟩

_≟_ : ∀ (Γ Δ : Env) → Dec (Γ ≡ Δ)
ε ≟ ε = yes refl
ε ≟ (Γ , A) = no (λ())
(Γ , A) ≟ ε = no (λ())
(Γ , A) ≟ (Δ , B) = map (equivalence obv1 obv2) ((Γ ≟ Δ) ×-dec (A ≟T B))
  where
  obv1 : ∀ {Γ Δ A B} → (Γ ≡ Δ) × (A ≡ B) → (Γ , A) ≡ (Δ , B)
  obv1 ⟨ refl , refl ⟩ = refl
  obv2 : ∀ {Γ Δ A B} → (Γ , A) ≡ (Δ , B) → (Γ ≡ Δ) × (A ≡ B)
  obv2 refl = ⟨ refl , refl ⟩

## Convert Phoas to Exp

\begin{code}
compare : ∀ (A : Type) (Γ Δ : Env) → Var Δ A
compare A Γ Δ    with (Γ , A) ≟ Δ
compare A Γ Δ       | yes refl = Z
compare A Γ (Δ , B) | no _     = S (compare A Γ Δ)
compare A Γ ε       | no _     = impossible
  where
    postulate
      impossible : ∀ {A : Set} → A

PH→Exp : ∀ {A : Type} → (∀ {X} → PH X A) → Exp ε A
PH→Exp M = h M ε
  where
  K : Type → Set
  K A = Env

  h : ∀ {A} → PH K A → (Δ : Env) → Exp Δ A
  h {A} (var Γ) Δ = var (compare A Γ Δ)
  h {A ⇒ B} (abs N) Δ = abs (h (N Δ) (Δ , A))
  h (app L M) Δ = app (h L Δ) (h M Δ)

ex₁ : PH→Exp twoPH ≡ twoExp
ex₁ = refl
\end{code}

## When one environment extends another

We could get rid of the use of `impossible` above if we could prove
that `Extends (Γ , A) Δ` in the `(var Γ)` case of the definition of `h`.

\begin{code}
data Extends : (Γ : Env) → (Δ : Env) → Set where
  Z : ∀ {Γ : Env} → Extends Γ Γ
  S : ∀ {A : Type} {Γ Δ : Env} → Extends Γ Δ → Extends Γ (Δ , A)

extract : ∀ {A : Type} {Γ Δ : Env} → Extends (Γ , A) Δ → Var Δ A
extract Z     = Z
extract (S k) = S (extract k)
\end{code}



