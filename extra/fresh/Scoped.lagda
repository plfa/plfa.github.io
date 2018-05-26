---
title     : "Scoped: Scoped and Typed DeBruijn representation"
layout    : page
permalink : /Scoped
---

## Imports

\begin{code}
module Scoped where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
-- open Eq.≡-Reasoning
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

## Syntax

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


# PH representation

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

## Decide whether environments and types are equal

\begin{code}
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
\end{code}


## Convert Phoas to Exp

\begin{code}
postulate
  impossible : ∀ {A : Set} → A

compare : ∀ (A : Type) (Γ Δ : Env) → Var Δ A   -- Extends (Γ , A) Δ
compare A Γ Δ with (Γ , A) ≟ Δ
compare A Γ Δ       | yes refl = Z
compare A Γ (Δ , B) | no ΓA≠ΔB = S (compare A Γ Δ)
compare A Γ ε       | no ΓA≠ΔB = impossible

PH→Exp : ∀ {A : Type} → (∀ {X} → PH X A) → Exp ε A
PH→Exp M = h M ε
  where
  K : Type → Set
  K A = Env

  h : ∀ {A} → PH K A → (Δ : Env) → Exp Δ A
  h {A} (var Γ) Δ = var (compare A Γ Δ)
  h {A ⇒ B} (abs N) Δ = abs (h (N Δ) (Δ , A))
  h (app L M) Δ = app (h L Δ) (h M Δ)

exPH : PH→Exp twoPH ≡ twoExp
exPH = refl
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

# Test code for semantics

\begin{code}
plus : Exp ε (Church ⇒ Church ⇒ Church)
plus = PH→Exp (abs λ{m → (abs λ{n → (abs λ{s → (abs λ{z →
  (app (app (var m) (var s)) (app (app (var n) (var s)) (var z)))})})})})

one : Exp ε Church
one =  PH→Exp (abs λ{s → (abs λ{z → (app (var s) (var z))})})

two : Exp ε Church
two = (app (app plus one) one)

four : Exp ε Church
four = (app (app plus two) two)
\end{code}


# Denotational semantics

\begin{code}
type : Type → Set
type o = ℕ
type (A ⇒ B) = type A → type B

env : Env → Set
env ε = ⊤
env (Γ , A) = env Γ × type A

lookup : ∀ {Γ : Env} {A : Type} → Var Γ A → env Γ → type A
lookup Z ⟨ ρ , v ⟩ = v
lookup (S n) ⟨ ρ , v ⟩ = lookup n ρ

eval : ∀ {Γ : Env} {A : Type} → Exp Γ A → env Γ → type A
eval (var n) ρ  =  lookup n ρ
eval (abs N) ρ  =  λ{ v → eval N ⟨ ρ , v ⟩ }
eval (app L M) ρ  =  eval L ρ (eval M ρ)

ex₀ : eval four tt suc zero ≡ 4
ex₀ = refl
\end{code}

# Operational semantics - with substitution a la Darais (31 lines)

## Remove variable from environment (4 lines)

\begin{code}
infix 4 _⊝_
_⊝_ : ∀ {A : Type} (Γ : Env) → Var Γ A → Env
(Γ , B) ⊝ Z = Γ
(Γ , B) ⊝ S k = (Γ ⊝ k) , B
\end{code}

## Rebuild environment (6 lines)

\begin{code}
shunt : ∀ (Γ Δ : Env) → Env
shunt Γ ε = Γ
shunt Γ (Δ , A) = shunt (Γ , A) Δ

weaken : ∀ (Γ Δ : Env) {A : Type} (k : Var Γ A) → Var (shunt Γ Δ) A
weaken Γ ε k = k
weaken Γ (Δ , A) k = weaken (Γ , A) Δ (S k)
\end{code}

## Lift term to a larger environment (8 lines)

\begin{code}
liftvar : ∀ {Γ : Env} {A B : Type} (j : Var Γ B) (k : Var (Γ ⊝ j) A) → Var Γ A
liftvar Z k = S k
liftvar (S j) Z = Z
liftvar (S j) (S k) = S (liftvar j k)

lift : ∀ {Γ : Env} {A B : Type} (j : Var Γ B) (M : Exp (Γ ⊝ j) A) → Exp Γ A
lift j (var k)    =  var (liftvar j k)
lift j (abs N)    =  abs (lift (S j) N)
lift j (app L M)  =  app (lift j L) (lift j M)
\end{code}

## Substitution (13 lines)

\begin{code}
substvar : ∀ (Γ Δ : Env) {A B : Type} (j : Var Γ B) (k : Var Γ A) (P : Exp (shunt (Γ ⊝ k) Δ) A) → Exp (shunt (Γ ⊝ k) Δ) B
substvar Γ Δ Z Z P = P
substvar (Γ , A) Δ Z (S k) P = var (weaken ((Γ ⊝ k) , A) Δ Z)
substvar (Γ , A) Δ (S j) Z P = var (weaken Γ Δ j)
substvar (Γ , A) Δ (S j) (S k) P = substvar Γ (Δ , A) j k P

subst : ∀ {Γ : Env} {A B : Type} (N : Exp Γ B) (k : Var Γ A) (M : Exp (Γ ⊝ k) A) → Exp (Γ ⊝ k) B
subst {Γ} (var j) k P = substvar Γ ε j k P
subst (abs N) k P =  abs (subst N (S k) (lift Z P))
subst (app L M) k P =  app (subst L k P) (subst M k P)
\end{code}

# Operational semantics - with simultaneous substitution, a la McBride (18 lines)

## Renaming (7 lines)

\begin{code}
extend : ∀ {Γ Δ : Env} {B : Type} → (∀ {A : Type} → Var Γ A → Var Δ A) → Var Δ B → (∀ {A : Type} → Var (Γ , B) A → Var Δ A)
extend ρ j Z      =  j
extend ρ j (S k)  =  ρ k

rename : ∀ {Γ Δ : Env} → (∀ {A : Type} → Var Γ A → Var Δ A) → (∀ {A : Type} → Exp Γ A → Exp Δ A)
rename ρ (var n)    =  var (ρ n)
rename ρ (abs N)    =  abs (rename (extend (S ∘ ρ) Z) N)
rename ρ (app L M)  =  app (rename ρ L) (rename ρ M)
\end{code}

## Substitution (9 lines)

\begin{code}
ext :  ∀ {Γ Δ : Env} {B : Type} → (∀ {A : Type} → Var Γ A → Exp Δ A) → Exp Δ B → (∀ {A : Type} → Var (Γ , B) A → Exp Δ A)
ext ρ j Z      =  j
ext ρ j (S k)  =  ρ k

sub : ∀ {Γ Δ : Env} → (∀ {A : Type} → Var Γ A → Exp Δ A) → (∀ {A : Type} → Exp Γ A → Exp Δ A)
sub ρ (var n)    =  ρ n
sub ρ (app L M)  =  app (sub ρ L) (sub ρ M)
sub ρ (abs N)    =  abs (sub (ext (rename S ∘ ρ) (var Z)) N)

substitute : ∀ {Γ : Env} {A B : Type} → Exp (Γ , A) B → Exp Γ A → Exp Γ B
substitute N M =  sub (ext var M) N 
\end{code}

## Value

\begin{code}
data Val : {Γ : Env} {A : Type} → Exp Γ A → Set where
  Fun : ∀ {Γ : Env} {A B : Type} {N : Exp (Γ , A) B} →
    Val (abs N)
\end{code}

## Reduction step

\begin{code}
data _⟶_ : {Γ : Env} {A : Type} → Exp Γ A → Exp Γ A → Set where
  ξ₁ : ∀ {Γ : Env} {A B : Type} {L : Exp Γ (A ⇒ B)} {L′ : Exp Γ (A ⇒ B)} {M : Exp Γ A} →
     L ⟶ L′ →
     app L M ⟶ app L′ M
  ξ₂ : ∀ {Γ : Env} {A B : Type} {L : Exp Γ (A ⇒ B)} {M : Exp Γ A} {M′ : Exp Γ A} →
     Val L →
     M ⟶ M′ →
     app L M ⟶ app L M′
  β : ∀ {Γ : Env} {A B : Type} {N : Exp (Γ , A) B} {M : Exp Γ A} → 
    Val M → 
    app (abs N) M ⟶ substitute N M
\end{code}

## Reflexive and transitive closure

\begin{code}
data _⟶*_ : {Γ : Env} {A : Type} → Exp Γ A → Exp Γ A → Set where
  reflexive : ∀ {Γ : Env} {A : Type} {M : Exp Γ A} →
    M ⟶* M
  inclusion : ∀ {Γ : Env} {A : Type} {L M : Exp Γ A} →
    L ⟶ M →
    L ⟶* M
  transitive : ∀ {Γ : Env} {A : Type} {L M N : Exp Γ A} →
    L ⟶* M →
    M ⟶* N →
    L ⟶* N
\end{code}

## Displaying reduction sequences

\begin{code}
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3 _∎

begin_ : {Γ : Env} {A : Type} {M N : Exp Γ A} → (M ⟶* N) → (M ⟶* N)
begin steps = steps

_⟶⟨_⟩_ : {Γ : Env} {A : Type} (L : Exp Γ A) {M N : Exp Γ A} → (L ⟶ M) → (M ⟶* N) → (L ⟶* N)
L ⟶⟨ L⟶M ⟩ M⟶*N = transitive (inclusion L⟶M) M⟶*N

_∎ : {Γ : Env} {A : Type} (M : Exp Γ A) → M ⟶* M
M ∎ = reflexive
\end{code}

## Example reduction sequence

\begin{code}
ex₁ : (app (abs (var Z)) (abs (var Z))) ⟶* (abs (var Z))
ex₁ =
  begin
    (app (abs {Γ = ε} {A = o ⇒ o} (var Z)) (abs (var Z)))
  ⟶⟨ β Fun ⟩
    (abs (var Z))
  ∎
\end{code}

\begin{code}
Γone : ∀ {Γ} → Exp Γ Church
Γone = (abs (abs (app (var (S Z)) (var Z))))

ex₂ : two ⟶* (abs (abs (app (app Γone (var (S Z))) (app (app Γone (var (S Z))) (var Z)))))
ex₂ =
  begin
    (app (app plus one) one)
  ⟶⟨ ξ₁ (β Fun) ⟩
    (app (abs (abs (abs (app (app Γone (var (S Z))) (app (app (var (S (S Z))) (var (S Z))) (var Z)))))) Γone)
  ⟶⟨ β Fun ⟩
    (abs (abs (app (app Γone (var (S Z))) (app (app Γone (var (S Z))) (var Z)))))
  ∎
\end{code}

\begin{code}
progress : ∀ {A : Type} → (M : Exp ε A) → (∃[ N ] (M ⟶ N)) ⊎ Val M
progress (var ())
progress (abs N)                                            = inj₂  Fun
progress (app L M)    with progress L
progress (app L M)       | inj₁ ⟨ L′ , r ⟩                  =  inj₁ ⟨ app L′ M , ξ₁ r ⟩
progress (app (abs N) M) | inj₂ Fun  with progress M
progress (app (abs N) M) | inj₂ Fun     | inj₁ ⟨ M′ , r ⟩   =  inj₁ ⟨ app (abs N) M′ , ξ₂ Fun r ⟩
progress (app (abs N) M) | inj₂ Fun     | inj₂ ValM         =  inj₁ ⟨ substitute N M , β ValM ⟩
\end{code}


\begin{code}
ex₃ : progress (app (app plus one) one) ≡
  inj₁ ⟨ (app (abs (abs (abs (app (app Γone (var (S Z))) (app (app (var (S (S Z))) (var (S Z))) (var Z)))))) Γone) , ξ₁ (β Fun) ⟩
ex₃ = refl

ex₄ : progress (app (abs (abs (abs (app (app Γone (var (S Z))) (app (app (var (S (S Z))) (var (S Z))) (var Z)))))) Γone) ≡
  inj₁ ⟨ (abs (abs (app (app Γone (var (S Z))) (app (app Γone (var (S Z))) (var Z))))) , β Fun ⟩
ex₄ = refl

ex₅ : progress (abs (abs (app (app Γone (var (S Z))) (app (app Γone (var (S Z))) (var Z))))) ≡ inj₂ Fun
ex₅ = refl  
\end{code}
