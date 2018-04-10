---
title     : "TypedDB: Typed DeBruijn representation"
layout    : page
permalink : /Scoped
---

## Imports

\begin{code}
module TypedDB where
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
infixl 6 _,_
infix  4 _⊢_
infix  4 _∋_
infixr 5 _⇒_
infixl 5 _·_
infix  6 S_
infix  4 ƛ_

data Type : Set where
  o   : Type
  _⇒_ : Type → Type → Type

data Env : Set where
  ε   : Env
  _,_ : Env → Type → Env

data _∋_ : Env → Type → Set where

  Z : ∀ {Γ} {A} →
    ------------
    Γ , A ∋ A

  S_ : ∀ {Γ} {A B} →
    Γ ∋ A →
    -----------
    Γ , B ∋ A

data _⊢_ : Env → Type → Set where

  ⌊_⌋ : ∀ {Γ} {A} →
    Γ ∋ A →
    -------
    Γ ⊢ A

  ƛ_  :  ∀ {Γ} {A B} →
    Γ , A ⊢ B →
    ------------
    Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ} {A B} →
    Γ ⊢ A ⇒ B →
    Γ ⊢ A →
    ------------
    Γ ⊢ B
\end{code}

## Writing variables as naturals

\begin{code}
postulate
  impossible : ⊥
  _≟Tp_ : ∀ (A B : Type) → Dec (A ≡ B)

conv : ∀ {Γ} {A} → ℕ → Γ ∋ A
conv {ε} = ⊥-elim impossible
conv {Γ , B} (suc n) = S (conv n)
conv {Γ , A} {B} zero with A ≟Tp B
...                   | yes refl  =  Z
...                   | no  A≢B   =  ⊥-elim impossible

⌈_⌉ : ∀ {Γ} {A} → ℕ → Γ ⊢ A
⌈ n ⌉  =  ⌊ conv n ⌋
\end{code}

## Test examples

\begin{code}
Ch : Type
Ch = (o ⇒ o) ⇒ o ⇒ o

plus : ∀ {Γ} → Γ ⊢ Ch ⇒ Ch ⇒ Ch
plus = ƛ ƛ ƛ ƛ (⌊ S S S Z ⌋ · ⌊ S Z ⌋ · (⌊ S S Z ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋))

two : ∀ {Γ} → Γ ⊢ Ch
two = ƛ ƛ (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))

four : ∀ {Γ} → Γ ⊢ Ch
four = ƛ ƛ (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))))

four′ : ∀ {Γ} → Γ ⊢ Ch
four′ = plus · two · two
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


# Denotational semantics

\begin{code}
⟦_⟧ᵀ : Type → Set
⟦ o ⟧ᵀ      =  ℕ
⟦ A ⇒ B ⟧ᵀ  =  ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ

⟦_⟧ᴱ : Env → Set
⟦ ε ⟧ᴱ      =  ⊤
⟦ Γ , A ⟧ᴱ  =  ⟦ Γ ⟧ᴱ × ⟦ A ⟧ᵀ

⟦_⟧ⱽ : ∀ {Γ : Env} {A : Type} → Γ ∋ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ Z ⟧ⱽ   ⟨ ρ , v ⟩ = v
⟦ S n ⟧ⱽ ⟨ ρ , v ⟩ = ⟦ n ⟧ⱽ ρ

⟦_⟧ : ∀ {Γ : Env} {A : Type} → Γ ⊢ A → ⟦ Γ ⟧ᴱ → ⟦ A ⟧ᵀ
⟦ ⌊ n ⌋ ⟧ ρ  =  ⟦ n ⟧ⱽ ρ
⟦ ƛ N   ⟧ ρ  =  λ{ v → ⟦ N ⟧ ⟨ ρ , v ⟩ }
⟦ L · M ⟧ ρ  =  (⟦ L ⟧ ρ) (⟦ M ⟧ ρ)

_ : ⟦ four ⟧ tt ≡ ⟦ four′ ⟧ tt
_ = refl

_ : ⟦ four ⟧ tt suc zero ≡ 4
_ = refl
\end{code}

## Operational semantics - with simultaneous substitution, a la McBride

## Renaming

\begin{code}
ext∋ : ∀ {Γ Δ} {B} → (∀ {A} → Γ ∋ A → Δ ∋ A) → Δ ∋ B → (∀ {A} → Γ , B ∋ A → Δ ∋ A)
ext∋ ρ j Z      =  j
ext∋ ρ j (S k)  =  ρ k

rename : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A) → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (⌊ n ⌋)  =  ⌊ ρ n ⌋
rename ρ (ƛ N)    =  ƛ (rename (ext∋ (S_ ∘ ρ) Z) N)
rename ρ (L · M)  =  (rename ρ L) · (rename ρ M)
\end{code}

## Substitution

\begin{code}
ext⊢ : ∀ {Γ Δ} {B} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → Δ ⊢ B → (∀ {A} → Γ , B ∋ A → Δ ⊢ A)
ext⊢ ρ M Z      =  M
ext⊢ ρ M (S k)  =  ρ k

subst : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst ρ (⌊ n ⌋)  =  ρ n
subst ρ (ƛ N)    =  ƛ (subst (ext⊢ (rename S_ ∘ ρ) ⌊ Z ⌋) N)
subst ρ (L · M)  =  (subst ρ L) · (subst ρ M)

substitute : ∀ {Γ} {A B} → Γ , A ⊢ B → Γ ⊢ A → Γ ⊢ B
substitute N M =  subst (ext⊢ ⌊_⌋ M) N 
\end{code}

## Normal

\begin{code}
data Normal : ∀ {Γ} {A} → Γ ⊢ A → Set
data Neutral : ∀ {Γ} {A} → Γ ⊢ A → Set

data Normal where
  Fun : ∀ {Γ} {A B} {N : Γ , A ⊢ B} → Normal N → Normal (ƛ N)
  Neu : ∀ {Γ} {A} {M : Γ ⊢ A} → Neutral M → Normal M

data Neutral where
  Var : ∀ {Γ} {A} → {n : Γ ∋ A} → Neutral ⌊ n ⌋
  App : ∀ {Γ} {A B} → {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} → Neutral L → Normal M → Neutral (L · M)
\end{code}

## Reduction step

\begin{code}
infix  2 _⟶_

data _⟶_ : ∀ {Γ} {A} → Γ ⊢ A → Γ ⊢ A → Set where

  ξ₁ : ∀ {Γ} {A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} →
    L ⟶ L′ →
    -----------------
    L · M ⟶ L′ · M

  ξ₂ : ∀ {Γ} {A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A} →
    Normal V →
    M ⟶ M′ →
    ----------------
    V · M ⟶ V · M′

  ζ : ∀ {Γ} {A B} {N N′ : Γ , A ⊢ B} →
    N ⟶ N′ →
    ------------
    ƛ N ⟶ ƛ N′

  β : ∀ {Γ} {A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A} → 
    Normal W →
    ----------------------------
    (ƛ N) · W ⟶ substitute N W
\end{code}

## Reflexive and transitive closure

\begin{code}
infix  2 _⟶*_

data _⟶*_ : ∀ {Γ} {A} → Γ ⊢ A → Γ ⊢ A → Set where

  reflexive : ∀ {Γ} {A} {M : Γ ⊢ A} →
    --------
    M ⟶* M

  inclusion : ∀ {Γ} {A} {M N : Γ ⊢ A} →
    M ⟶ N →
    ---------
    M ⟶* N

  transitive : ∀ {Γ} {A} {L M N : Γ ⊢ A} →
    L ⟶* M →
    M ⟶* N →
    ----------
    L ⟶* N
\end{code}

## Displaying reduction sequences

\begin{code}
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3 _∎

begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A} → (M ⟶* N) → (M ⟶* N)
begin M⟶*N = M⟶*N

_⟶⟨_⟩_ : ∀ {Γ} {A} (L : Γ ⊢ A) {M N : Γ ⊢ A} → (L ⟶ M) → (M ⟶* N) → (L ⟶* N)
L ⟶⟨ L⟶M ⟩ M⟶*N = transitive (inclusion L⟶M) M⟶*N

_∎ : ∀ {Γ} {A} (M : Γ ⊢ A) → M ⟶* M
M ∎ = reflexive
\end{code}

## Example reduction sequence

\begin{code}
id : ∀ (A : Type) → ε ⊢ A ⇒ A
id A = ƛ ⌊ Z ⌋

_ : id (o ⇒ o) · id o  ⟶* id o
_ =
  begin
    id (o ⇒ o) · id o
  ⟶⟨ β (Fun (Neu Var)) ⟩
    id o
  ∎

Nmplus : Normal (plus {ε})
Nmplus = Fun (Fun (Fun (Fun (Neu (App (App Var (Neu Var)) (Neu (App (App Var (Neu Var)) (Neu Var))))))))

Nmtwo : Normal (two {ε})
Nmtwo =  Fun (Fun (Neu (App Var (Neu (App Var (Neu Var))))))

_ : four′ {ε} ⟶* four {ε}
_ =
  begin
    plus · two · two
  ⟶⟨ ξ₁ (β Nmtwo) ⟩
    (ƛ ƛ ƛ (two · ⌊ S Z ⌋ · (⌊ S S Z ⌋ · ⌊ S Z ⌋ · ⌊ Z ⌋))) · two
  ⟶⟨ β Nmtwo ⟩
    (ƛ ƛ (two · ⌊ S Z ⌋ · (two · ⌊ S Z ⌋ · ⌊ Z ⌋)))
  ⟶⟨ ζ (ζ (ξ₁ (β (Neu Var)))) ⟩
    (ƛ ƛ ((ƛ (⌊ S S Z ⌋ · (⌊ S S Z ⌋ · ⌊ Z ⌋))) · (two · ⌊ S Z ⌋ · ⌊ Z ⌋)))
  ⟶⟨ ζ (ζ (ξ₂ (Fun (Neu (App Var (Neu (App Var (Neu Var)))))) (ξ₁ (β (Neu Var))))) ⟩
    (ƛ ƛ ((ƛ (⌊ S S Z ⌋ · (⌊ S S Z ⌋ · ⌊ Z ⌋))) · ((ƛ (⌊ S S Z ⌋ · (⌊ S S Z ⌋ · ⌊ Z ⌋))) · ⌊ Z ⌋)))
  ⟶⟨ ζ (ζ (ξ₂ (Fun (Neu (App Var (Neu (App Var (Neu Var)))))) (β (Neu Var)))) ⟩
    (ƛ ƛ ((ƛ (⌊ S S Z ⌋ · (⌊ S S Z ⌋ · ⌊ Z ⌋))) · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋))))
  ⟶⟨ ζ (ζ (β (Neu (App Var (Neu (App Var (Neu Var))))))) ⟩
    (ƛ ƛ (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · (⌊ S Z ⌋ · ⌊ Z ⌋)))))
  ∎
\end{code}

## Progress

\begin{code}
progress : ∀ {Γ} {A} → (M : Γ ⊢ A) → (∃[ N ] (M ⟶ N)) ⊎ Normal M
progress ⌊ x ⌋                                                  =  inj₂ (Neu Var)
progress (ƛ N)       with progress N
progress (ƛ N)          | inj₁ ⟨ N′ , r ⟩                       =  inj₁ ⟨ ƛ N′ , ζ r ⟩
progress (ƛ V)          | inj₂ NmV                              =  inj₂ (Fun NmV)
progress (L · M)     with progress L
progress (L · M)        | inj₁ ⟨ L′ , r ⟩                       =  inj₁ ⟨ L′ · M , ξ₁ r ⟩
progress (V · M)        | inj₂ NmV     with progress M
progress (V · M)        | inj₂ NmV        | inj₁ ⟨ M′ , r ⟩     =  inj₁ ⟨ V · M′ , ξ₂ NmV r ⟩
progress (V · W)        | inj₂ (Neu NeV)  | inj₂ NmW            =  inj₂ (Neu (App NeV NmW))
progress ((ƛ V) · W)    | inj₂ (Fun NmV)  | inj₂ NmW            =  inj₁ ⟨ substitute V W , β NmW ⟩
\end{code}


\begin{code}
{-
ex₃ : progress (app (app plus one) one) ≡
  inj₁ ⟨ (app (abs (abs (abs (app (app Γone (var (S Z))) (app (app (var (S (S Z))) (var (S Z))) (var Z)))))) Γone) , ξ₁ (β Fun) ⟩
ex₃ = refl

ex₄ : progress (app (abs (abs (abs (app (app Γone (var (S Z))) (app (app (var (S (S Z))) (var (S Z))) (var Z)))))) Γone) ≡
  inj₁ ⟨ (abs (abs (app (app Γone (var (S Z))) (app (app Γone (var (S Z))) (var Z))))) , β Fun ⟩
ex₄ = refl

ex₅ : progress (abs (abs (app (app Γone (var (S Z))) (app (app Γone (var (S Z))) (var Z))))) ≡ inj₂ Fun
ex₅ = refl  

-}
\end{code}
