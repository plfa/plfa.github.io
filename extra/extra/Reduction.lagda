Old version of reduction

## Imports

\begin{code}
open import Maps using (Id; id; _≟_; PartialMap; module PartialMap)
open PartialMap using (∅) renaming (_,_↦_ to _,_∶_)
-- open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Stlc hiding (_⟹*_; _⟹⟨_⟩_; _∎; reduction₁; reduction₂)
\end{code}

## Reflexive and transitive closure

\begin{code}
Rel : Set → Set₁
Rel A = A → A → Set

infixl 10 _>>_

data _* {A : Set} (R : Rel A) : Rel A where
  ⟨⟩ : ∀ {x : A} → (R *) x x
  ⟨_⟩ : ∀ {x y : A} → R x y → (R *) x y
  _>>_ : ∀ {x y z : A} → (R *) x y → (R *) y z → (R *) x z

infix 10 _⟹*_

_⟹*_ : Rel Term
_⟹*_ = (_⟹_) *
\end{code}

## Notation for setting out reductions

\begin{code}
infixr 2 _⟹⟨_⟩_
infix  3 _∎

_⟹⟨_⟩_ : ∀ L {M N} → L ⟹ M → M ⟹* N → L ⟹* N
L ⟹⟨ L⟹M ⟩ M⟹*N  =  ⟨ L⟹M ⟩ >> M⟹*N

_∎ : ∀ M → M ⟹* M
M ∎  =  ⟨⟩
\end{code}

## Example reduction derivations

\begin{code}
reduction₁ : not · true ⟹* false
reduction₁ =
    not · true
  ⟹⟨ β⇒ value-true ⟩
    if true then false else true
  ⟹⟨ β𝔹₁  ⟩
    false
  ∎

reduction₂ : two · not · true ⟹* true
reduction₂ =
    two · not · true
  ⟹⟨ γ⇒₁ (β⇒ value-λ) ⟩
    (λ[ x ∶ 𝔹 ] not · (not · var x)) · true
  ⟹⟨ β⇒ value-true ⟩
    not · (not · true)
  ⟹⟨ γ⇒₂ value-λ (β⇒ value-true) ⟩
    not · (if true then false else true)
  ⟹⟨ γ⇒₂ value-λ β𝔹₁ ⟩
    not · false
  ⟹⟨ β⇒ value-false ⟩
    if false then false else true
  ⟹⟨ β𝔹₂ ⟩
    true
  ∎
\end{code}
