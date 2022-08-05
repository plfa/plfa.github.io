## Subset

\begin{code}
open import Data.List using (List; []; _∷_)
open import Function using (id; _∘_)
open import Relation.Binary.Core using (Reflexive; Transitive)

module Subset (A : Set) where

  infix 4 _⊆_
  infix 4 _∈_

  data _∈_ : A → List A → Set where

    here : ∀ {x : A} {xs : List A}
        ----------
      → x ∈ x ∷ xs

    there : ∀ {x y : A} {xs : List A}
      → x ∈ xs
        ----------
      → x ∈ y ∷ xs

  _⊆_ : List A → List A → Set
  xs ⊆ ys  =  ∀ {w : A} → w ∈ xs → w ∈ ys

  ⊆-refl : Reflexive _⊆_
  ⊆-refl  =  id

  ⊆-trans : Transitive _⊆_
  ⊆-trans xs⊆ys ys⊆zs  =  ys⊆zs ∘ xs⊆ys
\end{code}
