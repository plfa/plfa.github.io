module TakeDropDec where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.All using (All; []; _∷_)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using ()
open import Function using (_∘_)

module TakeDrop {A : Set} {P : A → Set} (P? : ∀ (x : A) → Dec (P x)) where

  takeWhile : List A → List A
  takeWhile []                   =  []
  takeWhile (x ∷ xs) with P? x
  ...                   | yes _  =  x ∷ takeWhile xs
  ...                   | no  _  =  []

  dropWhile : List A → List A
  dropWhile []                   =  []
  dropWhile (x ∷ xs) with P? x
  ...                   | yes _  =  dropWhile xs
  ...                   | no  _  =  x ∷ xs

  Head : (A → Set) → List A → Set
  Head P []        =  ⊥
  Head P (x ∷ xs)  =  P x

  takeWhile-lemma : ∀ (xs : List A) → All P (takeWhile xs)
  takeWhile-lemma []                    =  []
  takeWhile-lemma (x ∷ xs) with P? x
  ...                         | yes px  =  px ∷ takeWhile-lemma xs
  ...                         | no  _   =  []

  dropWhile-lemma : ∀ (xs : List A) → ¬ Head P (dropWhile xs)
  dropWhile-lemma []                     =  λ()
  dropWhile-lemma (x ∷ xs) with P? x
  ...                         | yes _    =  dropWhile-lemma xs
  ...                         | no  ¬px  =  ¬px

open TakeDrop
open import Data.Nat using (ℕ; zero; suc; _≟_)

_ : takeWhile (0 ≟_) (0 ∷ 0 ∷ 1 ∷ []) ≡ (0 ∷ 0 ∷ [])
_ = refl

_ : dropWhile (0 ≟_) (0 ∷ 0 ∷ 1 ∷ []) ≡ (1 ∷ [])
_ = refl
