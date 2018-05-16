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

module TakeDropDec {A : Set} {P : A → Set} where

Decidable : (A → Set) → Set
Decidable P = ∀ (x : A) → Dec (P x)

takeWhile : Decidable P → List A → List A
takeWhile P? []                   =  []
takeWhile P? (x ∷ xs) with P? x
...                      | yes _  =  x ∷ takeWhile P? xs
...                      | no  _  =  []

dropWhile : Decidable P → List A → List A
dropWhile P? []                   =  []
dropWhile P? (x ∷ xs) with P? x
...                      | yes _  =  dropWhile P? xs
...                      | no  _  =  x ∷ xs

Head : (A → Set) → List A → Set
Head P []        =  ⊥
Head P (x ∷ xs)  =  P x

takeWhile-lemma : ∀ (P? : Decidable P) (xs : List A) → All P (takeWhile P? xs)
takeWhile-lemma P? []                    =  []
takeWhile-lemma P? (x ∷ xs) with P? x
...                            | yes px  =  px ∷ takeWhile-lemma P? xs
...                            | no  _   =  []

dropWhile-lemma : ∀ (P? : Decidable P) (xs : List A) → ¬ Head P (dropWhile P? xs)
dropWhile-lemma P? []                     =  λ()
dropWhile-lemma P? (x ∷ xs) with P? x
...                            | yes _    =  dropWhile-lemma P? xs
...                            | no  ¬px  =  ¬px
