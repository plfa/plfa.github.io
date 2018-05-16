import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; takeWhile; dropWhile)
open import Data.List.All using (All; []; _∷_)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)

module TakeDropLemmas (A : Set) (P : A → Bool) where

  Head : ∀ {A : Set} → (A → Bool) → List A → Set
  Head P []       =  ⊥
  Head P (c ∷ s)  =  T (P c)

  drop-lemma : ∀ (s : List A) → ¬ Head P (dropWhile P s)
  drop-lemma [] = λ()
  drop-lemma (c ∷ s) with P c
  ...  | true   =  drop-lemma s
  ...  | false  =  {!!}

  take-lemma : ∀ (s : List A) → All (T ∘ P) (takeWhile P s)
  take-lemma [] = []
  take-lemma (c ∷ s) with P c
  ...  | true   =  {!!} ∷ take-lemma s
  ...  | false  =  []

{-  Hole 0
Goal: ⊥
————————————————————————————————————————————————————————————
s  : List A
c  : A
eq : T (P c)
P  : A → Bool
s  : List A
c  : A
A  : Set
-}

{- Hole 1
Goal: T (P c)
————————————————————————————————————————————————————————————
s : List A
c : A
P : A → Bool
A : Set
-}
