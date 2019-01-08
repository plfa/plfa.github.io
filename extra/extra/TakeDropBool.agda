import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; takeWhile; dropWhile)
open import Data.List.All using (All; []; _∷_)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)

module TakeDropBool (A : Set) (P : A → Bool) where

  Head : ∀ {A : Set} → (A → Bool) → List A → Set
  Head P []       =  ⊥
  Head P (c ∷ s)  =  T (P c)

  data Book (x : A) (b : Bool) : Set where
    book : P x ≡ b → Book x b

  boo : ∀ (x : A) → Book x (P x)
  boo x = book refl

  dropWhile-lemma : ∀ (s : List A) → ¬ Head P (dropWhile P s)
  dropWhile-lemma []                                         =  λ()
  dropWhile-lemma (c ∷ s) with P c    | boo c
  ...                        | true   | _                    =  dropWhile-lemma s
  ...                        | false  | book eq  rewrite eq  =  λ()

  takeWhile-lemma : ∀ (s : List A) → All (T ∘ P) (takeWhile P s)
  takeWhile-lemma []                                         =  []
  takeWhile-lemma (c ∷ s) with P c    | boo c
  ...                        | false  | _                    =  []
  ...                        | true   | book eq rewrite eq   =  {! tt!} ∷ takeWhile-lemma s


{-  Hole 0
Goal: T (P c)
————————————————————————————————————————————————————————————
s  : List A
eq : P c ≡ true
c  : A
P  : A → Bool
A  : Set
-}
