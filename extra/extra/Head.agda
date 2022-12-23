import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; dropWhile)
open import Data.Char using (Char)
open import Data.Bool using (Bool; true; false)
import Data.Char as Char using (_≟_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)


data Head {A : Set} (P : A → Bool) : List A → Set where
  head : ∀ (c : A) (s : List A) → P c ≡ true → Head P (c ∷ s)

prime : Char
prime = '′'

isPrime : Char → Bool
isPrime c = ⌊ c Char.≟ prime ⌋

head-lemma : ∀ (s : List Char) → ¬ Head isPrime (dropWhile isPrime s)
head-lemma [] = λ()
head-lemma (c ∷ s) with isPrime c
...                   | true       =  head-lemma s
...                   | false      =  ¬h
  where
  ¬h : ¬ Head isPrime (c ∷ s)
  ¬h (head c s eqn′) = {!!}

{-
Goal: ⊥
————————————————————————————————————————————————————————————
s    : List Char
c    : Char
eqn′ : ⌊ (c Char.≟ '′' | .Agda.Builtin.Char.primCharEquality c '′')
       ⌋
       ≡ true
s    : List Char
c    : Char
-}
