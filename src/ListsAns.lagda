---
title     : "Lists Answers"
layout    : page
permalink : /ListsAns
---

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; suc; zero; _+_; _*_)
open import Data.Nat.Properties.Simple using (*-comm; distribʳ-*-+)
open import Data.List using (List; []; _∷_; _++_; foldr)

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m n p = distribʳ-*-+ p m n
\end{code}

*Sum of count*

\begin{code}
sum : List ℕ → ℕ
sum = foldr _+_ 0

countdown : ℕ → List ℕ
countdown zero = []
countdown (suc n) = suc n ∷ countdown n

infix 6 _+

_+ : ℕ → ℕ → ℕ
(m +) n = m + n

cong2 : ∀ {A B C : Set} {x x′ : A} {y y′ : B} →
  (f : A → B → C) → (x ≡ x′) → (y ≡ y′) → (f x y ≡ f x′ y′)
cong2 f x≡x′ y≡y′ rewrite x≡x′ | y≡y′ = refl

sum-countdown : ∀ (n : ℕ) → sum (countdown n) * 2 ≡ suc n * n
sum-countdown zero = refl
sum-countdown (suc n) = 
  begin
    sum (countdown (suc n)) * 2
  ≡⟨⟩
    sum (suc n ∷ countdown n) * 2
  ≡⟨⟩
    (suc n + sum (countdown n)) * 2
  ≡⟨ *-distrib-+ (suc n) (sum (countdown n)) 2 ⟩
    suc n * 2 + sum (countdown n) * 2
  ≡⟨ cong (suc n * 2 +) (sum-countdown n) ⟩
    suc n * 2 + suc n * n
  ≡⟨ cong2 _+_ (*-comm (suc n) 2) (*-comm (suc n) n) ⟩
    2 * suc n + n * suc n
  ≡⟨ sym (*-distrib-+ 2 n (suc n))⟩
    (2 + n) * suc n
  ∎
\end{code}
