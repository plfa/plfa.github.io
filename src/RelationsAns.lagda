---
title     : "Relations Answers"
layout    : page
permalink : /RelationsAns
---

## Imports

\begin{code}
open import Relations using (_≤_; _<_; even; odd; e+e≡e; ≤-refl; ≤-trans; +-mono-≤)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-suc)
open import Data.Product using (∃; _,_)
open _≤_
open _<_
open even
open odd
\end{code}

### Transitivity

\begin{code}
<-trans : ∀ {m n p} → m < n → n < p → m < p
<-trans z<s       (s<s n<p)  =  z<s
<-trans (s<s m<n) (s<s n<p)  =  s<s (<-trans m<n n<p)
\end{code}

### Trichotomy

\begin{code}
_>_ : ℕ → ℕ → Set
m > n = n < m

data Trichotomy (m n : ℕ) : Set where
  less : m < n → Trichotomy m n
  same : m ≡ n → Trichotomy m n
  more : m > n → Trichotomy m n
  
trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero    zero                    =  same refl
trichotomy zero    (suc n)                 =  less z<s
trichotomy (suc m) zero                    =  more z<s
trichotomy (suc m) (suc n) with trichotomy m n
...                           | less m<n   =  less (s<s m<n)
...                           | same refl  =  same refl
...                           | more m>n   =  more (s<s m>n)
\end{code}

### Monotonicity

\begin{code}
+-monoʳ-< : ∀ (m p q : ℕ) → p < q → m + p < m + q
+-monoʳ-< zero    p q p<q  =  p<q
+-monoʳ-< (suc m) p q p<q  =  s<s (+-monoʳ-< m p q p<q) 

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)
\end{code}

### Relate inequality to strict inequality

\begin{code}
≤-implies-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-implies-< (s≤s z≤n) = z<s
≤-implies-< (s≤s (s≤s m≤n)) = s<s (≤-implies-< (s≤s m≤n))

<-implies-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-implies-≤ z<s = s≤s z≤n
<-implies-≤ (s<s m<n) = s≤s (<-implies-≤ m<n)

<-trans′ : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans′ m<n n<p = ≤-implies-< (helper (<-implies-≤ m<n) (<-implies-≤ n<p))
  where
  helper : ∀ {m n p : ℕ} → suc m ≤ n → suc n ≤ p → suc m ≤ p
  helper sm≤n sn≤p = ≤-trans sm≤n (≤-trans n≤sn sn≤p)
    where
    n≤sn : ∀ {n : ℕ} → n ≤ suc n
    n≤sn {n} = +-mono-≤ 0 1 n n z≤n ≤-refl
\end{code}

*Even and odd*

\begin{code}
o+o≡e : ∀ {m n : ℕ} → odd  m → odd n → even (m + n)
e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd  (m + n)

o+o≡e (odd-suc em)  on  =  even-suc (e+o≡o em on)

e+o≡o even-zero     on  =  on
e+o≡o (even-suc om) on  =  odd-suc  (o+o≡e om on)
\end{code}

An alternative proof
\begin{code}
o+o≡e′ : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e′ {suc m} {suc n} (odd-suc em) (odd-suc en)
  rewrite +-suc m n = even-suc (odd-suc (e+e≡e em en))
\end{code}


The following is a solution to an exercise that should be moved
to the chapter that introduces quantifiers.

\begin{code}
+-lemma : ∀ (m : ℕ) → suc (suc (m + (m + 0))) ≡ suc m + (suc m + 0)
+-lemma m rewrite +-suc m (m + 0) = refl

is-even : ∀ (n : ℕ) → even n → ∃(λ (m : ℕ) → n ≡ 2 * m)
is-odd : ∀ (n : ℕ) → odd n → ∃(λ (m : ℕ) → n ≡ 1 + 2 * m)

is-even zero even-zero =  zero , refl
is-even (suc n) (even-suc on) with is-odd n on
... | m , n≡1+2*m rewrite n≡1+2*m | +-lemma m = suc m , refl

is-odd (suc n) (odd-suc en) with is-even n en
... | m , n≡2*m rewrite n≡2*m = m , refl
\end{code}

    
