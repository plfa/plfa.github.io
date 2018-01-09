---
title     : "Relations Exercises"
layout    : page
permalink : /RelationsEx
---

## Imports

\begin{code}
open import Naturals using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Relations using (_≤_; _<_; Trichotomy; even; odd)
open import Properties using (+-comm; +-identity; +-suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Product using (∃; _,_)
open Trichotomy
open _<_
open _≤_
open even
open odd
\end{code}

*Trichotomy*

\begin{code}
trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = same refl
trichotomy zero (suc n) = less z<s
trichotomy (suc m) zero = more z<s
trichotomy (suc m) (suc n) with trichotomy m n
... | less m<n = less (s<s m<n)
... | same refl = same refl
... | more n<m = more (s<s n<m)
\end{code}

*Relate strict comparison to comparison*

\begin{code}
<-implies-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-implies-≤ z<s = s≤s z≤n
<-implies-≤ (s<s m<n) = s≤s (<-implies-≤ m<n)

≤-implies-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-implies-< (s≤s z≤n) = z<s
≤-implies-< (s≤s (s≤s m≤n)) = s<s (≤-implies-< (s≤s m≤n))
\end{code}

*Even and odd*

\begin{code}
+-evev : ∀ {m n : ℕ} → even m → even n → even (m + n)
+-evev ev-zero evn = evn
+-evev (ev-suc (od-suc evm)) evn = ev-suc (od-suc (+-evev evm evn))

+-evod : ∀ {m n : ℕ} → even m → odd n → odd (m + n)
+-evod ev-zero odn = odn
+-evod (ev-suc (od-suc evm)) odn = od-suc (ev-suc (+-evod evm odn))

+-odev : ∀ {m n : ℕ} → odd m → even n → odd (m + n)
+-odev (od-suc evm) evn = od-suc (+-evev evm evn)

+-odod : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
+-odod (od-suc evm) odn = ev-suc (+-evod evm odn)
\end{code}

\begin{code}
+-lemma : ∀ (m : ℕ) → suc (suc (m + (m + 0))) ≡ suc m + (suc m + 0)
+-lemma m rewrite +-identity m | +-suc m m = refl

+-lemma′ : ∀ (m : ℕ) → suc (suc (m + (m + 0))) ≡ suc m + (suc m + 0)
+-lemma′ m rewrite +-suc m (m + 0) = {!!}

mutual
  is-even : ∀ (n : ℕ) → even n → ∃(λ (m : ℕ) → n ≡ 2 * m)
  is-even zero ev-zero =  zero , refl
  is-even (suc n) (ev-suc odn) with is-odd n odn
  ... | m , n≡1+2*m rewrite n≡1+2*m | +-lemma m = suc m , refl

  is-odd : ∀ (n : ℕ) → odd n → ∃(λ (m : ℕ) → n ≡ 1 + 2 * m)
  is-odd (suc n) (od-suc evn) with is-even n evn
  ... | m , n≡2*m rewrite n≡2*m = m , refl
\end{code}

    
