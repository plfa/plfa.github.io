---
title     : "Quantitative: Multiplicities and Linearity"
permalink : /Quantitative/Mult/
---

\begin{code}
module qtt.Quantitative.Mult where
\end{code}

\begin{code}
open import Data.Product using (_×_; _,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; isEquivalence)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
\end{code}

\begin{code}
data Mult : Set where
  0# : Mult
  1# : Mult
  ω# : Mult
\end{code}

\begin{code}
open import Algebra
open import Algebra.Structures         {A = Mult} _≡_
open import Algebra.FunctionProperties {A = Mult} _≡_
\end{code}

\begin{code}
suc : Mult → Mult
suc 0# = 1#
suc 1# = ω#
suc ω# = ω#
\end{code}

\begin{code}
_+_ : Mult → Mult → Mult
0# + π = π
1# + π = suc π
ω# + _ = ω#
\end{code}

\begin{code}
_*_ : Mult → Mult → Mult
0# * _  = 0#
1# * π  = π
ω# * 0# = 0#
ω# * 1# = ω#
ω# * ω# = ω#
\end{code}

\begin{code}
+-suc : ∀ π π′ → suc π + π′ ≡ suc (π + π′)
+-suc 0# π′ = refl
+-suc 1# 0# = refl
+-suc 1# 1# = refl
+-suc 1# ω# = refl
+-suc ω# π′ = refl
\end{code}

\begin{code}
+-assoc : Associative _+_
+-assoc 0# π′ π″ = refl
+-assoc 1# π′ π″ = +-suc π′ π″
+-assoc ω# π′ π″ = refl
\end{code}

\begin{code}
+-identityˡ : LeftIdentity 0# _+_
+-identityˡ π = refl

+-identityʳ : RightIdentity 0# _+_
+-identityʳ 0# = refl
+-identityʳ 1# = refl
+-identityʳ ω# = refl

+-identity : Identity 0# _+_
+-identity = +-identityˡ , +-identityʳ
\end{code}

\begin{code}
+-zeroˡ : LeftZero ω# _+_
+-zeroˡ _ = refl

+-zeroʳ : RightZero ω# _+_
+-zeroʳ 0# = refl
+-zeroʳ 1# = refl
+-zeroʳ ω# = refl

+-zero : Zero ω# _+_
+-zero = +-zeroˡ , +-zeroʳ
\end{code}

\begin{code}
+-comm : Commutative _+_
+-comm 0# π = sym (+-identityʳ π)
+-comm 1# 0# = refl
+-comm 1# 1# = refl
+-comm 1# ω# = refl
+-comm ω# π = sym (+-zeroʳ π)
\end{code}

\begin{code}
+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = +-assoc
  ; ∙-cong        = cong₂ _+_
  }
\end{code}

\begin{code}
+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ 0#
+-0-isCommutativeMonoid = record
  { isSemigroup = +-isSemigroup
  ; identityˡ   = +-identityˡ
  ; comm        = +-comm
  }
\end{code}

\begin{code}
*-identityˡ : LeftIdentity 1# _*_
*-identityˡ _ = refl

*-identityʳ : RightIdentity 1# _*_
*-identityʳ 0# = refl
*-identityʳ 1# = refl
*-identityʳ ω# = refl

*-identity : Identity 1# _*_
*-identity = *-identityˡ , *-identityʳ
\end{code}

\begin{code}
*-assoc : Associative _*_
*-assoc 0# π′ π″ = refl
*-assoc 1# π′ π″ = refl
*-assoc ω# 0# π″ = refl
*-assoc ω# 1# π″ = refl
*-assoc ω# ω# 0# = refl
*-assoc ω# ω# 1# = refl
*-assoc ω# ω# ω# = refl
\end{code}

\begin{code}
*-isSemigroup : IsSemigroup _*_
*-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = *-assoc
  ; ∙-cong        = cong₂ _*_
  }
\end{code}

\begin{code}
*-1-isMonoid : IsMonoid _*_ 1#
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }
\end{code}


\begin{code}
*-zeroˡ : LeftZero 0# _*_
*-zeroˡ _ = refl

*-zeroʳ : RightZero 0# _*_
*-zeroʳ 0# = refl
*-zeroʳ 1# = refl
*-zeroʳ ω# = refl

*-zero : Zero 0# _*_
*-zero = *-zeroˡ , *-zeroʳ
\end{code}

\begin{code}
*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ 0# 0# π″ = refl
*-distribʳ-+ 0# 1# 0# = refl
*-distribʳ-+ 0# 1# 1# = refl
*-distribʳ-+ 0# 1# ω# = refl
*-distribʳ-+ 0# ω# 0# = refl
*-distribʳ-+ 0# ω# 1# = refl
*-distribʳ-+ 0# ω# ω# = refl
*-distribʳ-+ 1# 0# π″ = refl
*-distribʳ-+ 1# 1# 0# = refl
*-distribʳ-+ 1# 1# 1# = refl
*-distribʳ-+ 1# 1# ω# = refl
*-distribʳ-+ 1# ω# π″ = refl
*-distribʳ-+ ω# 0# π″ = refl
*-distribʳ-+ ω# 1# 0# = refl
*-distribʳ-+ ω# 1# 1# = refl
*-distribʳ-+ ω# 1# ω# = refl
*-distribʳ-+ ω# ω# π″ = refl

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ 0# 0# π″ = refl
*-distribˡ-+ 0# 1# π″ = refl
*-distribˡ-+ 0# ω# π″ = refl
*-distribˡ-+ 1# 0# π″ = refl
*-distribˡ-+ 1# 1# π″ = refl
*-distribˡ-+ 1# ω# π″ = refl
*-distribˡ-+ ω# 0# π″ = refl
*-distribˡ-+ ω# 1# 0# = refl
*-distribˡ-+ ω# 1# 1# = refl
*-distribˡ-+ ω# 1# ω# = refl
*-distribˡ-+ ω# ω# 0# = refl
*-distribˡ-+ ω# ω# 1# = refl
*-distribˡ-+ ω# ω# ω# = refl

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+
\end{code}

\begin{code}
*-+-isSemiring : IsSemiring _+_ _*_ 0# 1#
*-+-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-0-isCommutativeMonoid
    ; *-isMonoid            = *-1-isMonoid
    ; distrib               = *-distrib-+
    }
  ; zero = *-zero
  }
\end{code}

\begin{code}
semiring : Semiring _ _
semiring = record
  { Carrier    = Mult
  ; _≈_        = _≡_
  ; _+_        = _+_
  ; _*_        = _*_
  ; 0#         = 0#
  ; 1#         = 1#
  ; isSemiring = *-+-isSemiring
  }
\end{code}
