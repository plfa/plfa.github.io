{-
\bN -- ℕ
\qed -- ∎
\< -- ⟨
\r -- → -- didn't navigate
\r -- ⇒ -- navigated 1 right
M-x agda-input-show-translations -- list special characters
M-x quail-show-key -- show character code under cursor
M-. -- go to definition
C-c C-l -- type check; convert "?" to "{ }0"
C-c C-n -- evaluate a new expression
C-c C-d -- show type of a new expression
C-c C-f -- forward to next hole (e.g. "{ }0")
C-c C-c -- split case
C-c C-, -- info about current hole. e.g. what variables are available
C-c C-space -- remove hole
C-c C-r -- fill a hole with a constructor, or list the multiple possible constructors
C-c C-a -- fill in holes by solving, if there's only one possibility

Locations:
≡ -- ~/tmp/agda/plfa/standard-library/src/Relation/Binary/PropositionalEquality.agda
     https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html
Definitions of basics -- ~/tmp/agda/agda/test/LibSucceed/InstanceArgument/13-implicitProofObligations.agda

Our repo branch:
  https://github.com/agda-reading-group/plfa.github.io/tree/arg
  git clone https://github.com/agda-reading-group/plfa.github.io.git
  git checkout -t origin/arg
-}

data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

seven' : ℕ
seven' = 7

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    5
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 + 4 ≡ 7
_ = refl

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

_ : 2 * 3 ≡ 6
_ = refl

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = refl

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

infixl 6 _+_ _∸_
infixl 7 _*_
infixr 8 _^_

plus : ℕ → ℕ → ℕ
plus zero n = n
plus (suc m) n = suc (plus m n)

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- big endian, considering fixity (_O, _I)
-- would be little endian in prefix notation
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (m O) = m I
inc (m I) = (inc m) O

_ : inc ⟨⟩ ≡ ⟨⟩ I
_ = refl
_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl
_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl
_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl
_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc m) = inc (to m)

from : Bin → ℕ
from ⟨⟩ = 0
from (m O) = 2 * from m
from (m I) = suc (2 * from m)

_ : from (to 0) ≡ 0
_ = refl
_ : from (to 1) ≡ 1
_ = refl
_ : from (to 2) ≡ 2
_ = refl
_ : from (to 3) ≡ 3
_ = refl
_ : from (to 4) ≡ 4
_ = refl
_ : from (to 5) ≡ 5
_ = refl

{-
trans : (T : Set₁) → (a : T) -> (b : T) -> (c : T) -> (a ≡ b) -> (b ≡ c) -> (a ≡ c)
trans T a b c ab bc = {!!}
-}
