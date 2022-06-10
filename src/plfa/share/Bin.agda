module plfa.share.Bin where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

infixl 5 _O _I

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = double (from b)
from (b I) = suc (double (from b))
