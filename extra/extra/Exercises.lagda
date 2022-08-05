(from Naturals.lagda)

#### Exercise (stretch: `ℕ¹`, `_+¹_ `, `_*¹_ `) {#Nat1}

Some mathematicians, instead of defining the naturals as starting
at zero define them as starting at one.
\begin{code}
data ℕ¹ : Set where
  one : ℕ¹
  suc : ℕ¹ → ℕ¹
\end{code}
In this system, there is no representation for zero, while
three is represented by `suc (suc one)`.  This is our first
use of _overloaded_ constructors, that is, using the same
name for constructors of different types.

Define versions of addition and multiplication that act on
such numbers.
\begin{code}
postulate
  _+¹_ : ℕ¹ → ℕ¹ → ℕ¹
  _*¹_ : ℕ¹ → ℕ¹ → ℕ¹
\end{code}
In Agda, functions --- unlike constructors --- may not be overloaded,
so we have chosen `_+¹_` and `_*¹_`  as names distinct from `_+_`
and `_*_`.

Confirm that two plus three is five and two times three is
six in this representation.
