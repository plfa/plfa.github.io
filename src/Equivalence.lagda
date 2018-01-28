---
title     : "Equivalence: Martin Löf equivalence"
layout    : page
permalink : /Logic
---

## Equivalence

Much of our reasoning has involved equivalence.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have taken equivalence as a primitive,
but in fact it can be defined using the machinery of inductive
datatypes.

We declare equivalence as follows.
\begin{code}
data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x
\end{code}
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`.  Hence, every
value is equivalent to itself, and we have no way of showing values
are equivalent.  Here we have quantified over all levels, so that
we can apply equivalence to types belonging to any level.

We declare the precedence of equivalence as follows.
\begin{code}
infix 4 _≡_
\end{code}
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.

[CONTINUE FROM HERE. FIND A SIMPLE PROOF USING REWRITE.]

Including the lines
\begin{code}
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}
\end{code}
permits the use of equivalences in rewrites.  When we give
a proof such as 

\begin{code}
cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl
\end{code}

