---
title     : "Properties: Proof by Induction"
layout    : page
permalink : /Properties
---

Now that we've defined the naturals and operations upon them,
our next step is to learn how to prove properties that they
satisfy.  Unsurprisingly, properties of *inductive datatypes*
are proved by *induction*.


## Imports

Each chapter will begin with a list of the imports we require from the
Agda standard library.  We will, of course, require the naturals;
everything in the previous chapter is also found in the library module
`Data.Nat`, so we import the required definitions from there.  We also
require propositional equality.

\begin{code}
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}

Each import consists of the keywords `open` and `import`, followed by
the module name, followed by the keyword `using`, followed by the
names of each identifier imported from the module, surrounded by
parentheses and separated by semicolons.


## Associativity

One property of addition is that it is *associative*, that is that the
order of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

We write `=` in an Agda definition, whereas we write `≡` for an
equality we are trying to prove.  Here `m`, `n`, and `p` are variables
that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables.

       (3 + 4) + 5
    ≡
       7 + 5
    ≡
       12
    ≡
       3 + 9
    ≡
       3 + (4 + 5)

Here we have displayed the computation in tabular form, one term to a
line.  We will often use such a form.  It is often easiest to read
such computations from the top down until one reaches the simplest
possible term (in this case, 12), and then from the bottom up until
one reaches the same term.

We could go on testing the proposition by choosing other numbers, but---since there are an infinite number of naturals---we will never finish.



To prove a property of natural numbers by induction, we need to prove two things.
First, we prove the property holds for `zero`, and secondly we prove that if
the property holds for an arbitrary natural `m` then it also holds for `suc m`.
If we write `P m` for a property of `m`, then we can write out the principle
of induction as an inference rule:

    P zero
    ∀ (m : ℕ) → P m → P (suc m)
    -----------------------------
    ∀ (m : ℕ) → P m

Let's unpack this rule.  The first hypothesis states
that property `P` holds for `zero`.  The second hypothesis states that for all natural
numbers `m`, if `P` holds for `m` then `P` also holds for `suc m`.  The conclusion
states that for all natural numbers `m` we have that `P` holds for `m`.
We call the first hypothesis the *base case*; it requires we show `P zero`.
We call the second hypothesis the *inductive case*; it requires we assume `P m`, which
we call the *induction hypothesis*, and use it to show `P (suc m)`.

In order to prove associativity, we take `P m` to be the property

    (m + n) + p ≡ m + (n + p)

Then the appropriate instance of the inference rule becomes:

    (zero + n) + p ≡ zero + (n + p)
    ∀ (m : ℕ) → (m + n) + p ≡ m + (n + p)  →  (suc m + n) + p ≡ (suc m + n) + p
    -----------------------------------------------------------------------------
    ∀ (m : ℕ) → (m + n) + p ≡ m + (n + p)

In the inference rule, `n` and `p` are any arbitary natural numbers, so when we
are done with the proof we know it holds for any `n` and `p` as well as any `m`.

Recall the definition of addition.
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero    + n  =  n                -- (i)
(suc m) + n  =  suc (m + n)      -- (ii)
\end{code}

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

By (i), both sides of the equation simplify to `n + p`, so it holds.
In tabular form, we write this as follows:

       (zero + n) + p
    ≡    (i)
       n + p
    ≡    (i)
       zero + (n + p)

It is often easiest to read such proofs down from the top and up from
the bottom, meeting in the middle where the two terms are the same.

For the inductive case, we assume

    (m + n) + p ≡ m + (n + p)

and must show

    (suc m + n) + p ≡ (suc m + n) + p

By (ii), the left-hand side simplifies to `suc ((m + n) + p)` and the
right-hand side simplifies to `suc (m + (n + p))`, and the equality of
these follow from what we assumed.  In tabular form:

       (suc m + n) + p
    ≡    (ii)
       suc (m + n) + p
    ≡    (ii)
       suc ((m + n) + p)
    ≡    (induction hypothesis)
       suc (m + (n + p))
    ≡    (ii)
       suc m + (n + p)





## Unicode

In this chapter we use the following unicode.

    ≡  U+2261  IDENTICAL TO (\==)
    ∀  U+2200  FOR ALL (\forall)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\Gl, \lambda)
