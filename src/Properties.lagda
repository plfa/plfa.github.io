---
title     : "Properties: Proof by Induction"
layout    : page
permalink : /Properties
---

Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of *inductive datatypes* are proved by
*induction*.


## Imports

Each chapter will begin with a list of the imports we require from the
Agda standard library.

<!-- We will, of course, require the naturals;
everything in the previous chapter is also found in the library module
`Data.Nat`, so we import the required definitions from there.
We also require propositional equality. -->

\begin{code}
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
line.  It is often easiest to read such computations from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for *all* the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
*proof by induction*.


## Proof by induction

Recall the definition of natural numbers.
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
\end{code}
This tells us that `zero` is a natural---the *base case*---and that if
`m` is a natural then `suc m` is also a natural---the *inductive
case*.

Proofs by induction follow the structure of this definition.  To prove
a property of natural numbers by induction, we need prove two cases.
First is the *base case*, where we need to show the property holds for
`zero`.  Second is the *inductive case*, where we assume as the
*inductive hypothesis* that the property holds for an arbitary natural
`m` and then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then we can write out the principle
of induction as an inference rule:

    P zero
    ∀ (m : ℕ) → P m → P (suc m)
    -----------------------------
    ∀ (m : ℕ) → P m

Let's unpack this rule.  The first hypothesis is the base case, and
requires we show that property `P` holds for `zero`.  The second
hypothesis is the inductive case, and requires that for any natural
`m` assuming the the induction hypothesis `P` holds for `m` we must
then show that `P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties.

    -- in the beginning, no properties are known

Now, we apply the two cases to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply.

    -- on the first day, one property is known
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the two
cases.  The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today.

    -- on the second day, two properties are known
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new.

    -- on the third day, three properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))

You've probably got the hang of it by now.

    -- on the fourth day, four properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the *n*th day there will be *n* distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day *n+1*. 

## Our first proof: associativity

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
In tabular form we have:

       (zero + n) + p
    ≡    (i)
       n + p
    ≡    (i)
       zero + (n + p)

Again, it is easiest to read from the top down until one reaches the
simplest term (`n + p`), and then from the bottom up
until one reaches the same term.

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

Here it is easiest to read from the top down until one reaches the
simplest term (`suc ((m + n) + p)`), and then from the bottom up until
one reaches the simplest term (`suc (m + (n + p))`).  In this case,
the two simplest terms are not the same, but are equated by the
induction hypothesis.

## Encoding the proof in Agda

We can encode this proof in Agda as follows.
\begin{code}
assoc+ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
assoc+ zero n p = refl
assoc+ (suc m) n p rewrite assoc+ m n p = refl
\end{code}
Here we have named the proof `assoc+`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The first line states that we are
defining the identifier `assoc+` which is a proof of the
proposition

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

Such a proof is a function that takes three natural
numbers---corresponding to `m`, `n`, and `p`---and returns
a proof of the proposition `(m + n) + p ≡ m + (n + p)`.
Proof by induction corresponds exactly to a recursive
definition.  Here we are inducting on the first
argument `m`, and leaving the other two arguments `n` and `p`
fixed.

The base case corresponds to instantiating `m` by
pattern matching on `zero`, so what we are required to
prove is:

    (zero + n) + p ≡ zero + (n + p)

After simplifying with the definition of addition, this equation
becomes:

    n + p ≡ n + p

The proof that a term is equal to itself is written `refl`.

The inductive case corresponds to instantiating `m` by `suc zero`,
so what we are required to prove is:

    (suc m + n) + p ≡ suc m + (n + p)

After simplifying with the definition of addition, this equation
becomes:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are
equal, and the proof is again given by `refl`.

Rewriting by a given equation is indicated by the keyword `rewrite`
followed by a proof of that equation.  Here the inductive hypothesis
is not assumed, but instead proved by a recursive invocation of the
function we are definining, `assoc+ m n p`.  As with addition, this is
well founded because associativity of larger numbers is defined in
terms of associativity of smaller numbers.  In this case,
`assoc (suc m) n p` is defined in terms of `assoc m n p`.

This correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.

## Unicode

In this chapter we use the following unicode.

    ≡  U+2261  IDENTICAL TO (\==)
    ∀  U+2200  FOR ALL (\forall)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\Gl, \lambda)
