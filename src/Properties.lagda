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
Agda standard library.  We will, of course, require the naturals; everything in the
previous chapter is also found in the library module `Data.Nat`, so we
import the required definitions from there.  We also require
propositional equality.

\begin{code}
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
\end{code}

Each import consists of the keywords `open` and `import`, followed by
the module name, followed by the keyword `using`, followed by the
names of each identifier imported from the module, surrounded by
parentheses and separated by semicolons. Parentheses and semicolons
are among the few characters that cannot appear in names, so we do not
need extra spaces in the import list.


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

Recall the definition of natural numbers consists of a *base case*
which tells us that `zero` is a natural, and an *inductive case*
which tells us that if `m` is a natural then `suc m` is also a natural.

Proofs by induction follow the structure of this definition.  To prove
a property of natural numbers by induction, we need prove two cases.
First is the *base case*, where we show the property holds for `zero`.
Second is the *inductive case*, where we assume the property holds for
an arbitary natural `m` (we call this the *inductive hypothesis*), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis, that `P` holds for `m`, then it follows that
`P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties.

    -- in the beginning, no properties are known

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply.

    -- on the first day, one property is known
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
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

Then the appropriate instances of the inference rules, which
we must show to hold, become:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

In the inference rules, `n` and `p` are any arbitary natural numbers, so when we
are done with the proof we know it holds for any `n` and `p` as well as any `m`.

Recall the definition of addition has two clauses. 

    zero    + n  =  n                -- (i)
    (suc m) + n  =  suc (m + n)      -- (ii)

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

    (suc m + n) + p ≡ suc m + (n + p)

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

We encode this proof in Agda as follows.
\begin{code}
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl
\end{code}
Here we have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The first line states that we are
defining the identifier `+-assoc` which is a proof of the
proposition

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p` that
the equations `(m + n) + p ≡ m + (n + p)` holds.  Such a proof
is a function that accepts three natural numbers---corresponding to
to `m`, `n`, and `p`---and returns a proof of the equation.

Proof by induction corresponds exactly to a recursive definition.
Here we induct on the first argument `m`, and leave the other two
arguments `n` and `p` fixed.

The base case corresponds to instantiating `m` by
pattern matching on `zero`, so what we are required to
prove is:

    (zero + n) + p ≡ zero + (n + p)

After simplifying with the definition of addition, this equation
becomes:

    n + p ≡ n + p

The proof that a term is equal to itself is written `refl`.

The inductive case corresponds to instantiating `m` by `suc m`,
so what we are required to prove is:

    (suc m + n) + p ≡ suc m + (n + p)

After simplifying with the definition of addition, this equation
becomes:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are
equal, and the proof is again given by `refl`.
Rewriting by a given equation is indicated by the keyword `rewrite`
followed by a proof of that equation.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are definining, `+-assoc m n p`.
As with addition, this is well-founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `+-assoc (suc m) n p` is proved using `+-assoc m n p`.

The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.


## Building proofs interactively

Agda is designed to be used with the Emacs text editor, and the two
in combination provide features that help to create proofs interactively.

Begin by typing

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `^C ^L` (control-C
followed by control-L), the question mark will be replaced.

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc m n p = { }0

The empty braces are called a *hole*, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgement.

We wish to prove the proposition by induction on `m`.  More
the cursor into the hole and type `^C ^C`.  You will be given
the prompt:

    pattern variables to case:

Typing `m` will cause a split on that variable, resulting
in an update to the code.

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc zero n p = { }0
    +-assoc (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `^C ^,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `^C ^R` will fill it in,
renumbering the remaining hole to 0:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc zero n p = refl
    +-assoc (suc m) n p = { }0

Going into the new hold 0 and typing `^C ^,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc zero n p = refl
    +-assoc (suc m) n p rewrite +-assoc m n p = { }0

Going into the remaining hole and typing `^C ^,` will show the
goal is now trivial:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `^C ^R` will fill it in, completing the proof:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc zero n p = refl
    +-assoc (suc m) n p rewrite +-assoc m n p = refl


## Creation, one last time

Again, it may be helpful to view the recursive definition as
a creation story.  This time we are concerned with judgements
asserting associativity.

     -- in the beginning, we know nothing about associativity

Now, we apply the rules to all the judgements we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then `(suc m + n) + p ≡ suc m + (n
+ p)` (today).  We didn't know any judgments about associativity
before today, so that rule doesn't give us any new judgments.

    -- on the first day, we know about associativity of 0
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    
Then we repeat the process, so on the next day we know about all the
judgements from the day before, plus any judgements added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgements.

    -- on the second day, we know about associativity of 0 and 1
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again.

    -- on the third day, we know about associativity of 0, 1, and 2
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've probably got the hang of it by now.

    -- on the fourth day, we know about associativity of 0, 1, 2, and 3
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

The process continues.  On the *m*th day we will know all the
judgements where the first number is less than *m*.


## Our second proof: commutativity

Another important property of addition is that it is commutative.  To show
this by induction, we take `P m` to be the property

    m + n ≡ n + m

Then the appropriate instances of the inference rules, which
we must show to hold, become:

    -------------------
    zero + n ≡ n + zero

    m + n ≡ n + m
    ---------------------
    suc m + n ≡ n + suc m

In the inference rules, `n` is any arbitary natural number, so when we
are done with the proof we know it holds for any `n` as well as any `m`.

By equation (i) of the definition of addition, the left-hand side of
the conclusion of the base case simplifies to `n`, so the base case
will hold if we can show

    n + zero ≡ n    -- (x)

By equation (ii) of the definition of addition, the left-hand side of
the conclusion of the inductive case simplifies to `suc (m + n)`, so
the inductive case will hold if we can show

    n + suc m ≡ suc (n + m)    -- (xi)

and then apply the inductive hypothesis to rewrite `m + n` to `n + m`.
We use induction two more times, on `n` this time rather than `m`, to
show both (x) and (xi).

Here is the proof written out in full, using tabular form.

Proposition.

    m + n ≡ n + m

Proof. By induction on `m`.

Base case.

       zero + n
    ≡    (i)
       n
    ≡    (x)
       n + zero

Inductive case.

       suc m + n
    ≡    (ii)
       suc (m + n)
    ≡    (inductive hypothesis)
       suc (n + m)
    ≡    (xi)
       n + suc m
       
QED.

As with other tabular prooofs, it is best understood by reading from top
down and bottom up and meeting in the middle.

We now prove each of the two required lemmas, (x) and (xi).

Lemma (x).

    n + zero ≡ n

Proof. By induction on `n`.

Base case.

       zero + zero
    ≡    (i)
       zero

Inductive case.

       suc n + zero
    ≡    (ii)
       suc (n + zero)
    ≡    (inductive hypothesis)
       suc n

QED.

Lemma (xi).

    m + suc n ≡ suc (m + n)

Proof. By induction on `m`.

Base case.

       zero + suc n
    ≡    (i)
       suc n
    ≡    (i)
       suc (zero + n)

Inductive case.

       suc m + suc n
    ≡    (ii)
       suc (m + suc n)
    ≡    (inductive hypothesis)
       suc (suc (m + n))
    ≡    (ii)
       suc (suc m + n)

QED.

## Encoding the proofs in Agda

These proofs can be encoded concisely in Agda.
\begin{code}
+-identity : ∀ (n : ℕ) → n + zero ≡ n
+-identity zero = refl
+-identity (suc n) rewrite +-identity n = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n rewrite +-identity n = refl
+-comm (suc m) n rewrite +-suc n m | +-comm m n = refl
\end{code}
Here we have renamed Lemma (x) and (xi) to `+-identity` and `+-suc`,
respectively.  In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.

## Exercises

+ *Swapping terms*. Show

    m + (n + p) ≡ n + (m + p)

  for all naturals `m`, `n`, and `p`. No induction is needed,
  just apply the previous results which show addition
  is associative and commutative.  You may need to use
  one or more of the following functions from the standard library:

     sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m
     trans : ∀ {m n p : ℕ} → m ≡ n → n ≡ p → m ≡ p

  Name your proof `+-swap`.  

+ *Multiplication distributes over addition*. Show

    (m + n) * p ≡ m * p + n * p

  for all naturals `m`, `n`, and `p`. Name your proof `*-distrib-+`.

+ *Multiplication is associative*. Show

    (m * n) * p ≡ m * (n * p)

  for all naturals `m`, `n`, and `p`. Name your proof `*-assoc`.

+ *Multiplication is commutative*. Show

    m * n ≡ n * m

  for all naturals `m` and `n`.  As with commutativity of addition,
  you will need to formulate and prove suitable lemmas.
  Name your proof `*-comm`.

+ *Monus from zero* Show

    zero ∸ n ≡ zero

  for all naturals `n`. Did your proof require induction?
  Name your proof `0∸n≡0`.

+ *Associativity of monus with addition* Show

    m ∸ n ∸ p ≡ m ∸ (n + p)

  for all naturals `m`, `n`, and `p`.
  Name your proof `∸-+-assoc`.

## Unicode

This chapter introduces the following unicode.

    ≡  U+2261  IDENTICAL TO (\==)
    ∀  U+2200  FOR ALL (\forall)
