---
title     : "Naturals: Natural numbers"
layout    : page
permalink : /Naturals
---


The night sky holds more stars than I can count, though less than five
thousand are visible to the naked sky.  The observable universe
contains about seventy sextillion stars.

But the number of stars is finite, while natural numbers are infinite.
Count all the stars, and you will still have as many natural numbers
left over as you started with.

## The naturals are an inductive datatype

Everyone is familiar with the natural numbers:

    0
    1
    2
    3
    ...

and so on. We write `ℕ` for the *type* of natural numbers, and say that
`0`, `1`, `2`, `3`, and so on are *values* of type `ℕ`.  In Agda,
we indicate this by writing

    0 : ℕ
    1 : ℕ
    2 : ℕ
    3 : ℕ
    ...

and so on.

The set of natural numbers is infinite, yet we can write down
its definition in just a few lines.  Here is the definition
as a pair of inference rules:

    --------
    zero : ℕ

    n : ℕ
    ---------
    suc n : ℕ

And here is the definition in Agda:
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
\end{code}
Here `ℕ` is the name of the *datatype* we are defining,
and `zero` and `suc` (short for *successor*) are the
*constructors* of the datatype.

Both definitions above tell us the same two things:

1. The term `zero` is a natural number.
2. If `n` is a natural number, then the term `suc n` is also a natural number.

Further, these two rules give the *only* ways of creating natural numbers.
Hence, the possible natural numbers are

    zero
    suc zero
    suc (suc zero)
    suc (suc (suc zero))
    ...

We write `0` as shorthand for `zero`; and `1` is shorthand
for `suc zero`, the successor of zero, that is, the natural that comes
after zero; and `2` is shorthand for `suc (suc zero)`, which is the
same as `suc 1`, the successor of one; and `3` is shorthand for the
successor of two; and so on.


### Unpacking the inference rules

Let's unpack the inference rules.  Each inference rule consists of zero
or more *judgments* written above a horizontal line, called the *hypotheses*,
and a single judgment written below, called the *conclusion*.  

The first rule has no hypotheses, and the conclusion asserts that zero
is a natural.  The second rule has one hypothesis, which assumes that
`n` is a natural number, and the conclusion asserts that `suc n` is a
natural number.


### Unpacking the Agda definition

Let's unpack the Agda definition. The keyword `data` tells us this is an
inductive definition, that is, that we are defining a new datatype
with constructors.  The phrase

    ℕ : Set

tells us that `ℕ` is the name of the new datatype, and that it is a
`Set`, which is the way in Agda of saying that it is a type.  The
keyword `where` separates the declaration of the datatype from the
declaration of its constructors. Each constructor is declared on a
separate line, which is indented to indicate that it belongs to the
corresponding `data` declaration.  The lines

    zero : ℕ
    suc : ℕ → ℕ

tell us that `zero` is a natural number and that `suc` takes a natural
number as argument and returns a natural number.

Here `ℕ` and `→` are unicode symbols that you won't find on your
keyboard. At the end of each chapter is a list of all the unicode used
in the chapter, including instructions on how to type them in the
Emacs text editor.


### The story of creation

Let's look again at the definition of natural numbers:

1. The term `zero` is a natural number.
2. If `n` is a natural number, then the term `suc n` is also a natural number.

Wait a minute! The second line appears to be defining natural numbers
in terms of natural numbers. How can that posssibly be allowed?

In fact, it is possible to assign this a non-circular meaning.
Furthermore, we can do so while only working with *finite* sets and never
referring to the entire *infinite* set of natural numbers.

We will think of it as a creation story.  To start with, we know about
no natural numbers at all.

    -- in the beginning there are no natural numbers

Now, we apply the rules to all the natural numbers we know about.  One
rule tells us that `zero` is a natural number, so we add it to the set
of known natural numbers.  The other rule tells us that if `n` is a
natural number (on the day before today) then `suc n` is also a
natural number (today).  We didn't know about any natural numbers
before today, so we don't add any natural numbers of the form `suc n`.

    -- on the first day, there is one natural number   
    zero

Then we repeat the process, so on the next day we know about all the
numbers from the day before, plus any numbers added by the rules.  One
rule tells us that `zero` is a natural number, but we already knew
that. But now the other rule tells us that since `zero` was a natural
number yesterday, `suc zero` is a natural number today.

    -- on the second day, there are two natural numbers
    zero
    suc zero

And we repeat the process again. Once more, one rule tells us what
we already knew, that `zero` is a natural number.  And now the other rule
tells us that since `zero` and `suc zero` are both natural numbers, then
`suc zero` and `suc (suc zero)` are natural numbers. We already knew about
the first of these, but the second is new.

    -- on the third day, there are three natural numbers
    zero
    suc zero
    suc (suc zero)

You've probably got the hang of it by now.

    -- on the fourth day, there are four natural numbers
    zero
    suc zero
    suc (suc zero)
    suc (suc (suc zero))

The process continues.  On the *n*th day there will be *n* distinct
natural numbers. Note that in this way, we only talk about finite sets
of numbers. Every natural number will appear on some given finite
day. In particular, the number *n* first appears on day *n+1*. And we
never actually define the set of numbers in terms of itself. Instead,
we define the set of numbers on day *n+1* in terms of the set of
numbers on day *n*.

A process like this one is called *inductive*. We start with nothing, and
build up a potentially infinite set by applying rules that convert one
finite set into another finite set.

The rule defining zero is called a *base case*, because it introduces
a natural number even when we know no other natural numbers.  The rule
defining successor is called an *inductive case*, because it
introduces more natural numbers once we already know some.  Note the
crucial role of the base case.  If we only had inductive rules, then
we would have no numbers in the beginning, and still no numbers on the
second day, and on the third, and so on.  An inductive definition lacking
a base case is useless, as in the phrase "Brexit means Brexit".

A philosopher might note that our reference to the first day, second
day, and so on, implicitly involves an understanding of natural
numbers.  In this sense, our definition might indeed be regarded as in
some sense circular.  We won't worry about the philosophy, but are ok
with taking some intuitive notions---such as counting---as given.

While the natural numbers have been understood for as long as people
could count, this way of viewing the natural numbers is relatively
recent.  It can be traced back to Richard Dedekind's paper "*Was sind
und was sollen die Zahlen?*" (What are and what should be the
numbers?), published in 1888, and Giuseppe Peano's book "*Arithmetices
principia, nova methodo exposita*" (The principles of arithmetic
presented by a new method), published the following year.


### The `NATURAL` pragma

In Agda, any line beginning `--`, or any code enclosed between `{-`
and `-}` is considered a *comment*.  Comments have no effect on the
code, with the exception of one special kind of comment, called a
*pragma*, which is enclosed between `{-#` and `#-}`.

Including the line
\begin{code}
{-# BUILTIN NATURAL ℕ #-}
\end{code}
tells Agda that `ℕ` corresponds to the natural numbers, and hence one
is permitted to type `0` as shorthand for `zero`, `1` as shorthand for
`suc zero`, `2` as shorthand for `suc (suc zero)`, and so on.

As well as enabling the above shorthand, the pragma also enables a
more efficient internal representation of naturals as the Haskell type
`Integer`.  Whereas representing the natural *n* with `suc` and `zero`
require space proportional to *n*, represeting it as an integer in
Haskell only requires space proportional to the logarithm of *n*.


## Operations on naturals are recursive functions

Now that we have the natural numbers, what can we do with them?
An obvious first step is to define basic operations such as
addition and multiplication.

As a child I spent much time memorising tables of addition and
multiplication.  At first the rules seemed tricky and I would often
make mistakes.  So it came as a shock to realise that all of addition
can be precisely defined in just a couple of lines, and the same is true of
multiplication.

Here is the definition of addition in Agda:
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)
\end{code}
This definition is *recursive*, in that the last line defines addition
(of `suc m` and `n`) in terms of addition (of `m` and `n`).

As with the inductive definition of the naturals, the apparent
circularity is not a problem.  It works because addition of larger
numbers is defined in terms of addition of smaller numbers.  For
example, let's add two and three.

       2 + 3
    =    { expand shorthand }
       (suc (suc zero)) + (suc (suc (suc zero)))
    =    { by the second equation, with m = suc zero and n = suc (suc (suc zero)) }
       suc ((suc zero) + (suc (suc (suc zero))))
    =    { by the second equation, with m = zero and n = suc (suc (suc zero)) }
       suc (suc (zero + (suc (suc (suc zero)))))
    =    { by the first equation, with n = suc (suc (suc zero)) }
       suc (suc (suc (suc (suc zero))))
    =    { compress shorthand }
       5

Or, more succintly,

       2 + 3
    =
       suc (1 + 3)
    =
       suc (suc (0 + 3))
    =
       suc (suc 3)
    =
       5



Indeed, the reasoning that justifies inductive and
recursive definitions is quite similar, and they might be considered
as two sides of the same coin.







## Equality on naturals is also an inductive datatype

## Proofs over naturals are also recursive functions


## Special characters

In each chapter, we will list all special characters used at the end.
In this chapter we use the following special characters.

    ℕ  U+2115:  DOUBLE-STRUCK CAPITAL N (\bN)  
    →  U+2192:  RIGHTWARDS ARROW (\to, \r) 
    ∀  U+2200:  FOR ALL (\forall)
    λ  U+03BB:  GREEK SMALL LETTER LAMBDA (\Gl, \lambda)
