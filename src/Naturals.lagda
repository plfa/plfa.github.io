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

[This line added to test make]


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

    m : ℕ
    ---------
    suc m : ℕ

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

+ *Base case*: `zero` is a natural number.
+ *Inductive case*: if `m` is a natural number, then `suc m` is also a
  natural number.

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

**Exercise 1** Write out `7` in longhand.


## Unpacking the inference rules

Let's unpack the inference rules.  Each inference rule consists of
zero or more *judgments* written above a horizontal line, called the
*hypotheses*, and a single judgment written below, called the
*conclusion*.  The first rule is the base case. It has no hypotheses,
and the conclusion asserts that `zero` is a natural.  The second rule
is the inductive case. It has one hypothesis, which assumes that `m`
is a natural, and the conclusion asserts that `suc n` is a also a
natural.


## Unpacking the Agda definition

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

You may have notices that `ℕ` and `→` are don't appear on your
keyboard.  They are symbols in *unicode*.  At the end of each chapter
is a list of all the unicode used in the chapter, including
instructions on how to type them in the Emacs text editor using keys
that are on your keyboard.


## The story of creation

Let's look again at the rules that define the natural numbers:

+ *Base case*: `zero` is a natural number.
+ *Inductive case*: if `m` is a natural number, then `suc m` is also a
  natural number.

Wait a minute! The second line defines natural numbers
in terms of natural numbers. How can that posssibly be allowed?
Isn't this as meaningless as claiming "Brexit means Brexit"?

In fact, it is possible to assign our definition a meaning without
resorting to any unpermitted circularities.  Furthermore, we can do so
while only working with *finite* sets and never referring to the
entire *infinite* set of natural numbers.

We will think of it as a creation story.  To start with, we know about
no natural numbers at all.

    -- in the beginning, there are no natural numbers

Now, we apply the rules to all the natural numbers we know about.  The
base case tells us that `zero` is a natural number, so we add it to the set
of known natural numbers.  The inductive case tells us that if `m` is a
natural number (on the day before today) then `suc m` is also a
natural number (today).  We didn't know about any natural numbers
before today, so the inductive case doesn't apply.

    -- on the first day, there is one natural number   
    zero : ℕ

Then we repeat the process, so on the next day we know about all the
numbers from the day before, plus any numbers added by the rules.  The
base case tells us that `zero` is a natural number, but we already knew
that. But now the inductive case tells us that since `zero` was a natural
number yesterday, then `suc zero` is a natural number today.

    -- on the second day, there are two natural numbers
    zero : ℕ
    suc zero : ℕ

And we repeat the process again. Now the inductive case
tells us that since `zero` and `suc zero` are both natural numbers, then
`suc zero` and `suc (suc zero)` are natural numbers. We already knew about
the first of these, but the second is new.

    -- on the third day, there are three natural numbers
    zero : ℕ
    suc zero : ℕ
    suc (suc zero) : ℕ

You've probably got the hang of it by now.

    -- on the fourth day, there are four natural numbers
    zero : ℕ
    suc zero : ℕ
    suc (suc zero) : ℕ
    suc (suc (suc zero)) : ℕ

The process continues.  On the *n*th day there will be *n* distinct
natural numbers. Every natural number will appear on some given day.
In particular, the number *n* first appears on day *n+1*. And we
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


## Philosophy and history

A philosopher might observe that our reference to the first day,
second day, and so on, implicitly involves an understanding of natural
numbers.  In this sense, our definition might indeed be regarded as in
some sense circular.  We need not let this circularity disturb us.
Everyone possesses a good informal understanding of the natural
numbers, which we may take as a foundation for their formal
description.

While the natural numbers have been understood for as long as people
can count, the inductive definition of the natural numbers is relatively
recent.  It can be traced back to Richard Dedekind's paper "*Was sind
und was sollen die Zahlen?*" (What are and what should be the
numbers?), published in 1888, and Giuseppe Peano's book "*Arithmetices
principia, nova methodo exposita*" (The principles of arithmetic
presented by a new method), published the following year.


## A useful pragma

In Agda, any text following `--` or enclosed between `{-`
and `-}` is considered a *comment*.  Comments have no effect on the
code, with the exception of one special kind of comment, called a
*pragma*, which is enclosed between `{-#` and `#-}`.

Including the line
\begin{code}
{-# BUILTIN NATURAL ℕ #-}
\end{code}
tells Agda that `ℕ` corresponds to the natural numbers, and hence one
is permitted to type `0` as shorthand for `zero`, `1` as shorthand for
`suc zero`, `2` as shorthand for `suc (suc zero)`, and so on.  The
declaration is not permitted unless the type given has two constructors,
one corresponding to zero and one to successor.

As well as enabling the above shorthand, the pragma also enables a
more efficient internal representation of naturals as the Haskell type
integer.  Representing the natural *n* with `zero` and `suc`
requires space proportional to *n*, whereas representing it as an integer in
Haskell only requires space proportional to the logarithm of *n*.  In
particular, if *n* is less than 2⁶⁴, it will require just one word on
a machine with 64-bit words.


## Operations on naturals are recursive functions

Now that we have the natural numbers, what can we do with them?
For instance, can we define arithmetic operations such as
addition and multiplication?

As a child I spent much time memorising tables of addition and
multiplication.  At first the rules seemed tricky and I would often
make mistakes.  So it came as a shock to me to realise that all of addition
and multiplication can be precisely defined in just a couple of lines.

Here is the definition of addition in Agda:
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero    + n  =  n                -- (i)
(suc m) + n  =  suc (m + n)      -- (ii)
\end{code}

Let's unpack this definition.  Addition is an infix operator.  It is
written with underbars where the arguement go, hence its name is
`_+_`.  It's type, `ℕ → ℕ → ℕ`, indicates that it accepts two naturals
and returns a natural.  There are two ways to construct a natural,
with `zero` or with `suc`, so there are two lines defining addition,
labeled with comments as (i) and (ii).  Line (i) says that
adding zero to a number (`zero + n`) returns that number (`n`). Line
(ii) says that adding the successor of a number to another number
(`(suc m) + n`) returns the successor of adding the two numbers (`suc
(m+n)`).  We say we are using *pattern matching* when we use a
constructor applied to a term as an argument, such as `zero` in (i)
or `(suc m)` in (ii).

If we write `zero` as `0` and `suc m` as `1 + m`, we get two familiar equations.

   0       + n  =  n
   (1 + m) + n  =  1 + (m + n)

The first follows because zero is a left identity for addition,
and the second because addition is associative.  In its most general
form, associativity is written

   (m + n) + p  =  m + (n + p)

meaning that the order of parentheses is irrelevant.  We get the
second equation from this one by taking `m` to be `1`, `n` to be `m`,
and `p` to be `n`.

The definition is *recursive*, in that the last line defines addition
in terms of addition.  As with the inductive definition of the
naturals, the apparent circularity is not a problem.  It works because
addition of larger numbers is defined in terms of addition of smaller
numbers.  Such a definition is called *well founded*.

For example, let's add two and three.

       2 + 3
    =    (is shorthand for)
       (suc (suc zero)) + (suc (suc (suc zero)))
    =    (ii)
       suc ((suc zero) + (suc (suc (suc zero))))
    =    (ii)
       suc (suc (zero + (suc (suc (suc zero)))))
    =    (i)
       suc (suc (suc (suc (suc zero))))
    =    (is longhand for)
       5

We can write this more compactly by only expanding shorthand as needed.

       2 + 3
    =    (ii)
       suc (1 + 3)
    =    (ii)
       suc (suc (0 + 3))
    =    (i)
       suc (suc 3)
    =    
       5

The first use of (ii) matches by taking `m = 1` and `n = 3`,
The second use of (ii) matches by taking `m = 0` and `n = 3`,
and the use of (i) matches by taking `n = 3`.

**Exercise** Compute `3 + 4` by the same technique.


## Multiplication

Once we have defined addition, we can define multiplication
as repeated addition.
\begin{code}
_*_ : ℕ → ℕ → ℕ
zero * n     =  zero           -- (iii)
(suc m) * n  =  n + (m * n)    -- (iv)
\end{code}

Again, rewriting gives us two familiar equations.

  0       * n  =  0
  (1 + m) * n  =  n + (m * n)

The first follows because zero times anything is zero,
and the second follow because multiplication distributes
over addition.  In its most general form, distribution of
multiplication over addition is written

  (m + n) * p  =  (m * p) + (n * p)

We get the second equation from this one by taking `m` to be `1`, `n`
to be `m`, and `p` to be `n`, and then using the fact that one is a
left identity for multiplication, so `1 * n = n`.

Again, the definition is well-founded in that multiplication of
larger numbers is defined in terms of multiplication of smaller numbers.
 
For example, let's multiply two and three.

       2 * 3
    =    (iv)
       3 + (1 * 3)
    =    (iv)
       3 + (3 + (0 * 3))
    =    (iii)
       3 + (3 + 0)
    =
       6

The first use of (iv) matches by taking `m = 1` and `n = 3`,
The second use of (iv) matches by taking `m = 0` and `n = 3`,
and the use of (iii) matches by taking `n = 3`.

**Exercise** Compute `3 * 4` by the same technique.


## Exponentiation

Similarly, once we have defined multiplication, we can define
exponentiation as repeated multiplication.
\begin{code}
_^_ : ℕ → ℕ → ℕ
n ^ zero     =  suc zero       -- (v)
n ^ (suc m)  =  n * (n ^ m)    -- (vi)
\end{code}

**Exercise** Compute `4 ^ 3`.


## Monus

We can also define subtraction.  Since there are no negative
natural numbers, if we subtract a larger number from a smaller
number we will take the result to be zero.  This adaption of
subtraction to naturals is called *monus* (as compared to *minus*).

Monus is our first example of a definition that uses pattern
matching against both arguments.
\begin{code}
_∸_ : ℕ → ℕ → ℕ
m       ∸ zero     =  m         -- (vii)
zero    ∸ (suc n)  =  zero      -- (viii)
(suc m) ∸ (suc n)  =  m ∸ n     -- (ix)
\end{code}
We can do a simple analysis to show that all the cases are covered.

  * The second argument is either `zero` or `suc n` for some `n`.
    + If it is `zero`, then equation (vii) applies.
    + If it is `suc n`, then the first argument is either `zero`
      or `suc m` for some `m`.
      - If it is `zero`, then equation (viii) applies.
      - If it is `suc m`, then equation (ix) applies.

Again, the recursive definition is well-founded because
monus on bigger numbers is defined in terms of monus on
small numbers.

For example, let's subtract two from three.

       3 ∸ 2
    =    (ix)
       2 ∸ 1
    =    (ix)
       1 ∸ 0
    =    (vii)
       1

We did not use equation (viii) at all, but it will be required
if we try to subtract a smaller number from a larger one.

       2 ∸ 3
    =    (ix)
       1 ∸ 2
    =    (ix)
       0 ∸ 1
    =    (viii)
       0

**Exercise** Compute `5 ∸ 3` and `3 ∸ 5` by the same technique.

## The story of creation, revisited

As with the definition of the naturals by induction, in the definition
of addition by recursion we have defined addition in terms of addition.

Again, it is possible to assign our definition a meaning without
resorting to unpermitted circularities.  We do so by reducing our
definition to equivalent inference rules for judgements about equality.

    ------------
    zero + n = n

    m + n = p
    -------------------
    (suc m) + n = suc p

Here we assume we have already defined the infinite set of natural
numbers, specifying the meaning of the judgment `n : ℕ`.  The first
inference rule is the base case, and corresponds to line (i) of the
definition.  It asserts that if `n` is a natural number then adding
zero to it gives `n`.  The second inference rule is the inductive
case, and corresponds to line (ii) of the definition. It asserts that
if adding `m` and `n` gives `p`, then adding `suc m` and `n` gives
`suc p`.

Again we resort to a creation story, where this time we are
concerned with judgements about addition.

    -- in the beginning, we know nothing about addition

Now, we apply the rules to all the judgment we know about.
The base case tells us that `zero + n = n` for every natural `n`,
so we add all those equations.  The inductive case tells us that if
`m + n = p` (on the day before today) then `suc m + n = suc p`
(today).  We didn't know any equations about addition before today,
so that rule doesn't give us any new equations.

    -- on the first day, we know about addition of 0
    0 + 0 = 0     0 + 1 = 1    0 + 2 = 2     ...

Then we repeat the process, so on the next day we know about all the
equations from the day before, plus any equations added by the rules.
The base case tells us nothing new, but now the inductive case adds
more equations.

    -- on the second day, we know about addition of 0 and 1
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...

And we repeat the process again.  

    -- on the third day, we know about addition of 0, 1, and 2
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
    2 + 0 = 2     2 + 1 = 3     2 + 2 = 4     2 + 3 = 5     ...

You've probably got the hang of it by now.

    -- on the fourth day, we know about addition of 0, 1, 2, and 3
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
    2 + 0 = 2     2 + 1 = 3     2 + 2 = 4     2 + 3 = 5     ...
    3 + 0 = 3     3 + 1 = 4     3 + 2 = 5     3 + 3 = 6     ...

The process continues.  On the *m*th day we will know all the
equations where the first number is less than *m*.

As we can see, the reasoning that justifies inductive and recursive
definitions is quite similar.  They might be considered two sides of
the same coin.


## Precedence

We often use *precedence* to avoid writing too many parentheses.
Application *binds more tightly than* (or *has precedence over*) any
operator, and so we may write `suc m + n` to mean `(suc m) + n`.
As another example, we say that multiplication binds more tightly than
addition, and so write `n + m * n` to mean `n + (m * n)`.
We also sometimes say that addition is *associates to the left*, and
so write `m + n + p` to mean `(m + n) + p`.

In Agda the precedence and associativity of infix operators
needs to be declared.
\begin{code}
infixl 7  _*_
infixl 6  _+_  _∸_
\end{code}
This states that operator `_*_` has precedence level 7, and that
operators `_+_` and `_∸_` have precedence level 6.  Multiplication
binds more tightly that addition or subtraction because it has a
higher precedence.  Writing `infixl` indicates that all three
operators associate to the left.  One can also write `infixr` to
indicate that an operator associates to the right, or just `infix` to
indicate that it has no associativity and parentheses are always
required to disambiguate.

## More pragmas

Inluding the lines
\begin{code}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}
\end{code}
tells Agda that these three operators correspond to the usual ones,
and enables it to perform these computations using the corresponing
Haskell operators on the integer type.  Representing naturals with
`zero` and `suc` requires time proportional to *m* to add *m* and *n*,
whereas representing naturals as integers in Haskell requires time
proportional to the larger of the logarithms of *m* and *n*.  In
particular, if *m* and *n* are both less than 2⁶⁴, it will require
constant time on a machine with 64-bit words.  Similarly, representing
naturals with `zero` and `suc` requires time proportional to the
product of *m* and *n* to multiply *m* and *n*, whereas representing
naturals as integers in Haskell requires time proportional to the sum
of the logarithms of *m* and *n*.

## Unicode

In each chapter, we will list at the end all unicode characters that
first appear in that chapter.  This chapter introduces the following
unicode.

    ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)  
    →  U+2192  RIGHTWARDS ARROW (\to, \r)
    ∸  U+2238  DOT MINUS (\.-)

Each line consists of the Unicode character (ℕ), the corresponding
code point (U+2115), the name of the character (DOUBLE-STRUCK CAPITAL N),
and the sequence to type into Emacs to generate the character (\bN).

The command \r is a little different to the others, because it gives
access to a wide variety of Unicode arrows.  After typing \r, one can access
the many available arrows by using the left, right, up, and down
keys on the keyboard to navigate.
