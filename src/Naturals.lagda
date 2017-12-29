---
title     : "Naturals: Natural numbers"
layout    : page
permalink : /Naturals
---

## The naturals are an inductive datatype

Our first example of an inductive datatype is ℕ, the natural numbers.
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
\end{code}
Here `ℕ` is the name of the *datatype* we are creating,
and `zero` and `suc` (short for *successor*) are the
*constructors* of the datatype.

### Inductive datatypes in detail

Let's unpack this definition. The keyword `data` tells us this is an
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

Here `ℕ` and `→` are special symbols, meaning that you won't find them
on your keyboard. At the end of each chapter is a list of all the
special symbols, including instructions on how to type them in the
Emacs text editor.

### How inductive datatypes work

The values of type `ℕ` are called natural numbers.
The two lines defining constructors tell us the following:

1. The term `zero` is a natural number.
2. If `n` is a natural number, then `suc n` is also a natural number.

Hence, the possible natural numbers are

    zero
    suc zero
    suc (suc zero)
    suc (suc (suc zero))

and so on.

This definition is *recursive* in that it defines the concept of
"natural number" in terms of the concept of "natural number". How can
this possibly be a sensible thing to do?  One way to think of this is
as a creation story.  To start with, we know about no natural numbers
at all.

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

The process continues. On the *n*th day there will be *n* distinct
natural numbers. Note that in this way, we only talk about finite sets
of numbers. Every number will appear on some given finite day. In
particular, the number *n* first appears on day *n+1*. And we never
actually define the set of numbers in terms of itself. Instead, we define
the set of numbers on day *n+1* in terms of the set of numbers on day *n*.

A process like this one is called *inductive*. We start with nothing, and
build up a potentially infinite set by applying rules that convert one
finite set into another finite set.


### Pragmas

\begin{code}
{-# BUILTIN NATURAL ℕ #-}
\end{code}

## Operations on naturals are recursive functions

## Equality on naturals is also an inductive datatype

## Proofs over naturals are also recursive functions


## Special characters

In each chapter, we will list all special characters used at the end.
In this chapter we use the following special characters.

    ℕ  U+2115:  DOUBLE-STRUCK CAPITAL N (\bN)  
    →  U+2192:  RIGHTWARDS ARROW (\to, \r) 
    ∀  U+2200:  FOR ALL (\forall)
    λ  U+03BB:  GREEK SMALL LETTER LAMBDA (\Gl, \lambda)
