---
title     : "Basics: Functional Programming in Agda"
layout    : page
permalink : /Basics
---

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}

The functional programming style brings programming closer to
simple, everyday mathematics: If a procedure or method has no side
effects, then (ignoring efficiency) all we need to understand
about it is how it maps inputs to outputs -- that is, we can think
of it as just a concrete method for computing a mathematical
function.  This is one sense of the word "functional" in
"functional programming."  The direct connection between programs
and simple mathematical objects supports both formal correctness
proofs and sound informal reasoning about program behavior.

The other sense in which functional programming is "functional" is
that it emphasizes the use of functions (or methods) as
_first-class_ values -- i.e., values that can be passed as
arguments to other functions, returned as results, included in
data structures, etc.  The recognition that functions can be
treated as data in this way enables a host of useful and powerful
idioms.

Other common features of functional languages include _algebraic
data types_ and _pattern matching_, which make it easy to
construct and manipulate rich data structures, and sophisticated
_polymorphic type systems_ supporting abstraction and code reuse.
Agda shares all of these features.

This chapter introduces the most essential elements of Agda.

## Enumerated Types

One unusual aspect of Agda is that its set of built-in
features is _extremely_ small. For example, instead of providing
the usual palette of atomic data types (booleans, integers,
strings, etc.), Agda offers a powerful mechanism for defining new
data types from scratch, from which all these familiar types arise
as instances.

Naturally, the Agda distribution comes with an extensive standard
library providing definitions of booleans, numbers, and many
common data structures like lists and hash tables.  But there is
nothing magic or primitive about these library definitions.  To
illustrate this, we will explicitly recapitulate all the
definitions we need in this course, rather than just getting them
implicitly from the library.

To see how this definition mechanism works, let's start with a
very simple example.

### Days of the Week

The following declaration tells Agda that we are defining
a new set of data values -- a _type_.

\begin{code}
data Day : Set where
  monday    : Day
  tuesday   : Day
  wednesday : Day
  thursday  : Day
  friday    : Day
  saturday  : Day
  sunday    : Day
\end{code}

The type is called `day`, and its members are `monday`,
`tuesday`, etc.  The second and following lines of the definition
can be read "`monday` is a `day`, `tuesday` is a `day`, etc."

Having defined `day`, we can write functions that operate on
days.

\begin{code}
nextWeekday : Day -> Day
nextWeekday monday    = tuesday
nextWeekday tuesday   = wednesday
nextWeekday wednesday = thursday
nextWeekday thursday  = friday
nextWeekday friday    = monday
nextWeekday saturday  = monday
nextWeekday sunday    = monday
\end{code}

One thing to note is that the argument and return types of
this function are explicitly declared.  Like most functional
programming languages, Agda can often figure out these types for
itself when they are not given explicitly -- i.e., it performs
_type inference_ -- but we'll include them to make reading
easier.

Having defined a function, we should check that it works on
some examples. There are actually three different ways to do this
in Agda.

First, we can use the Emacs command `C-c C-n` to evaluate a
compound expression involving `nextWeekday`. For instance, `nextWeekday
friday` should evaluate to `monday`. If you have a computer handy, this
would be an excellent moment to fire up Agda and try this for yourself.
Load this file, `Basics.lagda`, load it using `C-c C-l`, submit the
above example to Agda, and observe the result.

Second, we can record what we _expect_ the result to be in the
form of an Agda type:

\begin{code}
test-nextWeekday : nextWeekday (nextWeekday saturday) ≡ tuesday
\end{code}

This declaration does two things: it makes an assertion (that the second
weekday after `saturday` is `tuesday`), and it gives the assertion a name
that can be used to refer to it later.

Having made the assertion, we must also verify it. We do this by giving
a term of the above type:

\begin{code}
test-nextWeekday = refl
\end{code}

There is no essential difference between the definition for
`test-nextWeekday` here and the definition for `nextWeekday` above,
except for the new symbol for equality `≡` and the constructor `refl`.
The details of these are not important for now (we'll come back to them in
a bit), but essentially `refl` can be read as "The assertion we've made
can be proved by observing that both sides of the equality evaluate to the
same thing, after some simplification."

Third, we can ask Agda to _compile_ some program involving our definition,
This facility is very interesting, since it gives us a way to construct
_fully certified_ programs. We'll come back to this topic in later chapters.
