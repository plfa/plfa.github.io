---
layout: page
title: Notes
permalink: /Notes/
---

## Downloading older versions

<https://github.com/plfa/plfa.github.io/releases>

## Google Analytics

<https://analytics.google.com/analytics/web/>

## Git commands

Git commands to create a branch and pull request

    git help <command>          -- get help on <command>
    git branch                  -- list all branches
    git branch <name>           -- create new local branch <name>
    git checkout <name>         -- make <name> the current branch
    git merge <name>            -- merge branch <name> into current branch 
    git push origin <name>      -- make local branch <name> into remote

On website, use pulldown menu to swith branch and then
click "new pull request" button.

## Suggestion from Conor for Inference

Conor McBride <conor.mcbride@strath.ac.uk>
	
29 Oct 2018, 09:34
	
Hi Phil

In a rush, but...

    data Tag : Set where
      tag-ℕ : Tag
      tag-⇒ : Tag

...that's just Bool. Bool is almost never your friend.

Get evidence!

    -- yer types
    data Type : Set where
      nat : Type
      _=>_ : Type -> Type -> Type

    -- logic
    data Zero : Set where
    record One : Set where constructor <>

    -- evidence of not being =>
    Not=> : Type -> Set
    Not=> (_ => _) = Zero
    Not=> _ = One

    -- constructing the "=> or not" view
    data Is=>? : Type -> Set where
      is=> : (S T : Type) -> Is=>? (S => T)
      not=> : {T : Type} -> Not=> T -> Is=>? T

    -- this will need all n cases, but you do it once
    is=>? : (T : Type) -> Is=>? T
    is=>? nat = not=> <>
    is=>? (S => T) = is=> _ _

    -- worked example: domain
    data Maybe (X : Set) : Set where
      yes : X -> Maybe X
      no : Maybe X

    -- only two cases
    dom : Type -> Maybe Type
    dom T with is=>? T
    dom .(S => T) | is=> S T = yes S
    dom T | not=> p = no

    -- addendum: in the not=> p case, if we subsequently inspect T, we can rule out the => case using p
    {- with T
    dom T | not=> p | nat = no
    dom T | not=> () | q => q₁
    -}


> We want to alert you that you've been granted the following access:
>      Manage Users and Edit
> to the Google Analytics account `plfa (UA-125055580)` by `wen.kokke@gmail.com`.

> [Google analytics](https://analytics.google.com/analytics/web/)

## Where to put Lists?

Three possible orders:
  + (a) As current
  + (b) Put Lists immediately after Induction.
    - requires moving composition & extensionality earlier
	- requires moving parameterised modules earlier for monoids
    - add material to relations:
	  lexical ordering, subtype ordering, All, Any, All-++ iff
    - add material to isomorphism: All-++ isomorphism
	- retain material on decidability of All, Any in Decidable
  + (c) Put Lists after Decidable
    - requires moving Any-decidable from Decidable to Lists
  + (d) As (b) but put parameterised modules in a separate chapter

Tradeoffs:
  + (b) Distribution of exercises near where material is taught
  + (b) Additional reinforcement for simple proofs by induction
  + (a,c) Can drop material if there is lack of time
  + (a,c) Earlier emphasis on induction over evidence	
  + (c) More consistent structuring principle

## Set up lists of exercises to do

* Use md rather than HTML
* Tell students to do _all_ exercises, and just mark some as stretch?
* Make a list of exercises to do, with some marked as stretch?
* Compare with previous set of exercises to discover some holes?
* Add ==N as an exercise to Relations?

## Other questions

* Resolve any issues with modules to define properties of orderings?
* Resolve any issues with equivalence and Setoids?

# Old questions

## Possible structures for the book

* One possible development
  + raw terms
  + scoped terms (is conversion from raw to scoped a function?)
  + typed terms (via bidirectional typing)

* The above could be developed either for
  + pure lambda terms with full normalisation
  + PCF with top-level reduction to value

* If I follow raw-scoped-typed then:
  + might want to have reductions for completely raw terms
    later in the book rather than earlier
  + full normalisation requires substitution of open terms

* Today's task (Tue 8 May)
  + consider lambda terms to values (not PCF)
  + raw, scoped, typed

  + Note that substitution for open terms is not hard,
    it is proving it correct that is difficult!
  + can put each development in a separate module
    to support reuse of names

* Today's thoughts (Thu 10 May)
  + simplify TypedFresh
    - Does it become easier once I have
      suitable lemmas about free in place?
  + still need a chain of development
    - raw -> scoped -> typed
    - raw -> typed and typed -> raw needed for examples
    - look again at raw to scoped
    - look at scoped to typed
    - typed to raw requires fresh names
    - fresh name strategy: primed or numbers?
    - ops on strings: show, read, strip from end
  + trickier ideas
    - factor TypedFresh into Barendregt followed
      by substitution? This might actually lead
      to a much longer development
    - would be cool if Barendregt never required
      renaming in case of substitution by closed
      terms, but I think this is hard

* Today's achievements and next steps (Thu 10 May)
  + defined break, make to extract a prefix
    and count primes at end of an id.  But hard
    to do corresponding proofs.  Need to figure out
	how to exploit abstraction to make terms readable.
  + Conversion of raw to scoped and scoped to raw
	is easy if I use impossible 
  + Added conversion of TypedDB to PHOAS in
    extra/DeBruijn-agda-list-4.lagda
  + Next: try adding bidirectional typing to
    convert Raw or Scoped to TypedDB
  + Next: Can proofs in Typed be simplified by
    applying suitable lemmas about free?
  + updated Agda from:
      Agda version 2.6.0-4654bfb-dirty
    to:
      Agda version 2.6.0-2f2f4f5 
    Now TypedFresh.lagda computes 2+2 in milliseconds
    (as opposed to failing to compute it in one day).


## STLC

* Russel O'Connor
  + STLC with recursive types, intrinsic representation
    - https://hub.darcs.net/roconnor/STLC/browse/src/STLC


## PHOAS

The following comments were collected on the Agda mailing list.

* Nils Anders Danielsson <nad@cse.gu.se>
  + cites Chlipala, who uses binary parametricity
    - http://adam.chlipala.net/cpdt/html/Cpdt.ProgLang.html 
    - http://adam.chlipala.net/cpdt/html/Intensional.html

* Roman <effectfully@gmail.com>
  + (similar to my solution)
    - https://github.com/effectfully/random-stuff/blob/master/Normalization/PHOAS.agda
    - https://github.com/effectfully/random-stuff/blob/master/Normalization/Liftable.agda
  + also cites Abel's habilitation
    -  http://www.cse.chalmers.se/~abela/habil.pdf
  + See his note to the Agda mailing list of 26 June,
	"Typed Jigger in vanilla Agda"
    It points to the following solution.
    - https://github.com/effectfully/random-stuff/blob/master/TypedJigger.agda

* András Kovács <kovacsahun@hotmail.com>
  + applies unary parametricity
    - http://lpaste.net/363029

* Ulf Norell <ulf.norell@gmail.com>
  + helped with deriving Eq

* David Darais (not on mailing list)
  + suggests Scoped PHOAS
    - https://plum-umd.github.io/darailude-agda/SF.PHOAS.html

## Untyped lambda calculus

* Nils Anders Danielsson <nad@cse.gu.se>
  +
  http://www.cse.chalmers.se/~nad/listings/partiality-monad/Lambda.Simplified.Delay-monad.Interpreter.html
  + /~nad/repos/codata/Lambda/Closure/Functional
* untyped lambda calculus by Gallais
  + https://gist.github.com/gallais/303cfcfe053fbc63eb61
* lambda calculus
  + https://github.com/pi8027/lambda-calculus/tree/master/agda/Lambda

## Relevant papers

* Kenichi Asai, Extracting a Call-by-Name Partial Evaluator from a Proof of
  Termination, PEPM 2019
  + http://pllab.is.ocha.ac.jp/~asai/papers/pepm19.pdf
  + http://pllab.is.ocha.ac.jp/~asai/papers/pepm2019/
* Kenichi Asai, Certifying CPS Transformation of Let-Polymorphic
  Calculus Using PHOAS, APLAS 2018
  + https://link.springer.com/chapter/10.1007/978-3-030-02768-1_20
  + http://pllab.is.ocha.ac.jp/~asai/papers/aplas18.agda


## Agda resources
* Chalmers class
  + http://www.cse.chalmers.se/edu/year/2017/course/DAT140_Types/
* Dybjer lecture notes
  + http://www.cse.chalmers.se/edu/year/2017/course/DAT140_Types/LectureNotes.pdf
* Ulf Norell and James Chapman lecture notes
  + http://www.cse.chalmers.se/~ulfn/darcs/AFP08/LectureNotes/AgdaIntro.pdf
* Chalmer Take Home exam 2017
  + http://www.cse.chalmers.se/edu/year/2017/course/DAT140_Types/TakeHomeExamTypes2017.pdf

## Syntax for lambda calculus

* ƛ \Gl-
* ∙ \.

