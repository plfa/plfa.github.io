# Notes

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

