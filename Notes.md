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

