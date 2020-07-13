---
title          : Table of Contents
layout         : page
---

This book is an introduction to programming language theory using the
proof assistant Agda.

Comments on all matters---organisation, material to add, material to
remove, parts that require better explanation, good exercises, errors,
and typos---are welcome.  The book repository is on [GitHub].
Pull requests are encouraged.

## Front matter

  - [Dedication]({{ site.baseurl }}/Dedication/)
  - [Preface]({{ site.baseurl }}/Preface/)

## Part 1: Logical Foundations

  - [Naturals]({{ site.baseurl }}/Naturals/): Natural numbers
  - [Induction]({{ site.baseurl }}/Induction/): Proof by induction
  - [Relations]({{ site.baseurl }}/Relations/): Inductive definition of relations
  - [Equality]({{ site.baseurl }}/Equality/): Equality and equational reasoning
  - [Isomorphism]({{ site.baseurl }}/Isomorphism/): Isomorphism and embedding
  - [Connectives]({{ site.baseurl }}/Connectives/): Conjunction, disjunction, and implication
  - [Negation]({{ site.baseurl }}/Negation/): Negation, with intuitionistic and classical logic
  - [Quantifiers]({{ site.baseurl }}/Quantifiers/): Universals and existentials
  - [Decidable]({{ site.baseurl }}/Decidable/): Booleans and decision procedures
  - [Lists]({{ site.baseurl }}/Lists/): Lists and higher-order functions

## Part 2: Programming Language Foundations

  - [Lambda]({{ site.baseurl }}/Lambda/): Introduction to Lambda Calculus
  - [Properties]({{ site.baseurl }}/Properties/): Progress and Preservation
  - [DeBruijn]({{ site.baseurl }}/DeBruijn/): Intrinsically-typed de Bruijn representation
  - [More]({{ site.baseurl }}/More/): Additional constructs of simply-typed lambda calculus
  - [Bisimulation]({{ site.baseurl }}/Bisimulation/): Relating reductions systems
  - [Inference]({{ site.baseurl }}/Inference/): Bidirectional type inference
  - [Untyped]({{ site.baseurl }}/Untyped/): Untyped lambda calculus with full normalisation
  - [Confluence]({{ site.baseurl }}/Confluence/): Confluence of untyped lambda calculus
  - [BigStep]({{ site.baseurl }}/BigStep/): Big-step semantics of untyped lambda calculus

## Part 3: Denotational Semantics

  - [Denotational]({{ site.baseurl }}/Denotational/): Denotational semantics of untyped lambda calculus
  - [Compositional]({{ site.baseurl }}/Compositional/): The denotational semantics is compositional
  - [Soundness]({{ site.baseurl }}/Soundness/): Soundness of reduction with respect to denotational semantics
  - [Adequacy]({{ site.baseurl }}/Adequacy/): Adequacy of denotational semantics with respect to operational semantics
  - [ContextualEquivalence]({{ site.baseurl }}/ContextualEquivalence/): Denotational equality implies contextual equivalence

## Appendix

  - [Substitution]({{ site.baseurl }}/Substitution/): Substitution in untyped lambda calculus


## Backmatter

  - [Acknowledgements]({{ site.baseurl }}/Acknowledgements/)
  - [Fonts]({{ site.baseurl }}/Fonts/): Test page for fonts
  - [Statistics]({{ site.baseurl }}/Statistics/): Line counts for each chapter

## Related

  - Mailing lists for PLFA:
    * [plfa-interest@inf.ed.ac.uk](http://lists.inf.ed.ac.uk/mailman/listinfo/plfa-interest): <br />
      A mailing list for users of the book. <br />
      This is the place to ask and answer questions, or comment on the content of the book.
    * [plfa-dev@inf.ed.ac.uk](http://lists.inf.ed.ac.uk/mailman/listinfo/plfa-dev): <br />
      A mailing list for contributors. <br />
      This is the place to discuss changes and new additions to the book in excruciating detail.
  - Courses taught from the textbook (please tell us of others):
    * Philip Wadler, University of Edinburgh,
      [2018]({{ site.baseurl }}/TSPL/2018/),
	  [2019]({{ site.baseurl }}/TSPL/2019/)
    * David Darais, University of Vermont,
      [2018][UVM-2018]
    * John Leo, Google Seattle, 2018--2019
    * Philip Wadler, Pontifícia Universidade Católica do Rio de Janeiro (PUC-Rio),
      [2019]({{ site.baseurl }}/PUC/2019/)
    * Prabhakar Ragde, University of Waterloo,
	  [2019][UW-2019]
    * Adrian King,
      San Francisco Types, Theorems, and Programming Languages Meetup
      [2019--2020][SFPL-Meetup-2020]
    * Dan Ghica, University of Birmingham
	  [2019][BHAM-2019]
    * Jeremy Siek, Indiana University,
	  [2020][IU-2020]
    * William Cook, University of Texas,
	  [2020][UT-2020]
  - Shortlisted for Outstanding Course by Edinburgh University Student
    Association (second place) [2020][EUSA-2020]
    * "Types and Semantics for Programming Languages was the single
      best course I took throughout my time at the University of
      Edinburgh. Philip Wadler clearly poured his heart into teaching
      it, including writing a whole textbook including exercises
      specifically for the course."
    * "One of the most inspiring courses. Philip designed a course
      that is both very theoretical and very practical."
  - A paper describing the book appeared in [SBMF][SBMF] and [SCP][SCP].
  - [NextJournal][NextJournal] has built a notebook version of PLFA, which lets you edit and execute the book via a web interface.

[GitHub]: https://github.com/plfa/plfa.github.io/
[UVM-2018]: https://web.archive.org/web/20190324115921/http://david.darais.com/courses/fa2018-cs295A/
[IU-2020]: https://jsiek.github.io/B522-PL-Foundations/
[SFPL-Meetup-2020]: http://meet.meetup.com/wf/click?upn=ZDzXt-2B-2BZmzYir6Bq5X7vEQ2iNYdgjN9-2FU9nWKp99AU8rZjrncUsSYODqOGn6kV-2BqW71oirCo-2Bk8O1q2FtDFhYZR-2B737CPhNWBjt58LuSRC-2BWTj61VZCHquysW8z7dVtQWxB5Sorl3chjZLDptP70L7aBZL14FTERnKJcRQdrMtc-3D_IqHN4t3hH47BvE1Cz0BakIxV4odHudhr6IVs-2Fzslmv-2FBuORsh-2FwQmOxMBdyMHsSBndQDQmt47hobqsLp-2Bm04Y9LwgV66MGyucsd0I9EgDEUB-2FjzdtSgRv-2Fxng8Pgsa3AZIEYILOhLpQ5ige5VFYTEHVN1pEqnujCHovmTxJkqAK9H-2BIL15-2FPxx97RfHcz7M30YNyqp6TOYfgTxyUHc6lufYKFA75Y7MV6MeDJMxw9-2FYUxR6CEjdoagQBmaGkBVzN
[UW-2019]: https://cs.uwaterloo.ca/~plragde/842/
[UT-2020]: https://www.cs.utexas.edu/~wcook/Courses/386L/Sp2020-GradPL.pdf
[BHAM-2019]: https://www.cs.bham.ac.uk/internal/modules/2019/06-26943/
[EUSA-2020]: https://www.eusa.ed.ac.uk/representation/campaigns/teachingawards2020/
[SBMF]: https://homepages.inf.ed.ac.uk/wadler/topics/agda.html#sbmf
[SCP]: https://homepages.inf.ed.ac.uk/wadler/topics/agda.html#scf
[NextJournal]: https://nextjournal.com/plfa/ToC
