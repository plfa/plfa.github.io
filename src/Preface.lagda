---
title     : "Preface"
layout    : page
permalink : /Preface
---

This book is an introduction to programming language theory, written
in Agda.  The authors are [Wen Kokke][wen] and [Philip Wadler][phil].

Please send us comments!  The text is currrently being drafted.  Part I
is ready for comment. We plan that Part II will be ready for comment
by the end of May.

Comments on all matters---organisation, material we should add,
material we should remove, parts that require better explanation, good
exercises, errors, and typos---are welcome.  Pull requests for small
fixes are encouraged.


## Personal remarks: From TAPL to PLTA

Since 2013, I have taught a course on Types and Semantics for
Programming Languages to fourth-year undergraduates and masters
students at the University of Edinburgh.  That course is not based on
Benjamin Pierce's excellent [TAPL][tapl], but on Pierce's subsequent
textbook, [Software Foundations][sf], written in collaboration with
others and based on Coq.  I am convinced of Pierce's claim that basing
a course around a proof assistant aids learning, as summarised in his
ICFP Keynote, [Lambda, The Ultimate TA][ta].

However, after five years of experience, I have come to the conclusion
that Coq may not be the best vehicle.  Too much of the course needs to
focus on learning tactics for proof derivation, to the cost of
learning the fundamentals of programming language theory.  Every
concept has to be learned twice: e.g., both the product data type, and
the corresponding tactics for introduction and elimination of
products.  The rules Coq applies to generate induction hypotheses can
sometimes seem mysterious.  While the `notation` construct permits
pleasingly flexible syntax, it can be confusing that the same concept
must always be given two names, e.g., both `subst N x M` and `N [x := M]`.
Names of tactics are sometimes short and sometimes long; naming
conventions in the standard library can be wildly inconsistent.
*Propositions as types* as a foundation of proof is present but
hidden.

I found myself keen to recast the course in Agda.  In Agda, there is
no longer any need to learn about tactics: there is just
dependently-typed programming, plain and simple. Introduction is
always by a constructor, elimination is always by pattern
matching. Induction is no longer a mysterious separate concept, but
corresponds to the familiar notion of recursion. Multifix syntax is flexible while
using just one name for each concept, e.g., substitution is
`_[_:=_]`. The standard library is not perfect, but there is a fair
attempt at consistency. *Propositions as types* as a foundation of
proof is on proud display.

Alas, there is no textbook for programming language theory in
Agda.  Stump's [Verified Functional Programming in Agda][stump] covers
related ground, but focusses more on programming with dependent
types than on the theory of programming languages.

The original goal was to simply adapt *Software Foundations*,
maintaining the same text but transposing the code from Coq to Agda.
But it quickly became clear to me that after five years in the
classroom I had my own ideas about how to present the material.  They
say you should never write a book unless you cannot *not* write the
book, and I soon found that this was a book I could not not write.

I am fortunate that my student, [Wen Kokke][wen], was keen to help.
They guided me as a newbie to Agda and provided an infrastructure that
is easy to use and produces pages that are a pleasure to view.

Most of the text was written during a sabbatical in the first half of 2018.

-- Philip Wadler, Rio de Janeiro, January--June 2018

[tapl]: http://www.cis.upenn.edu/~bcpierce/tapl/index.html
[sf]: https://softwarefoundations.cis.upenn.edu/
[ta]: http://www.cis.upenn.edu/~bcpierce/papers/plcurriculum.pdf
[stump]: http://www.morganclaypoolpublishers.com/catalog_Orig/product_info.php?cPath=24&products_id=908
[wen]: https://github.com/wenkokke
[phil]: http://homepages.inf.ed.ac.uk/wadler/

## A word on the exercises

Each exercise is followed by a name, which is the name you should use when
preparing an Agda file that solves the exercise.  Sometimes it is up to you to
work out the type of the identifier, but sometimes we give it in the exercise.
In some cases the type is bound to an identifier with a capital in its
name, where the identifier you are to define has a small letter instead.

