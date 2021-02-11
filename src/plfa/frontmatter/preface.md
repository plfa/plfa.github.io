---
title     : "Preface"
layout    : page
prev      : /Dedication/
permalink : /Preface/
next      : /GettingStarted/
---

The most profound connection between logic and computation is a pun.
The doctrine of Propositions as Types asserts that a certain kind of
formal structure may be read in two ways: either as a proposition in
logic or as a type in computing.  Further, a related structure may be
read as either the proof of the proposition or as a programme of the
corresponding type.  Further still, simplification of proofs
corresponds to evaluation of programs.

Accordingly, the title of this book also has two readings.  It may be
parsed as "(Programming Language) Foundations in Agda" or "Programming
(Language Foundations) in Agda" — the specifications we will write in
the proof assistant Agda both describe programming languages and are
themselves programmes.

The book is aimed at students in the last year of an undergraduate
honours programme or the first year of a master or doctorate degree.
It aims to teach the fundamentals of operational semantics of
programming languages, with simply-typed lambda calculus as the
central example.  The textbook is written as a literate script in
Agda.  The hope is that using a proof assistant will make the
development more concrete and accessible to students, and give them
rapid feedback to find and correct misapprehensions.

The book is broken into two parts. The first part, Logical
Foundations, develops the needed formalisms.  The second part,
Programming Language Foundations, introduces basic methods of
operational semantics.

## Personal remarks

Since 2013, I have taught a course on Types and Semantics for
Programming Languages to fourth-year undergraduates and masters
students at the University of Edinburgh.  An earlier version of that
course was based on Benjamin Pierce's excellent [TAPL][tapl].  My
version was based of Pierce's subsequent textbook, [Software
Foundations][sf], written in collaboration with others and based on
Coq.  I am convinced of Pierce's claim that basing a course around a
proof assistant aids learning, as summarised in his ICFP Keynote,
[Lambda, The Ultimate TA][ta].

However, after five years of experience, I have come to the conclusion
that Coq is not the best vehicle.  Too much of the course needs to
focus on learning tactics for proof derivation, to the cost of
learning the fundamentals of programming language theory.  Every
concept has to be learned twice: e.g., both the product data type, and
the corresponding tactics for introduction and elimination of
conjunctions.  The rules Coq applies to generate induction hypotheses
can sometimes seem mysterious.  While the `notation` construct permits
pleasingly flexible syntax, it can be confusing that the same concept
must always be given two names, e.g., both `subst N x M` and `N [x :=
M]`.  Names of tactics are sometimes short and sometimes long; naming
conventions in the standard library can be wildly inconsistent.
*Propositions as types* as a foundation of proof is present but
hidden.

I found myself keen to recast the course in Agda.  In Agda, there is
no longer any need to learn about tactics: there is just
dependently-typed programming, plain and simple. Introduction is
always by a constructor, elimination is always by pattern
matching. Induction is no longer a mysterious separate concept, but
corresponds to the familiar notion of recursion. Mixfix syntax is
flexible while using just one name for each concept, e.g.,
substitution is `_[_:=_]`. The standard library is not perfect, but
there is a fair attempt at consistency. *Propositions as types* as a
foundation of proof is on proud display.

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
She guided me as a newbie to Agda and provided an infrastructure that
is easy to use and produces pages that are a pleasure to view.

Most of the text was written during a sabbatical in the first half of 2018.

— Philip Wadler, Rio de Janeiro, January–June 2018

[tapl]: https://www.cis.upenn.edu/~bcpierce/tapl/
[sf]: https://softwarefoundations.cis.upenn.edu/
[ta]: https://www.cis.upenn.edu/~bcpierce/papers/plcurriculum.pdf
[stump]: https://www.morganclaypoolpublishers.com/catalog_Orig/product_info.php?cPath=24&products_id=908
[wen]: https://github.com/wenkokke
[phil]: https://homepages.inf.ed.ac.uk/wadler/

## A word on the exercises

Exercises labelled "(recommended)" are the ones students are
required to do in the class taught at Edinburgh from this textbook.

Exercises labelled "(stretch)" are there to provide an extra challenge.
Few students do all of these, but most attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra
practice.

You may need to import library functions required for the solution.

Please do not post answers to the exercises in a public place.

There is a private repository of answers to selected questions on
github. Please contact Philip Wadler if you would like to access it.
