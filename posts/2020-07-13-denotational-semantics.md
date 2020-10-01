---
layout : post
title  : "Introducing Part 3: Denotational Semantics"
short  : false
---

We’re pleased to announce an entirely new part of the book, contributed by Jeremy G. Siek! You may have noticed his name appearing on the list of authors some months ago, or the chapters that make up Part 3 slowly making their appearance. Well, that’s all Jeremy’s work!

<!--more-->

Part 3 introduces denotational semantics, presenting the denotational semantics of the untyped lambda calculus. Our development is unusual in that emphasizes the use of intersection type systems as denotational models instead of the more traditional domain theory, but this choice allows us to build upon the simple type systems studied in Part 2.
Part 3 also proves the basic properties of the denotational semantics using techniques and variations of the techniques introduced in Part 2. We prove the *soundness* of reduction with respect to the denotational semantics by showing that reduction preserves and reflects denotations. We prove *adequacy* of the denotational semantics using a logical-relations style proof with respect to a big-step semantics of the untyped calculus. Finally, with these results in hand, we prove a standardisation theorem, that reduction to weak-head normal form implies the termination of call-by-name evaluation.

To better prepare the reader for Part 3, we made some changes and updates to Part 2. We’ve changed the reduction semantics for the untyped lambda calculus to be the standard one, with unconstrained beta reduction. We also added two new chapters to Part 2. The first proves confluence—a.k.a. the Church-Rosser property—for the untyped lambda calculus. The second presents big-step semantics for call-by-name evaluation, and proves that call-by-name termination implies the reduction to weak-head normal form.

Finally, we also include an Appendix with a single chapter, which proves the substitution lemma for the untyped lambda calculus. We opted to place this chapter an Appendix, and not in Part 2, because we already discuss substitution for the simply-typed lambda calculus, and we feel it would not be particularly enlightening for students to work through the proofs, especially since the ratio of insight to lines of code is rather low.
