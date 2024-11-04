---
title     : "TSPL: Course notes (Fall 2024)"
permalink : /TSPL/2024/
---


## Staff

* **Instructor**
    [Philip Wadler](https://homepages.inf.ed.ac.uk/wadler)
* **Teaching assistants**
    [Malin Altenmüller](https://maltenmuller.github.io/),
    [Louis Lemonnier](https://homepages.inf.ed.ac.uk/llemonni/)


## Lectures and tutorials

Lectures take place Tuesday, Wednesday, and Thursday weeks 4--10.
Lectures on Tuesday and Thursday are immediately followed by a tutorial.

* **12.10--14.00** _Tuesday Lecture and Tutorial_
  Teaching Room 13 (01M.473) - Doorway 3 - Medical School, Teviot
* **12.10--13.00** _Wednesday Lecture_
  G.07 Meadows Lecture Theatre - Doorway 4 - Medical School, Teviot
* **12.10--14.00** _Thursday Lecture and Tutorial_
  5.3 - Lister Learning and Teaching Centre

## Course textbook

* [PLFA](https://plfa.inf.ed.ac.uk)

## Links

* [Piazza][piazza]
* [Learn][learn]
<!-- Omit DRPS because it is not https -->
<!-- * [Lectures][lectures] -->

[piazza]: https://piazza.com/class/m03x8uq3s642g7
[learn]: https://www.learn.ed.ac.uk/ultra/courses/_117826_1/outline
[lectures]: https://echo360.org.uk/section/a4451855-1138-4ae3-9c94-acd37a91c8a4/home

## Schedule

<table>
<thead>
 <tr>
  <th scope="col">Week</th>
  <th scope="col">Tue</th>
  <th scope="col">Wed</th>
  <th scope="col">Thu<th>
 </tr>
</thead>
<tbody>
 <tr>
  <td>4</td>
  <td>**8 Oct** [Naturals](/Naturals/)</td>
  <td>**9 Oct** [Induction](/Induction/)</td>
  <td>**10 Oct** [Relations](/Relations/)</td>
 </tr>
 <tr>
  <td>5</td>
  <td>**15 Oct** [Equality](/Equality/)</td>
  <td>**16 Oct** [Isomorphism](/Isomorphism/)</td>
  <td>**17 Oct** [Connectives](/Connectives/)</td>
 </tr>
 <tr>
  <td>6</td>
  <td>**22 Oct** [Negation](/Negation/)</td>
  <td>**23 Oct** [Quantifiers](/Quantifiers/)</td>
  <td>**24 Oct** [Decidable](/Decidable/)</td>
 </tr>
 <tr>
  <td>7</td>
  <td>**29 Oct** [Lambda](/Lambda/)[^lists]</td>
  <td>**30 Oct** [Lambda](/Lambda/)</td>
  <td>**31 Oct** (Milner lecture)
 </tr>
 <tr>
  <td>8</td>
  <td>**5 Nov** [Properties](/Properties/)</td>
  <td>**6 Nov** [Properties](/Properties/)[^online]</td>
  <td>**7 Nov** [DeBruijn](/DeBruijn/)</td>
 </tr>
 <tr>
  <td>9</td>
  <td>**12 Nov** [More](/More/)</td>
  <td>**13 Nov** [More](/More/)</td>
  <td>**14 Nov** [Inference](/Inference/)</td>
 </tr>
 <tr>
  <td>10</td>
  <td>**19 Nov** [Inference](/Inference/)</td>
  <td>**20 Nov** [Untyped](/Untyped/)</td>
  <td>**21 Nov** Propositions as Types</td>
 </tr>
</tbody>
</table>

[^lists]:In week 7, also read [Lists](/Lists/) on your own.

[^online]:This lecture willl be delivered online by Malin Altenmuller.
The Zoom link is here:<br/>
[https://ed-ac-uk.zoom.us/j/81894080012](https://ed-ac-uk.zoom.us/j/81894080012)<br/>
Meeting ID: 818 9408 0012<br/>
Passcode: aDvv0dXC

## Assessment

Assessment for the course is as follows.

* four courseworks, marked best three out of four, **80%**
* essay, take a research paper and formalise its development, **20%**

Because there is no final, we need to be able to check that students
can explain their work during tutorials.  For this reason, _you can
only achieve marks on coursework if you have attended at least one of
the four tutorial sessions in the week before it is due_.

In order to conform with the University's Common Marking Scheme,
students may typically get only 10 points or less (out of 20) on the
essay.  _Attempting the essay may not be a good use of time
compared to other courses where there are easier marks to be had._
Not all students are expected to attempt the essay.


## Coursework

For instructions on how to set up Agda for PLFA see [Getting Started](/GettingStarted/).

* [Assignment 1](/TSPL/2024/Assignment1/) cw1 due 12 noon Friday 18 October (Week 5)
* [Assignment 2](/TSPL/2024/Assignment2/) cw2 due 12 noon Friday 1 November (Week 7)
* [Assignment 3](/TSPL/2024/Assignment3/) cw3 due 12 noon Friday 15 November (Week 9)
* Assignment 4 cw4 due 12 noon Friday 29 November (Week 11)
* Essay cw5 due 12 noon Thursday 23 January 2025 (Week 2, Semester 2)


## How to submit coursework

Go to the TSPL [Learn][learn] course and select “Assessment” from the left hand
menu. Select the “Assignment Submission” folder and then click on the
link “submit your coursework here”. This will take you to the
Gradescope interface.

For anyone who has sat an online exam, Gradescope should look familiar.
Gradescope programming assignments differ from exams in that
it offers three options for submitting your work:

  *   Drag and drop your code file(s) into Gradescope
  *   Submit a GitHub repository
  *   Submit a Bitbucket repository

For the last two, you need to link your account to submit from GitHub
or Bitbucket if you have not already.  Instructions to do so are
[here](https://help.gradescope.com/article/lcn4nfvcww-student-edit-account#linking_accounts).


<!-- Assignments are submitted by running
``` bash
submit tspl cwN AssignmentN.lagda.md
```
where N is the number of the assignment. -->


## Essay

The essay is to take a research paper and formalise all or
part of it in Agda.  In the past, some students have submitted superb
essays that contributed to ongoing research.
Talk to Prof Wadler about what you would like to submit.

<!--
## Mock exam

10am-12noon Monday 28 November. An online
examination with the Agda proof assistant, to let you
practice for the exam and familiarise yourself with exam conditions.
-->

## Additional reading

* John Reynolds,
  [Three Approaches to Type Structure][reynolds],
  _Mathematical Foundations of Software Development_,
  LNCS 185, pages 97–138, 1985.

* Henk Barendregt,
  [Introduction to generalized type systems][barendregt]
  _Journal of Functional Programming_, 1(2): 125–154, 1991.

* Vladimir Gapayev, Michael Levin, Benjamin Pierce.
  [Recursive Subtyping Revealed][gapayev],
  _International Conference on Functional Programming_, 2000.

* Philip Wadler.
  [Propositions as Types][p-as-t],
  _Communications of the ACM_, 58(12): 75–84, December 2015.

[reynolds]: https://homepages.inf.ed.ac.uk/wadler/papers/reynolds/three-approaches.pdf
[barendregt]: https://homepages.inf.ed.ac.uk/wadler/papers/barendregt/pure-type-systems.pdf
[gapayev]: https://homepages.inf.ed.ac.uk/wadler/papers/gapayev/gapayev-et-al-icfp2000.pdf
[p-as-t]: https://dl.acm.org/doi/10.1145/2699407

<!--
## Midterm course feedback

You may offer feedback on the course at
[https://www.surveymonkey.co.uk/r/YX7ZFYC](https://www.surveymonkey.co.uk/r/YX7ZFYC).

Please do so by 12 noon Thursday 31 October.
-->

<!--

## Mock exam

Here is the text of the [second mock](/courses/tspl/2018/Mock2.pdf)
and the exam [instructions](/courses/tspl/2018/Instructions.pdf).

-->
