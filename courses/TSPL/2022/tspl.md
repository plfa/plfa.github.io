---
title     : "TSPL: Course notes"
permalink : /TSPL/2022/
---


## Staff

* **Instructor**
    [Philip Wadler](https://homepages.inf.ed.ac.uk/wadler)
* **Teaching assistant**
    [Tudor Ferariu](https://www.inf.ed.ac.uk/people/students/Tudor_Ferariu.html)

## Lectures and tutorials

Lectures take place Monday and Thursday.
Monday's lecture is immediately followed by a tutorial.

* **10.00--12.00** _Monday Lecture and Tutorial_
  George Square 50, room G.02 (50GS G.02).
* **10.00--10.50** _Thursday Lecture_
  Informatics Forum, room G.03 (IF G.03), save for Thursday 10 November in G.07 (IF G.07).

## Links

* [Piazza][piazza]
* [Lectures][lectures]
* [Learn][learn]

[piazza]: https://piazza.com/class/l8epstau8uc5dd/
[lectures]: https://echo360.org.uk/section/a4451855-1138-4ae3-9c94-acd37a91c8a4/home
[learn]: https://www.learn.ed.ac.uk/ultra/courses/_98006_1/cl/outline

## Schedule

<table>
<thead>
 <tr>
  <th scope="col">Week</th>
  <th scope="col">Mon</th>
  <th scope="col">Thu</th>
 </tr>
</thead>
<tbody>
 <tr>
  <td>1</td>
  <td>**19 Sep** (Bank Holiday)
  <td>**22 Sep** Introduction </td>
 </tr>
 <tr>
  <td>2</td>
  <td>**26 Sep** [Naturals](/Naturals/)</td>
  <td>**29 Sep** [Induction](/Induction/)</td>
 </tr>
 <tr>
  <td>3</td>
  <td> **3 Oct** [Relations](/Relations/)</td>
  <td> **6 Oct** [Equality](/Equality/) &amp; [Isomorphism](/Isomorphism/)</td>
 </tr>
 <tr>
  <td>4</td>
  <td>**10 Oct** [Connectives](/Connectives/) &amp; [Negation](/Negation/)</td>
  <td>**13 Oct** [Quantifiers](/Quantifiers/)</td>
 </tr>
 <tr>
  <td>5</td>
  <td>**17 Oct** [Decidable](/Decidable/) &amp; [Lists](/Lists/)</td>
  <td>**20 Oct** [Lambda](/Lambda/)</td>
 </tr>
 <tr>
  <td>6</td>
  <td>**24 Oct** [Lambda](/Lambda/)</td>
  <td>**27 Oct** [Properties](/Properties/)</td>
 </tr>
 <tr>
  <td>7</td>
  <td>**31 Oct** [Properties](/Properties/)</td>
  <td> **3 Nov** [DeBruijn](/DeBruijn/)</td>
 </tr>
 <tr>
  <td>8</td>
  <td> **7 Nov** [More](/More/)</td>
  <td>**10 Nov** [Inference](/Inference/)</td>
 </tr>
 <tr>
  <td>9</td>
  <td>**14 Nov** [Untyped](/Untyped/)</td>
  <td>**17 Nov** [Eval](/TSPL/2022/Eval/)</td>
 </tr>
 <tr>
  <td>10</td>
  <td>**21 Nov** [agda2hs](https://github.com/agda/agda2hs) (guest: [Orestis Melkonian](https://omelkonian.github.io/))</td>
  <td>**24 Nov**</td>
 </tr>
 <tr>
  <td>11</td>
  <td>**28 Nov** Mock Exam</td>
  <td> **1 Dec** Propositions as Types</td>
 </tr>
</tbody>
</table>


## Assessment

Assessment for the course is as follows.

* five courseworks, five points each, including a take-home mock exam
  (the "mock mock"), **25%**
* optional project, take a research paper and formalise its development, **25%**
* mock exam, online with Agda proof assistant under exam conditions, **0%**
* final exam, online with Agda proof assistant, **50%**

Students are expected to get 3--5 points each (out of 5) on the
courseworks. Students who undertake the coursework and mock exam typically
get 50 points (out of 50) on the final exam. In order to conform with
the University's Common Marking Scheme, students may typically
get only 10 points or less (out of 25) on the optional project.  Attempting
the optional project may not be a good use of time compared to other
courses where there are easier marks to be had.


## Coursework

For instructions on how to set up Agda for PLFA see [Getting Started](/GettingStarted/).

* [Assignment 1](/TSPL/2022/Assignment1/) cw1 due 12 noon Thursday 6 October (Week 3)
* [Assignment 2](/TSPL/2022/Assignment2/) cw2 due 12 noon Thursday 20 October (Week 5)
* [Assignment 3](/TSPL/2022/Assignment3/) cw3 due 12 noon Thursday 3 November(Week 7)
* [Assignment 4](/TSPL/2022/Assignment4/) cw4 due 12 noon Thursday 17 November (Week 9)
* Assignment 5 cw5 due 12 noon Thursday 24 November (Week 10)
  Use file [Exam](/TSPL/2022/Exam/). Despite the rubric, do **all three questions**.

## How to submit coursework

Go to the TSPL [Learn][learn] course and select “Assessment” from the left hand
menu. Select the “Assignment Submission” folder and then click on the
link “submit your coursework here”. This will take you to the
Gradescope interface.

For anyone who has sat an online exam over the
last two years, Gradescope should look familiar.
Gradescope programming assignments differ from exams in that
it offers three options for submitting your work:

  *   Drag and drop your code file(s) into Gradescope
  *   Submit a GitHub repository
  *   Submit a Bitbucket repository

For the last two, you need to link your account to submit from GitHub or Bitbucket if you have not already.
Instructions to do so are [here](https://help.gradescope.com/article/lcn4nfvcww-student-edit-account#linking_accounts).


<!-- Assignments are submitted by running
``` bash
submit tspl cwN AssignmentN.lagda.md
```
where N is the number of the assignment. -->


## Optional project

The optional project is to take a research paper and formalise all or
part of it in Agda.  In the past, some students have submitted superb optional
projects that contributed to ongoing research.
Talk to me about what you would like to submit.
<!-- One possible paper to tackle is
[here](https://homepages.inf.ed.ac.uk/wadler/papers/coercions-jfp/coercions-jfp.pdf). -->

* Optional project cw6 due 12 noon Thursday 1 December (Week 11)

<!--
Submit the optional project by running
``` bash
submit tspl essay Essay.lagda.md
```
-->

## Mock exam

10am-12noon Monday 28 November. An online
examination with the Agda proof assistant, to let you
practice for the exam and familiarise yourself with exam conditions.


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

[reynolds]: https://homepages.inf.ed.ac.uk/wadler/papers/reynolds/three-approaches.pdf
[barendregt]: https://homepages.inf.ed.ac.uk/wadler/papers/barendregt/pure-type-systems.pdf
[gapayev]: https://homepages.inf.ed.ac.uk/wadler/papers/gapayev/gapayev-et-al-icfp2000.pdf


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
