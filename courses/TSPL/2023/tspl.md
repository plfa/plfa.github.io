---
title     : "TSPL: Course notes"
permalink : /TSPL/2023/
---


## Staff

* **Instructor**
    [Philip Wadler](https://homepages.inf.ed.ac.uk/wadler)
* **Teaching assistant**
    [Tudor Ferariu](https://www.inf.ed.ac.uk/people/students/Tudor_Ferariu.html)

## Lectures and tutorials

Lectures take place Monday and Wednesday.
Each lecture is immediately followed by a tutorial.

* **12.10--14.00** _Monday Lecture and Tutorial_
  [Old Medical School](https://www.ed.ac.uk/maps/maps?building=0113)
  [MST Teaching Room 13 (01M.473) - Doorway 3]( https://www.ed.ac.uk/timetabling-examinations/timetabling/room-bookings/bookable-rooms3/room/0113_01M_01M.473)
* **12.10--14.00** _Wednesday Lecture and Tutorial_
  [Appleton Tower](https://www.ed.ac.uk/maps/maps?building=0201)
  [AT 2.12](https://www.ed.ac.uk/timetabling-examinations/timetabling/room-bookings/bookable-rooms3/room/0201_02_2.12)
* **12.10--14.00** _Friday Lecture and Tutorial_ **(week 1 only)**
  [Old Medical School](https://www.ed.ac.uk/maps/maps?building=0113)
  [MST Teaching Room 13 (01M.473) - Doorway 3]( https://www.ed.ac.uk/timetabling-examinations/timetabling/room-bookings/bookable-rooms3/room/0113_01M_01M.473)

## Links

* [Piazza][piazza]
* [Learn][learn]
<!-- * [Lectures][lectures] -->

[piazza]: https://piazza.com/class/lmgbduj9sw0589
[lectures]: https://echo360.org.uk/section/a4451855-1138-4ae3-9c94-acd37a91c8a4/home
[learn]: https://www.learn.ed.ac.uk/ultra/courses/_108407_1/outline

## Schedule

<table>
<thead>
 <tr>
  <th scope="col">Week</th>
  <th scope="col">Mon</th>
  <th scope="col">Wed</th>
  <th scope="col">Fri<th>
 </tr>
</thead>
<tbody>
 <tr>
  <td>1</td>
  <td>**18 Sep** [Naturals](/Naturals/)</td>
  <td>**20 Sep** [Induction](/Induction/)</td>
  <td>**22 Sep** [Relations](/Relations/)</td>
 </tr>
 <tr>
  <td>2</td>
  <td>**25 Sep** </td>
  <td>**28 Sep** </td>
 </tr>
 <tr>
  <td>3</td>
  <td>**2 Oct** [Equality](/Equality/) (no class, read on your own)</td>
  <td>**4 Oct** [Isomorphism](/Isomorphism/) (no class, read on your own)</td>
 </tr>
 <tr>
  <td>4</td>
  <td>**9 Oct** [Connectives](/Connectives/)</td>
  <td>**11 Oct** [Negation](/Negation/) &amp; [Quantifiers](/Quantifiers/)</td>
 </tr>
 <tr>
  <td>5</td>
  <td>**16 Oct** [Decidable](/Decidable/)</td>
  <td>**18 Oct** [Lambda](/Lambda/)</td>
 </tr>
 <tr>
  <td>6</td>
  <td>**23 Oct** [Lambda](/Lambda/) &amp; [Properties](/Properties/)</td>
  <td>**25 Oct** [Properties](/Properties/)</td>
 </tr>
 <tr>
  <td>7</td>
  <td>**30 Oct** [DeBruijn](/DeBruijn/)</td>
  <td>**1 Nov** [More](/More/)</td>
 </tr>
 <tr>
  <td>8</td>
  <td>**6 Nov** [Inference](/Inference/)</td>
  <td>**8 Nov** [Untyped](/Untyped/)</td>
 </tr>
 <tr>
  <td>9</td>
  <td>**13 Nov** [Untyped](/Untyped/)</td>
  <td>**15 Nov** [Eval](/TSPL/2023/Eval/)</td>
 </tr>
 <tr>
  <td>10</td>
  <td>**20 Nov** extra tutorial </td>
  <td>**23 Nov** extra tutorial </td>
 </tr>
 <tr>
  <td>11</td>
  <td>**27 Nov** [Propositions as Types][p-as-t] </td>
  <td>**29 Nov** (no class) </td>
 </tr>
</tbody>
</table>


## Assessment

Assessment for the course is as follows.

* five courseworks, sixteen points each, **80%**
* optional project, take a research paper and formalise its development, **20%**

In order to conform with the University's Common Marking Scheme,
students may typically get only 10 points or less (out of 20) on the
optional project.  Attempting the optional project may not be a good
use of time compared to other courses where there are easier marks to
be had.


## Coursework

For instructions on how to set up Agda for PLFA see [Getting Started](/GettingStarted/).

* [Assignment 1](/TSPL/2023/Assignment1/) cw1 due 12 noon Thursday 5 October (Week 3)
* [Assignment 2](/TSPL/2023/Assignment2/) cw2 due 12 noon Thursday 19 October (Week 5)
* [Assignment 3](/TSPL/2023/Assignment3/) cw3 due 12 noon Thursday 2 November (Week 7)
* [Assignment 4](/TSPL/2023/Assignment4/) cw4 due 12 noon Thursday 16 November (Week 9)
* [Assignment 5][Assignment5] cw5 due 12 noon Thursday 23 November (Week 10)
  Use file [Exam][Exam]. Despite the rubric, do **all
  three questions**.

[Assignment5]: https://homepages.inf.ed.ac.uk/wadler/tspl/2023/Assignment5.pdf
[Exam]: https://homepages.inf.ed.ac.uk/wadler/tspl/2023/Exam.lagda.md


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
