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
  Appleton Tower, room 2.11 (AT 2.11).

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
  <td><b>19 Sep</b> (Bank Holiday)
  <td><b>22 Sep</b> <a href="/Naturals/">Naturals</a></td>
 </tr>
 <tr>
  <td>2</td>
  <td><b>26 Sep</b> <a href="/Induction/">Induction</a></td>
  <td><b>29 Sep</b> <a href="/Relations/">Relations</a></td>
 </tr>
 <tr>
  <td>3</td>
  <td><b> 3 Oct</b> <a href="/Equality/">Equality</a> &amp;
                    <a href="/Isomorphism/">Isomorphism</a></td></td>
  <td><b> 6 Oct</b> <a href="/Connectives/">Connectives</a></td>
 </tr>
 <tr>
  <td>4</td>
  <td><b>10 Oct</b> <a href="/Negation/">Negation</a></td>
  <td><b>13 Oct</b> <a href="/Quantifiers/">Quantifiers</a></td>
 </tr>
 <tr>
  <td>5</td>
  <td><b>17 Oct</b> <a href="/Decidable/">Decidable</a> &amp;
                    <a href="/Lists/">Lists</a></td>
  <td><b>20 Oct</b> <a href="/Lambda/">Lambda</a></td>
 </tr>
 <tr>
  <td>6</td>
  <td><b>24 Oct</b> <a href="/Lambda/">Lambda</a></td>
  <td><b>27 Oct</b> <a href="/Properties/">Properties</a></td>
 </tr>
 <tr>
  <td>7</td>
  <td><b>31 Oct</b> <a href="/DeBruijn/">DeBruijn</a></td>
  <td><b> 3 Nov</b> <a href="/More/">More</a></td>
 </tr>
 <tr>
  <td>8</td>
  <td><b> 7 Nov</b> <a href="/Inference/">Inference</a></td>
  <td><b>10 Nov</b> <a href="/Untyped/">Untyped</a></td></td>
 </tr>
 <tr>
  <td>9</td>
  <td><b>14 Nov</b> Blame and Coercions </td>
  <td><b>17 Nov</b> </td>
 </tr>
 <tr>
  <td>10</td>
  <td><b>21 Nov</b>	</td>
  <td><b>24 Nov</b>	</td>
 </tr>
 <tr>
  <td>11</td>
  <td><b>28 Nov</b> Propositions as Types </td>
  <td><b> 1 Dec</b> Mock Exam </td>
 </tr>
</tbody>
</table>


## Assessment

Assessment for the course is as follows.

* five courseworks, five points each, including a take-home mock exam
  (the "mock mock"), <b>25%</b>
* optional project, take a research paper and formalise its development, <b>25%</b>
* mock exam, online with Agda proof assistant under exam conditions, <b>0%</b>
* final exam, online with Agda proof assistant, <b>50%</b>

Students are expected to get 3--5 points each (out of 5) on the
courseworks. Students who undertake the coursework and mock exam typically
get 50 points (out of 50) on the final exam. In order to conform with
the University's Common Marking Scheme, students may typically
get only 10 points (out of 25) on the optional project.  Attempting
the optional project may not be a good use of time compared to other
courses where there are easier marks to be had.


## Coursework

For instructions on how to set up Agda for PLFA see [Getting Started](/GettingStarted/).

* [Assignment 1](/TSPL/2022/Assignment1/) cw1 due 12 noon Thursday 6 October (Week 3)
* Assignment 2 cw2 due 12 noon Thursday 20 October (Week 5)
* Assignment 3 cw3 due 12 noon Thursday 3 November(Week 7)
* Assignment 4 cw4 due 12 noon Thursday 17 November (Week 9)
* Assignment 5 cw5 due 12 noon Thursday 24 November (Week 10)
<!-- Use file [Exam](/TSPL/2022/Exam/). Despite the rubric, do **all three questions**. -->


Assignments are submitted by running
``` bash
submit tspl cwN AssignmentN.lagda.md
```
where N is the number of the assignment.


## Optional project

The optional project is to take a research paper and formalise all or
part of it in Agda.  In the past, some students have submitted superb optional
projects that contributed to ongoing research. One possible paper to tackle is
[here](https://homepages.inf.ed.ac.uk/wadler/papers/coercions-jfp/coercions-jfp.pdf).
Talk to me if you want to formalise something else.

* Optional project cw6 due 12 noon Thursday 28 November (Week 11)

Submit the optional project by running
``` bash
submit tspl essay Essay.lagda.md
```

## Mock exam

10am-12noon Friday 29 November, AT 5.05 West Lab. An online
examination with the Agda proof assistant, under DICE to let you
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
