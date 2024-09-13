---
title     : Table of Contents
permalink : /
next      : /Dedication/
---

This book is an introduction to programming language theory using the proof
assistant Agda.

Comments on all matters---organisation, material to add, material to remove,
parts that require better explanation, good exercises, errors, and typos---are
welcome.  The book repository is on [GitHub]. Pull requests are encouraged.
There is a private repository of answers to selected questions on github. Please
contact one of the authors if you would like to access it.


$for(toc.part)$
## $toc.part.title$
$for(toc.part.chapter)$
$if(toc.part.chapter.titlerunning)$
  * [$toc.part.chapter.titlerunning$]($toc.part.chapter.url$): $toc.part.chapter.subtitle$
$else$
  * [$toc.part.chapter.title$]($toc.part.chapter.url$)
$endif$
$endfor$

$endfor$

## Related


<!-- NOTE: The Mailing Lists are Deprecated -->
<!--
### Mailing lists
  * [plfa-interest@inf.ed.ac.uk](https://lists.inf.ed.ac.uk/mailman/listinfo/plfa-interest): <br />
    A mailing list for users of the book. <br />
    This is the place to ask and answer questions, or comment on the content of the book.
  * [plfa-dev@inf.ed.ac.uk](https://lists.inf.ed.ac.uk/mailman/listinfo/plfa-dev): <br />
    A mailing list for contributors. <br />
    This is the place to discuss changes and new additions to the book in excruciating detail.
-->

### Courses taught from the textbook

#### 2024
  * [Jacques Carette, McMaster University](
    https://github.com/JacquesCarette/CAS706-F2024)  
    (With course materials based on Prabhakar Ragde's 2021 course materials.)
  * [Philip Wadler, University of Edinburgh](
    /TSPL/2024/)

#### 2023
  * [Peter Thiemann, Albert-Ludwigs University][Freiburg-2023]
  * [Philip Wadler, University of Edinburgh][TSPL-2023]
  * [Ugo de'Liguoro, Università di Torino](
    https://laurea.informatica.unito.it/do/storicocorsi.pl/Show?_id=4509_2324)
  * [Maria Emilia Maietti and Ingo Blechschmidt, Università di Padova](
    https://www.math.unipd.it/~maietti/typ24.html)
  * [Peter Thiemann, Albert-Ludwigs University](
    https://web.archive.org/web/20240208112146/https://proglang.informatik.uni-freiburg.de/teaching/proglang/2023ws/)
  * [Philip Wadler, University of Edinburgh](
    /TSPL/2023/)

#### 2022
  * [Andrej Bauer, University of Ljubljana](
    https://web.archive.org/web/20220222095923/https://www.andrej.com/zapiski/ISRM-LOGRAC-2022/00-introduction.html)
  * [Ugo de'Liguoro, Università di Torino](
    https://laurea.informatica.unito.it/do/storicocorsi.pl/Show?_id=4509_2223)
  * [Maria Emilia Maietti and Ingo Blechschmidt, Università di Padova](
    https://www.math.unipd.it/~maietti/typ23.html)
  * [Prabhakar Ragde, University of Waterloo](
    https://web.archive.org/web/20221231183423/https://cs.uwaterloo.ca/~plragde/747/)
  * Michael Shulman, University of San Diego
    <!-- The course website is not public. -->
  * [Peter Thiemann, Albert-Ludwigs University](
    https://web.archive.org/web/20220810154516/https://proglang.informatik.uni-freiburg.de/teaching/proglang/2022ss/)
  * [Philip Wadler, University of Edinburgh](
    /TSPL/2022/)

#### 2021
  * Favonia, University of Minnesota
    <!-- The course website is not public. -->
  * [Jacques Carette, McMaster University](
    https://github.com/JacquesCarette/CAS706-F2021/)  
    (Using course materials based on Prabhakar Ragde's course materials.)
  * [Maria Emilia Maietti and Ingo Blechschmidt, Università di Padova](
    https://www.math.unipd.it/~maietti/typ22.html)
  * [Prabhakar Ragde, University of Waterloo](
    https://web.archive.org/web/20210424214202/https://cs.uwaterloo.ca/~plragde/747/)

#### 2020
  * [William Cook, University of Texas](
    https://web.archive.org/web/20220101114527/https://www.cs.utexas.edu/~wcook/Courses/386L/Sp2020-GradPL.pdf)
  * Ugo de'Liguoro, Università di Torino
    <!-- The course website is not public. -->
  * [Maria Emilia Maietti and Ingo Blechschmidt, Università di Padova](
    https://web.archive.org/web/20220810154713/https://www.math.unipd.it/~maietti/typ21.html)
  * [John Maraist, University of Wisconsin-La Crosse](
    https://web.archive.org/web/20220810155032/https://github.com/jphmrst/PLC/tree/fall2020#readme)
  * [Jeremy Siek, Indiana University](
    https://web.archive.org/web/20220421134334/https://jsiek.github.io/B522-PL-Foundations/)

#### 2019
  * [Dan Ghica, University of Birmingham](
    https://web.archive.org/web/20210126123738/https://www.cs.bham.ac.uk/internal/modules/2019/06-26943/)
  * Adrian King, San Francisco Types, Theorems, and Programming Languages Meetup
  * [Prabhakar Ragde, University of Waterloo](
    https://web.archive.org/web/20220103155952/https://cs.uwaterloo.ca/~plragde/842/)
  * [Philip Wadler, University of Edinburgh](
    https://plfa.github.io/20.07/TSPL/2019/)
    ([Praise](
      https://web.archive.org/web/20201130051416/https://www.eusa.ed.ac.uk/representation/campaigns/teachingawards2020/))
  * [Philip Wadler, Pontifícia Universidade Católica do Rio de Janeiro](
    https://plfa.github.io/20.07/PUC/2019/)

#### 2018
  * [David Darais, University of Vermont](
    https://web.archive.org/web/20190324115921/https://david.darais.com/courses/fa2018-cs295A/)
  * [Philip Wadler, University of Edinburgh](
    https://plfa.github.io/19.08/TSPL/2018/)
  * John Leo, Google Seattle
    <!-- The course website is not public. -->

Please tell us of others!

[GitHub]: https://github.com/plfa/plfa.github.io/
[SBMF]: https://homepages.inf.ed.ac.uk/wadler/topics/agda.html#sbmf
[SCP]: https://homepages.inf.ed.ac.uk/wadler/topics/agda.html#scf
[NextJournal]: https://nextjournal.com/plfa/ToC
