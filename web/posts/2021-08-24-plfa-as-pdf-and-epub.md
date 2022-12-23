---
title: "PLFA as PDF and EPUB"
---

We’re pleased to announce that PLFA is now available as both ~~a PDF~~ and [an EPUB][EPUB]! Thanks to hard work by [Yuanting Mao][Altariarite], who did an internship with Phil at the University of Edinburgh, and a little elbow grease on our part, we're finally compiling to PDF!

In a double whammy, we’ve recently fixed compilation to EPUB as well! Compilation to EPUB never quite survived the move to Hakyll, and the EPUB available on the website was broken for quite a while. Fortunately, we’ve fixed the EPUB compilation, based on [Yuanting Mao][Altariarite] work on PDF compilation and [Michael Reed][mreed20]’s original work on EPUB compilation.

<!--more-->

There’s still several kinks to even out in the process:

  - ([#577][issue577]) EPUB generation breaks internal links;
  - ([#578][issue578]) EPUB fragment identifier is not defined;
  - ([#579][issue579]) EPUB font cannot be found;
  - ([#580][issue580]) EPUB attribute "name" not allowed;
  - ([#581][issue581]) PDF code overflows margins;

And probably tons of other little bugs I've missed!

As always, bug reports and pull requests are very, very welcome!

[Altariarite]: https://github.com/Altariarite
[mreed20]: https://github.com/mreed20

[EPUB]: https://plfa.github.io/plfa.epub

[issue577]: https://github.com/plfa/plfa.github.io/issues/577
[issue578]: https://github.com/plfa/plfa.github.io/issues/578
[issue579]: https://github.com/plfa/plfa.github.io/issues/579
[issue580]: https://github.com/plfa/plfa.github.io/issues/580
[issue581]: https://github.com/plfa/plfa.github.io/issues/581
