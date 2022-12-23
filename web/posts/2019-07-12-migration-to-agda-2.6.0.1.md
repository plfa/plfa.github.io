---
title: "Migration to Agda 2.6.0.1"
---

We upgraded to [Agda 2.6.0.1][agda-2.6.0.1] and [version 1.1 of the standard library][agda-stdlib-v1.1]. If you want to continue working with the book, you'll have to update your versions locally. Please follow the instructions in [Getting Started](/GettingStarted/) to reinstall Agda and the standard library.

<!--more-->

For this upgrade, we made several major changes to the PLFA infrastructure.

We deprecated [agda2html][agda2html]. In version 2.6, Agda has added support for the `--html-highlight` flag. Using this command, Agda will highlight only the code in a file, and leave the rest untouched:
```bash
agda --html --html-highlight=code FILE.lagda.md
```
Of course, [agda2html][agda2html] offered support for more than just inline highlighting of code in Markdown files. We have written a bash script, [`highlight.sh`][highlight.sh] (*deprecated*) which supports much of the same functionality. In particular, it uses sed to redirect links to the standard library to [the online version](https://agda.github.io/agda-stdlib/README.html). For the time being, we dropped support for module references, e.g., linking to the chapter on Naturals by writing `[Naturals][plfa.Naturals]`, and removed all module references from the text.

Lastly, to use Agda 2.6 with Markdown, we updated all literal Agda files. We replaced LaTeX code fences, i.e., `\begin{code}` and `\end{code}`, with Markdown backtick fences ```` ``` ````, and changed the file extensions `.lagda` to `.lagda.md`. As a consequence, when you open up a literate Agda file in Emacs, it will open the file in Markdown mode -- if you have it installed -- or in fundamental mode. To switch to Agda mode, you will have to invoke `M-x agda2-mode`.

[agda-stdlib-v1.1]: https://github.com/agda/agda-stdlib/releases/tag/v1.1
  "Agda standard library version 1.1 on GitHub"
[agda-2.6.0.1]: https://github.com/agda/agda/releases/tag/v2.6.0.1
  "Agda version 2.6.0.1 on GitHub"
[highlight.sh]: https://github.com/plfa/plfa.github.io/blob/ea8bee4461e2e43891605d7f694dfce8a2b1923f/highlight.sh
  "The deprecated shell script used for highlighting Agda code"
[agda2html]: https://github.com/wenkokke/agda2html
  "The deprecated Haskell library used for highlighting Agda code"
