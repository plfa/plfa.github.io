---
layout : post
title  : "Changes to PLFA"
---

Today, we are making several major changes to the PLFA infrastructure!

First off, we are upgrading to [Agda 2.6.0.1](https://github.com/agda/agda/releases/tag/v2.6.0.1) and [version 1.1 of the standard library](https://github.com/agda/agda-stdlib/releases/tag/v1.1). Please update your versions locally before submitting any bug reports!

With Agda 2.6, we now have support for the `--html-highlight` flag. Using this flag, Agda will highlight only the code in a file, and leave the rest untouched. This means that we can finally deprecate the [`agda2html`](https://github.com/wenkokke/agda2html) tool! We have replaced [`agda2html`](https://github.com/wenkokke/agda2html) with a bash script, [`highlight.sh`](https://github.com/plfa/plfa.github.io/blob/dev/highlight.sh), which does many of the same things. In particular, it uses GNU sed to reroute links to the Agda standard library to the online version.

To use Agda 2.6 with Markdown we have updated all literate Agda files. We have replaced the LaTeX code delimiters `\begin{code}` and `\end{code}` with Markdown backtick fences ```` ``` ````, and replaced the extension `.lagda` with `.lagda.md`. This means that when you open up a literate Agda file in emacs, it will likely start in Markdown mode instead of in Agda mode. You can switch to Agda mode by running `M-x agda2-mode`.
