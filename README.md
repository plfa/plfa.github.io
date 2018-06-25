---
layout: page
title: About
permalink: /about/
---

This book is an introduction to programming language theory, written in Agda.  The authors are [Wen Kokke][twitter.com/wenkokke] and [Philip Wadler][twitter.com/PhilipWadler].

Please send us comments!  The text is currrently being drafted. The first draft of Part I will be completed before the end of March 2018. When that is done it will be announced here, and that would be an excellent time to comment on the first part.

The book was inspired by [Software Foundations][softwarefoundations.cis.upenn.edu], but presents the material in a different way; see the [Preface](Preface).

## How to host literate code

In directory `plta/` run the following:

    $ make clobber              (remove all files before rebuilding system)
    $ make macos-setup          (might need sudo, but try it without first)
    $ make build                (builds lagda->markdown and website)
    $ make build-incremental    (builds lagda->markdown and website using incremental)
    $ make server-start         (starts server in detached mode)
    $ make server-stop          (stops the server, uses pkill)

The visible page appears at

    localhost:4000/sf/<permalink>

## Unicode abbreviations


    \to    →
    \u+    ⊎
    \all   ∀
    \x     ×
    x\_1   x₁
    x\_i   xᵢ

See [agda-input.el](https://github.com/agda/agda/blob/master/src/data/emacs-mode/agda-input.el#L194) for more details.

## How to use `agda-mode`

    ?            create hole
    {!...!}      create hole
    C-c C-l      load buffer
    C-c C-c x    split on variable x 
    C-c C-space  fill in hole

See [the emacs-mode docs]( http://agda.readthedocs.io/en/latest/tools/emacs-mode.html) for more details.

## Markdown

For an overview of the Markdown syntax, see [the original description](daringfireball.net/projects/markdown/syntax), [the CommonMark project](spec.commonmark.org/0.28/), or [the version that is used in this book](kramdown.gettalong.org/syntax.html).


