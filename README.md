---
layout: page
title: About
permalink: /about/
---

This book is an introduction to programming language theory, written
in Agda.  The authors are [Wen Kokke][wen] and [Philip Wadler][phil].

Please send us comments!  The text is currrently being drafted. The
first draft of Part I will be completed before the end of
March 2018. When that is done it will be announced here, and that would be
an excellent time to comment on the first part.

The book was inspired by [Software Foundations][sf], but presents the
material in a different way; see the [Preface](Preface).

## How to host literate code

In directory `sf/` run the following:

    $ make clobber              (remove all files before rebuilding system)
    $ make macos-setup          (might need sudo, but try it without first)
    $ make build                (builds lagda->markdown and website)
    $ make build-incremental    (builds lagda->markdown and website using incremental)
    $ make server-start         (starts server in detached mode)
    $ make server-stop          (stops the server, uses pkill)

The visible page appears at

    localhost:4000/sf/<permalink>

<!--
    $ make clobber
    $ make
    $ make serve &
-->

## Unicode abbreviations


    \to    →
    \u+    ⊎
    \all   ∀
    \x     ×
	x\_1   x₁
	x\_i   xᵢ

Also see [here](
https://github.com/agda/agda/blob/master/src/data/emacs-mode/agda-input.el#L194
).

## Bindings for Agda mode

    ?            create hole
    {!...!}      create hole
    C-c C-l      reload
    C-c C-c x    split on variable x 
    C-c C-space  fill in hole

Also see [here](
http://agda.readthedocs.io/en/latest/tools/emacs-mode.html
).

## Markdown

For markdown commands see [Daring Fireball](
https://daringfireball.net/projects/markdown/syntax
), [CommonMark](
http://spec.commonmark.org/0.28/
), or [Kramdown](
https://kramdown.gettalong.org/syntax.html
).


