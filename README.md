---
layout: page
title: About
permalink: /about/
---

This is a rewrite of the text [Software Foundations](
https://softwarefoundations.cis.upenn.edu/current/index.html
)
from Coq to Agda. The authors are 
[Wen Kokke](
https://github.com/wenkokke
)
and
[Philip Wadler](
http://homepages.inf.ed.ac.uk/wadler/
).


## How to host literate code

In directory `sf/` run the following:

	$ make clobber
    $ make
    $ make serve &

The visible page appears at

    localhost:4000/sf/<permalink>

## Markdown

For markdown commands see [Daring Fireball](
https://daringfireball.net/projects/markdown/syntax
).

## Important git commands

    git pull
    git commit -am "message"
    git push

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
    {!...!}      create holde
    C-c C-l      reload
    C-c C-c x    split on variable x 
    C-c C-space  fill in hole


Also see [here](
http://agda.readthedocs.io/en/latest/tools/emacs-mode.html
).

