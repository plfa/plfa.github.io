---
layout: page
title: About
permalink: /about/
---

This is a rewrite of the text

* [Software Foundations](
  https://softwarefoundations.cis.upenn.edu/current/index.html
  )

from Coq to Agda. The authors are

* [Wen Kokke](
  https://github.com/wenkokke
  )
* [Philip Wadler](
  http://homepages.inf.ed.ac.uk/wadler/
  )

## Instructions

_How to host literate code_

In directory `sf/` the following:

	$ make clobber
    $ make
    $ make serve &

The visible page appears at

    localhost:4000/sf/<permalink>

For markdown commands see [Daring Fireball](
https://daringfireball.net/projects/markdown/syntax
).

_Important git commands_

    git pull
    git commit -am "message"
    git push

_[Unicode abbreviations](
https://github.com/agda/agda/blob/master/src/data/emacs-mode/agda-input.el#L194
)_

    \to    →
    \u+    ⊎
    \all   ∀
    \x     ×
	x\_1   x₁
	x\_i   xᵢ

_Bindings for [Agda mode](
http://agda.readthedocs.io/en/latest/tools/emacs-mode.html
)_

    ?            create hole
    {!...!}      create holde
    C-c C-l      reload
    C-c C-c x    split on variable x 
    C-c C-space  fill in hole
    
