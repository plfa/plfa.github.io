---
layout: page
title: About
permalink: /about/
---

## How to host literate code

In directory `plfa.github.io/` run the following:

    $ make clobber              (remove all files before rebuilding system)
    $ make macos-setup          (might need sudo, but try it without first)
    $ make build                (builds lagda->markdown and website)
    $ make test                 (checks all links are valid)
    $ make build-incremental    (builds lagda->markdown and website using incremental)
    $ make server-start         (starts server in detached mode)
    $ make server-stop          (stops the server, uses pkill)

The visible page appears at

    localhost:4000/<permalink>


## Travis

Travis performs continuous integration (CI), generating web pages from github.
View error messages at [travis-ci.org](http://travis-ci.org/plfa/plfa.github.io).


## Updates to agda2html

Go to your clone of the agda2html repository, and run

    $ git pull
    $ stack install


## Unicode abbreviations

    \to    →
    \u+    ⊎
    \all   ∀
    \x     ×
    x\_1   x₁
    x\_i   xᵢ

See
[agda-input.el](https://github.com/agda/agda/blob/master/src/data/emacs-mode/agda-input.el#L194)
for more details.


## How to use `agda-mode`

    ?            create hole
    {!...!}      create hole
    C-c C-l      load buffer

Command to give when in a hole:

    C-c C-c x    split on variable x
    C-c C-space  fill in hole
	C-c C-r      refine with constructor
	C-c C-a      automatically fill in hole
	C-c C-,      Goal type and context
	C-c C-.      Goal type, context, and inferred type

See
[the emacs-mode docs](http://agda.readthedocs.io/en/latest/tools/emacs-mode.html)
for more details.

If you want to see messages beside rather than below your Agda code,
you can do the following: Load your Agda file and do C-c C-l.  Type
C-x 1 to get only your agda file showing, then type C-x 3 to split the
window horizontally.  Now move to the right-hand half of your frame
and switch to the buffer called "Agda information" by typing C-x b
Agda TAB.  Now messages from Agda will appear next to your file,
rather than squashed beneath it.




## Markdown

For an overview of the Markdown syntax, see
[the original description](https://daringfireball.net/projects/markdown/syntax),
[the CommonMark project](https://spec.commonmark.org/0.28/), or
[the version that is used in this book](https://kramdown.gettalong.org/syntax.html).


## Git

Checkout this repository with

    git clone git@github.com:plfa/plfa.github.io.git

You can check this worked:

    $ cd plfa.github.io
    $ git status
    On branch dev
    Your branch is up-to-date with 'origin/dev'.

    Untracked files:
      (use "git add <file>..." to include in what will be committed)

    	out/

    nothing added to commit but untracked files present (use "git add" to track)
    $

## Analytics

Wen and Phil can track [Google Analytics](http://analytics.google.com/analytics/web/).
