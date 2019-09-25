---
layout: page
title: Getting Started
permalink: /GettingStarted/
---

[![Build Status](https://travis-ci.org/plfa/plfa.github.io.svg?branch=dev)](https://travis-ci.org/plfa/plfa.github.io)
[![Agda](https://img.shields.io/badge/agda-2.6.0.1-blue.svg)](https://github.com/agda/agda/releases/tag/v2.6.0.1)
[![agda-stdlib](https://img.shields.io/badge/agda--stdlib-1.1-blue.svg)](https://github.com/agda/agda-stdlib/releases/tag/v1.1)


# Getting Started with PLFA

There are several tools you need to work with PLFA:

  - [Agda](https://agda.readthedocs.io/en/v2.6.0.1/getting-started/installation.html)
  - [Agda standard library](https://github.com/agda/agda-stdlib/releases/tag/v1.1)

For most of the tools, you can simply follow their respective build instructions.
We list the versions of our dependencies on the badges above.  We have
tested with the versions listed; either earlier or later versions may
cause problems.

You can get the appropriate version of Programming Language Foundations in Agda from GitHub,
either by cloning the repository,
or by downloading [the zip archive](https://github.com/plfa/plfa.github.io/archive/dev.zip):

    git clone https://github.com/plfa/plfa.github.io

Finally, we need to let Agda know where to find the standard library.
For this, you can follow the instructions
[here](https://agda.readthedocs.io/en/v2.6.0.1/tools/package-system.html#example-using-the-standard-library).

It is possible to set up PLFA as an Agda library as well.  If you want
to complete the exercises found in the `courses` folder, or to import
modules from the book, you need to do this.  To do so, add the path to
`plfa.agda-lib` to `~/.agda/libraries` and add `plfa` to
`~/.agda/defaults`, both on lines of their own.

## Auto-loading `agda-mode` in Emacs

In order to have `agda-mode` automatically loaded whenever you open a file ending
with `.agda` or `.lagda.md`, put the following on your Emacs configuration file:

``` elisp
(setq auto-mode-alist
   (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))
```

The configuration file for Emacs is normally located in `~/.emacs` or `~/.emacs.d/init.el`,
but Aquamacs users might need to move their startup settings to the Preferences.el file in
`~/Library/Preferences/Aquamacs Emacs/Preferences`.

## Unicode characters

If you're having trouble typing the Unicode characters into Emacs, the end of
each chapter should provide a list of the unicode characters introduced in that
chapter. For a full list of supported characters, see
[agda-input.el](https://github.com/agda/agda/blob/master/src/data/emacs-mode/agda-input.el#L194).


## Using `agda-mode`

    ?            hole
    {!...!}      hole with contents
    C-c C-l      load buffer

Command to give when in a hole:

    C-c C-c x    split on variable x
    C-c C-space  fill in hole
    C-c C-r      refine with constructor
    C-c C-a      automatically fill in hole
    C-c C-,      Goal type and context
    C-c C-.      Goal type, context, and inferred type

See
[the emacs-mode docs](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)
for more details.

If you want to see messages beside rather than below your Agda code,
you can do the following:

  - Load your Agda file and do `C-c C-l`;
  - type `C-x 1` to get only your Agda file showing;
  - type `C-x 3` to split the window horizontally;
  - move your cursor to the right-hand half of your frame;
  - type `C-x b` and switch to the buffer called "Agda information"

Now, error messages from Agda will appear next to your file, rather than
squished beneath it.


## Fonts in Emacs

It is recommended that you install the font [mononoki](https://madmalik.github.io/mononoki/), and add the following to the end of your emacs configuration file at `~/.emacs`:

``` elisp
;; default to mononoki
(set-face-attribute 'default nil
		    :family "mononoki"
		    :height 120
		    :weight 'normal
		    :width  'normal)
```


# Building the book

To build and host a local copy of the book, there are several tools you need *in addition to those listed above*:

  - [Ruby](https://www.ruby-lang.org/en/documentation/installation/)
  - [Bundler](https://bundler.io/#getting-started)

For most of the tools, you can simply follow their respective build instructions.
Most recent versions of Ruby should work.
You install the Ruby dependencies---[Jekyll](https://jekyllrb.com/), [html-proofer](https://github.com/gjtorikian/html-proofer), *etc.*---using Bundler:

    bundle install

Once you have installed all of the dependencies, you can build a copy of the book by running:

    make build

You can host your copy of the book locally by running:

    make serve

The Makefile offers more than just these options:

    make                      (see make test)
    make build                (builds lagda->markdown and the website)
    make build-incremental    (builds lagda->markdown and the website incrementally)
    make test                 (checks all links are valid)
    make test-offline         (checks all links are valid offline)
    make serve                (starts the server)
    make server-start         (starts the server in detached mode)
    make server-stop          (stops the server, uses pkill)
    make clean                (removes all ~unnecessary~ generated files)
    make clobber              (removes all generated files)

If you simply wish to have a local copy of the book, e.g. for offline reading,
but don't care about editing and rebuilding the book, you can grab a copy of the
[master branch](https://github.com/plfa/plfa.github.io/archive/master.zip),
which is automatically built using Travis. You will still need Ruby and Bundler
to host the book (see above). To host the book this way, download a copy of the
[master branch](https://github.com/plfa/plfa.github.io/archive/master.zip),
unzip, and from within the directory run

    bundle install
    bundle exec jekyll serve


## Markdown

The book is written in
[Kramdown Markdown](https://kramdown.gettalong.org/syntax.html).


## Travis Continuous Integration

You can view the build history of PLFA at [travis-ci.org](https://travis-ci.org/plfa/plfa.github.io).
