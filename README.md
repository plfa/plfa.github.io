---
layout: page
title: Getting Started
permalink: /GettingStarted/
---

<!-- Links -->

[plfa-dev]: https://github.com/plfa/plfa.github.io/archive/dev.zip
[plfa-status]: https://travis-ci.org/plfa/plfa.github.io.svg?branch=dev
[plfa-travis]: https://travis-ci.org/plfa/plfa.github.io
[plfa-master]: https://github.com/plfa/plfa.github.io/archive/master.zip

[agda]: https://github.com/agda/agda/releases/tag/v2.6.0.1
[agda-version]: https://img.shields.io/badge/agda-v2.6.0.1-blue.svg
[agda-docs-emacs-mode]: https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html
[agda-docs-package-system]: https://agda.readthedocs.io/en/v2.6.0.1/tools/package-system.html#example-using-the-standard-library

[agda-stdlib-version]: https://img.shields.io/badge/agda--stdlib-v1.1-blue.svg
[agda-stdlib]: https://github.com/agda/agda-stdlib/releases/tag/v1.1

[mononoki]: https://madmalik.github.io/mononoki/

[ruby]: https://www.ruby-lang.org/en/documentation/installation/
[ruby-bundler]: https://bundler.io/#getting-started
[ruby-jekyll]: https://jekyllrb.com/
[ruby-html-proofer]: https://github.com/gjtorikian/html-proofer

[kramdown]: https://kramdown.gettalong.org/syntax.html


<!-- Status & Version Badges -->

[![Build Status][plfa-status]][plfa-travis]
[![Agda][agda-version]][agda]
[![agda-stdlib][agda-stdlib-version]][agda-stdlib]


# Getting Started with PLFA

There are several tools you need to work with PLFA:

  - [Agda][agda]
  - [Agda standard library][agda-stdlib]

We require specific versions of Agda and the Agda standard library. These are shown and linked to in the badges above. We test with the versions listed. Agda changes rapidly, and earlier or later versions usually cause problems. The easiest way to install a specific version of Agda is using Stack. You can get the required version of Agda from GitHub, either by cloning the repository and switching to the correct branch, or by downloading [the zip archive][agda]:

```bash
git clone https://github.com/agda/agda.git
cd agda
git checkout v2.6.0.1
```

You can install Agda by running Stack from the source directory. Agda supplies several Stack configurations, each for a different version of GHC. If you’re in doubt which version is best for you, just pick the latest version:

```bash
stack install --stack-yaml stack-8.6.5.yaml
```

You can get the required version of the Agda standard library from GitHub, either by cloning the repository and switching to the correct branch, or by downloading [the zip archive][agda-stdlib]:

```bash
git clone https://github.com/agda/agda-stdlib.git
cd agda-stdlib
git checkout v1.1
```

You can get the latest version of Programming Language Foundations in Agda from GitHub, either by cloning the repository, or by downloading [the zip archive][plfa-dev]:

```bash
git clone https://github.com/plfa/plfa.github.io
```

Finally, we need to let Agda know where to find the standard library. For this, you can follow the instructions [here][agda-docs-package-system].

It is possible to set up PLFA as an Agda library as well.  If you want to complete the exercises found in the `courses` folder, or to import modules from the book, you need to do this.  To do so, add the path to `plfa.agda-lib` to `~/.agda/libraries` and add `plfa` to `~/.agda/defaults`, both on lines of their own.


## Auto-loading `agda-mode` in Emacs

In order to have `agda-mode` automatically loaded whenever you open a file ending with `.agda` or `.lagda.md`, put the following on your Emacs configuration file:

``` elisp
(setq auto-mode-alist
   (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))
```

The configuration file for Emacs is normally located in `~/.emacs` or `~/.emacs.d/init.el`, but Aquamacs users might need to move their startup settings to the `Preferences.el` file in `~/Library/Preferences/Aquamacs Emacs/Preferences`.


## Unicode characters

If you're having trouble typing the Unicode characters into Emacs, the end of each chapter should provide a list of the unicode characters introduced in that chapter.

`agda-mode` and emacs have a number of useful commands. Two of them are especially useful when you solve exercises.

For a full list of supported characters, use `agda-input-show-translations` with:

    M-x agda-input-show-translations

All the supported characters in `agda-mode` are shown.

If you want to know how you input a specific Unicode character in agda file, move the cursor onto the character and type the following command:

    M-x quail-show-key

You'll see the key sequence of the character in mini buffer.


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

See [the emacs-mode docs][agda-docs-emacs-mode] for more details.

If you want to see messages beside rather than below your Agda code, you can do the following:

  - Load your Agda file and do `C-c C-l`;
  - type `C-x 1` to get only your Agda file showing;
  - type `C-x 3` to split the window horizontally;
  - move your cursor to the right-hand half of your frame;
  - type `C-x b` and switch to the buffer called "Agda information"

Now, error messages from Agda will appear next to your file, rather than squished beneath it.


## Fonts in Emacs

It is recommended that you install the font [mononoki][mononoki], and add the following to the end of your emacs configuration file at `~/.emacs`:

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

  - [Ruby][ruby]
  - [Bundler][ruby-bundler]

For most of the tools, you can simply follow their respective build instructions. Most recent versions of Ruby should work. You install the Ruby dependencies---[Jekyll][ruby-jekyll], [html-proofer][ruby-html-proofer], *etc.*---using Bundler:

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

If you simply wish to have a local copy of the book, e.g. for offline reading, but don't care about editing and rebuilding the book, you can grab a copy of the [master branch][plfa-master], which is automatically built using Travis. You will still need Ruby and Bundler to host the book (see above). To host the book this way, download a copy of the [master branch][plfa-master], unzip, and from within the directory run

    bundle install
    bundle exec jekyll serve


## Markdown

The book is written in [Kramdown Markdown][kramdown].


## Travis Continuous Integration

You can view the build history of PLFA at [travis-ci.org][plfa-travis].
