---
layout: page
title: Getting Started
permalink: /GettingStarted/
---

<!-- Links -->

[plfa]: http://plfa.inf.ed.ac.uk
[plfa-dev]: https://github.com/plfa/plfa.github.io/archive/dev.zip
[plfa-status]: https://travis-ci.org/plfa/plfa.github.io.svg?branch=dev
[plfa-travis]: https://travis-ci.org/plfa/plfa.github.io
[plfa-calver]: https://img.shields.io/badge/calver-20.07-22bfda
[plfa-latest]: https://github.com/plfa/plfa.github.io/releases/latest
[plfa-master]: https://github.com/plfa/plfa.github.io/archive/master.zip

[agda]: https://github.com/agda/agda/releases/tag/v2.6.0.1
[agda-version]: https://img.shields.io/badge/agda-v2.6.0.1-blue.svg
[agda-docs-emacs-mode]: https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html
[agda-docs-emacs-notation]: https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html#notation-for-key-combinations
[agda-docs-package-system]: https://agda.readthedocs.io/en/v2.6.0.1/tools/package-system.html#example-using-the-standard-library

[agda-stdlib-version]: https://img.shields.io/badge/agda--stdlib-v1.1-blue.svg
[agda-stdlib]: https://github.com/agda/agda-stdlib/releases/tag/v1.1

[haskell-stack]:  https://docs.haskellstack.org/en/stable/README/
[haskell-ghc]: https://www.haskell.org/ghc/

[mononoki]: https://madmalik.github.io/mononoki/

[ruby]: https://www.ruby-lang.org/en/documentation/installation/
[ruby-bundler]: https://bundler.io/#getting-started
[ruby-jekyll]: https://jekyllrb.com/
[ruby-html-proofer]: https://github.com/gjtorikian/html-proofer

[kramdown]: https://kramdown.gettalong.org/syntax.html
[pandoc]: https://pandoc.org/installing.html
[epubcheck]: https://github.com/w3c/epubcheck


<!-- Status & Version Badges -->
[![Calendar Version][plfa-calver]][plfa-latest]
[![Build Status][plfa-status]][plfa-travis]
[![Agda][agda-version]][agda]
[![agda-stdlib][agda-stdlib-version]][agda-stdlib]


# Getting Started with PLFA

## Dependencies for users

You can read PLFA [online][plfa] without installing anything.
However, if you wish to interact with the code or complete the exercises, you need several things:

  - [Agda][agda]
  - [Agda standard library][agda-stdlib]
  - [PLFA][plfa-dev]

PLFA is tested against specific versions of Agda and the standard library, which are shown in the badges above. Agda and the standard library change rapidly, and these changes often break PLFA, so using older or newer versions usually causes problems.

### Installing Agda using Stack

The easiest way to install any specific version of Agda is using [Stack][haskell-stack]. You can get the required version of Agda from GitHub, either by cloning the repository and switching to the correct branch, or by downloading [the zip archive][agda]:
```bash
git clone https://github.com/agda/agda.git
cd agda
git checkout v2.6.0.1
```
To install Agda, run Stack from the Agda source directory:
```bash
stack install --stack-yaml stack-8.6.5.yaml
```
If you want Stack to use you system installation of GHC, you can pass the `--system-ghc` flag and select the appropriate `stack-*.yaml` file. For instance, if you have GHC 8.2.2 installed, run:
```bash
stack install --system-ghc --stack-yaml stack-8.2.2.yaml
```

### Installing the Standard Library and PLFA

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


## Setting up and using Emacs

The recommended editor for Agda is Emacs with `agda-mode`. Agda ships with `agda-mode`, so if you’ve installed Agda, all you have to do to configure `agda-mode` is run:
```bash
agda-mode setup
```

To load and type-check the file, use [`C-c C-l`][agda-docs-emacs-notation].


Agda is edited “interactively, which means that one can type check code which is not yet complete: if a question mark (?) is used as a placeholder for an expression, and the buffer is then checked, Agda will replace the question mark with a “hole” which can be filled in later. One can also do various other things in the context of a hole: listing the context, inferring the type of an expression, and even evaluating an open term which mentions variables bound in the surrounding context.”

Agda is edited interactively, using “holes”, which are bits of the program that are not yet filled in. If you use a question mark as an expression, and load the buffer using `C-c C-l`, Agda replaces the question mark with a hole. There are several things you can to while the cursor is in a hole:

    C-c C-c x    split on variable x
    C-c C-space  fill in hole
    C-c C-r      refine with constructor
    C-c C-a      automatically fill in hole
    C-c C-,      goal type and context
    C-c C-.      goal type, context, and inferred type

See [the emacs-mode docs][agda-docs-emacs-mode] for more details.

If you want to see messages beside rather than below your Agda code, you can do the following:

  - Open your Agda file, and load it using `C-c C-l`;
  - type `C-x 1` to get only your Agda file showing;
  - type `C-x 3` to split the window horizontally;
  - move your cursor to the right-hand half of your frame;
  - type `C-x b` and switch to the buffer called “Agda information”.

Now, error messages from Agda will appear next to your file, rather than squished beneath it.


### Auto-loading `agda-mode` in Emacs

Since version 2.6.0, Agda has support for literate editing with Markdown, using the `.lagda.md` extension. One side-effect of this extension is that most editors default to Markdown editing mode, whereas
In order to have `agda-mode` automatically loaded whenever you open a file ending with `.agda` or `.lagda.md`, put the following on your Emacs configuration file:
```elisp
(setq auto-mode-alist
   (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))
```

The configuration file for Emacs is normally located in `~/.emacs` or `~/.emacs.d/init.el`, but Aquamacs users might need to move their startup settings to the `Preferences.el` file in `~/Library/Preferences/Aquamacs Emacs/Preferences`.


### Using mononoki in Emacs

It is recommended that you install the font [mononoki][mononoki], and add the following to the end of your emacs configuration file at `~/.emacs`:

``` elisp
;; default to mononoki
(set-face-attribute 'default nil
		    :family "mononoki"
		    :height 120
		    :weight 'normal
		    :width  'normal)
```


### Unicode characters

If you're having trouble typing the Unicode characters into Emacs, the end of each chapter should provide a list of the unicode characters introduced in that chapter.

`agda-mode` and emacs have a number of useful commands. Two of them are especially useful when you solve exercises.

For a full list of supported characters, use `agda-input-show-translations` with:

    M-x agda-input-show-translations

All the supported characters in `agda-mode` are shown.

If you want to know how you input a specific Unicode character in agda file, move the cursor onto the character and type the following command:

    M-x quail-show-key

You'll see the key sequence of the character in mini buffer.


## Dependencies for developers

PLFA is available as both a website and an EPUB e-book,
both of which can be built on Linux and macOS.
PLFA is written in literate Agda with [Kramdown Markdown][kramdown].

### Building the website

The website version of the book is built in three stages:

 1. The `.lagda.md` files are compiled to Markdown using Agda’s highlighter.
    (This requires several POSIX tools, such as `bash`, `sed`, and `grep`.)

 2. The Markdown files are converted to HTML using [Jekyll][ruby-jekyll], a widely-used static site builder.
    (This requires [Ruby][ruby] and [Jekyll][ruby-jekyll].)

 3. The HTML is checked using [html-proofer][ruby-html-proofer].
    (This requires [Ruby][ruby] and [html-proofer][ruby-html-proofer].)

Most recent versions of [Ruby][ruby] should work. The easiest way to install [Jekyll][ruby-jekyll] and [html-proofer][ruby-html-proofer] is using [Bundler][ruby-bundler]. You can install [Bundler][ruby-bundler] by running:
```bash
gem install bundler
```
You can install the remainder of the dependencies---[Jekyll][ruby-jekyll], [html-proofer][ruby-html-proofer], *etc.*---by running:
```bash
bundle install
```
Once you have installed all of the dependencies, you can build a copy of the book, and host it locally, by running:
```bash
make build
make serve
```
The Makefile offers more than just these options:
```bash
make                      # see make test
make build                # builds lagda->markdown and the website
make build-incremental    # builds lagda->markdown and the website incrementally
make test                 # checks all links are valid
make test-offline         # checks all links are valid offline
make serve                # starts the server
make server-start         # starts the server in detached mode
make server-stop          # stops the server, uses pkill
make clean                # removes all ~unnecessary~ generated files
make clobber              # removes all generated files
```
If you simply wish to have a local copy of the book, e.g. for offline reading, but don't care about editing and rebuilding the book, you can grab a copy of the [master branch][plfa-master], which is automatically built using Travis. You will still need [Jekyll][ruby-jekyll] and preferably [Bundler][ruby-bundler] to host the book (see above). To host the book this way, download a copy of the [master branch][plfa-master], unzip, and from within the directory run
```bash
bundle install
bundle exec jekyll serve
```

### Building the EPUB

The EPUB version of the book is built using Pandoc. Here's how to build the EPUB:

1. Install a recent version of Pandoc, [available here][pandoc].
   We recommend their official installer (on the linked page),
   which is much faster than compiling Pandoc from source with Haskell Stack.

2. Build the EPUB by running:
   ```bash
   make epub
   ```
   The EPUB is written to `out/epub/plfa.epub`.
