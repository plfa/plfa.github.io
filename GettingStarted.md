---
layout: page
title: Setting up Agda for PLFA
permalink: /GettingStarted/
---

Download the latest version of Programming Language Foundations in Agda from Github:

```
$ git clone https://github.com/plfa/plfa.github.io ~/plfa.github.io
```

Download the version of the Agda standard library that works with the textbook:

```
$ git clone https://github.com/plfa/agda-stdlib ~/agda-stdlib
```

We need to tell Agda to use the standard library, and the material from Programming Language Foundations in Agda by default. Create a directory called `.agda` inside of your home directory:

```
$ mkdir ~/.agda
```

When you run Agda, it looks in this directory to figure out which libraries to use. Specifically, Agda expects `~/.agda` to contain two files:

  1. `~/.agda/libraries`, a list of all the libraries we want Agda to know about; and
  2. `~/.agda/defaults`, a list of the libraries we want Agda to use all the time.

Using your favourite text editor, create `~/.agda/libraries`. It should contain:

```
~/agda-stdlib/standard-library.agda-lib
~/plfa.github.io/plfa.agda-lib
```

Next, create `~/.agda/defaults` and edit its contents to be:
```
standard-library
plfa
```

Finally, we need to enable the Emacs mode for Agda. To do so, run:

```
$ agda-mode setup
```

If all goes well, when you open a file ending in `.agda` or `.lagda` with Emacs, the buffer for that file should have the Agda major mode enabled by default!

## Fonts in Emacs

It is reccommended that you add the following to the end of your emacs configuration file at `~/.emacs`:
```
;; Setting up Fonts for use with Agda/PLFA on DICE machines:
;;
;; default to DejaVu Sans Mono, 
(set-face-attribute 'default nil
		    :family "DejaVu Sans Mono"
		    :height 120
		    :weight 'normal
		    :width  'normal)

;; fix \:
(set-fontset-font "fontset-default"
		  (cons (decode-char 'ucs #x2982)
			(decode-char 'ucs #x2982))
		  "STIX")
```

