---
title: Getting Started
permalink: /GettingStarted/
---

<!-- Status & Version Badges -->

[![CI][plfa-badge-status-svg]][plfa-badge-status-url]
[![pre-commit.ci status][pre-commit-status-svg]][pre-commit-status-url]
[![Release Version][plfa-badge-version-svg]][plfa-badge-version-url]
[![agda][agda-badge-version-svg]][agda-badge-version-url]
[![standard-library][agda-stdlib-version-svg]][agda-stdlib-version-url]

## Getting Started for Readers

You can read PLFA [online][plfa] without installing anything. However, if you wish to interact with the code or complete the exercises, you need several things:

- On macOS: [The XCode Command Line Tools](#on-macos-install-the-xcode-command-line-tools)
- [Git](#install-git)
- [GHC and Cabal](#install-ghc-and-cabal)
- [Agda](#install-agda)
- [Agda standard library](#install-plfa-and-the-agda-standard-library)
- [PLFA](#install-plfa-and-the-agda-standard-library)

PLFA is tested against specific versions of Agda and the standard library, which are shown in the badges above. Agda and the standard library change rapidly, and these changes often break PLFA, so using older or newer versions usually causes problems.

There are several versions of Agda and its standard library online. If you are using a package manager, like Homebrew or Debian apt, the version of Agda available there may be out of date. Furthermore, Agda is under active development, so if you install the development version from the GitHub, you might find the developers have introduced changes which break the code here. Therefore, it’s important to have the specific versions of Agda and the standard library shown above.

### On macOS: Install the XCode Command Line Tools

On macOS, you’ll need to install [The XCode Command Line Tools][xcode]. For most versions of macOS, you can install these by running the following command:

```bash
xcode-select --install
```

### Install Git

You can check whether you have Git by running the following command:

```bash
git --version
```

If you do not have Git, see [the Git downloads page][git].

### Install GHC and Cabal

Agda is written in Haskell, so to install it we’ll need the _Glorious Haskell Compiler_ and its package manager _Cabal_. PLFA should work with any version of GHC >=8.10, but is tested with versions 8.10 and 9.2. We recommend installing GHC and Cabal using [ghcup][ghcup].  For instance, once `ghcup` is installed, by typing

```bash
ghcup install ghc 9.2.4
ghcup install cabal recommended

ghcup set ghc 9.2.4
ghcup set cabal recommended
```
or using `ghcup tui` and choosing to `set` the appropriate tools.

### Install Agda

The easiest way to install Agda is using Cabal. PLFA uses Agda version 2.6.3. Run the following command:

```bash
cabal update
cabal install Agda-2.6.3
```

This step will take a long time and a lot of memory to complete.

If you have problems or for alternatives see the [Agda installation instructions][agda-readthedocs-installation].

If you'd like, you can [test to see if you've installed Agda correctly][agda-readthedocs-hello-world].

### Install PLFA and the Agda standard library

We recommend installing PLFA from Github into your home directory, by running the following command:

```bash
git clone --depth 1 --recurse-submodules --shallow-submodules https://github.com/plfa/plfa.github.io plfa
```

PLFA ships with the required version of the Agda standard library, so if you cloned with the `--recurse-submodules` flag, you’ve already got it, in the `standard-library` directory!

Finally, we need to let Agda know where to find the Agda standard library and PLFA. Two configuration files are required, one which lists paths to the libraries and one which specifies which libraries to load by default.

On macOS and Unix, if PLFA is installed in your home directory and you have no existing library configuration files you wish to preserve, run the following commands:

```bash
mkdir -p ~/.agda
cp ~/plfa/data/dotagda/* ~/.agda
```

This provides access to both the Agda standard library and to PLFA as an Agda library.

Otherwise, you will need to edit the appropriate files. Both configuration files are located in the directory `AGDA_DIR`. On UNIX and macOS, `AGDA_DIR` defaults to `~/.agda`. On Windows, `AGDA_DIR` usually defaults to `%AppData%\agda`, where `%AppData%` usually defaults to `C:\Users\USERNAME\AppData\Roaming`.

- If the `AGDA_DIR` directory does not already exist, create it.
- In `AGDA_DIR`, create a plain-text file called `libraries` containing `AGDA_STDLIB/standard-library.agda-lib`, where `AGDA_STDLIB` is the path to where the Agda standard library is located (e.g., `~/plfa/standard-library/`). This lets Agda know that an Agda library called `standard-library` is available.
- In `AGDA_DIR`, create a plain-text file called `defaults` containing _just_ the line `standard-library`.
- If you want to import modules from the book, you will also need to provide access to PLFA as an Agda library. To do so, let `PLFA` be the path to the root directory for PLFA.
  Add `PLFA/src/plfa.agda-lib` to `AGDA_DIR/libraries` and add `plfa` to `AGDA_DIR/defaults`, each on a line of their own.

More information about placing the standard libraries is available from [the Library Management page][agda-readthedocs-package-system] of the Agda documentation.

## Setting up an editor for Agda

### Emacs

The recommended editor for Agda is Emacs. To install Emacs:

- _On UNIX_, the version of Emacs in your repository is probably fine as long as it is fairly recent. There are also links to the most recent release on the [GNU Emacs downloads page][emacs].

- _On MacOS_, [Aquamacs][aquamacs] is probably the preferred version of Emacs, but GNU Emacs can also be installed via Homebrew or MacPorts. See the [GNU Emacs downloads page][emacs] for instructions.

- _On Windows_. See the [GNU Emacs downloads page][emacs] for instructions.

Make sure that you are able to open, edit, and save text files with your installation. The [tour of Emacs][emacs-tour] page on the GNU Emacs site describes how to access the tutorial within your Emacs installation.

Agda ships with the editor support for Emacs built-in, so if you’ve installed Agda, all you have to do to configure Emacs is run:

```bash
agda-mode setup
agda-mode compile
```

If you are already an Emacs user and have customized your setup, you may want to note the configuration which the `setup` appends to your `.emacs` file, and integrate it with your own preferred setup.

#### Auto-loading `agda-mode` in Emacs

Since version 2.6.0, Agda has had support for literate editing with Markdown, using the `.lagda.md` extension. One issue is that Emacs will default to Markdown editing mode for files with a `.md` suffix. In order to have `agda-mode` automatically loaded whenever you open a file ending with `.agda` or `.lagda.md`, add the following line to your Emacs configuration file:

```elisp
;; auto-load agda-mode for .agda and .lagda.md
(setq auto-mode-alist
   (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))
```

If you already have settings which change your `auto-mode-alist` in your configuration, put these _after_ the ones you already have or combine them if you are comfortable with Emacs Lisp. The configuration file for Emacs is normally located in `HOME/.emacs` or `HOME/.emacs.d/init.el`, but Aquamacs users might need to move their startup settings to the “Preferences.el” file in `HOME/Library/Preferences/Aquamacs Emacs/Preferences`. For Windows, see [the GNU Emacs documentation][emacs-home] for a description of where the Emacs configuration is located.

#### Optional: using the mononoki font with Emacs

Agda uses Unicode characters for many key symbols, and it is important that the font which you use to view and edit Agda programs shows these symbols correctly. The most important part is that the font you use has good Unicode support, so while we recommend [mononoki][font-mononoki], fonts such as [Source Code Pro][font-sourcecodepro], [DejaVu Sans Mono][font-dejavusansmono], and [FreeMono][font-freemono] are all good alternatives.

You can download and install mononoki directly from [the website][font-mononoki]. For most systems, installing a font is merely a matter of clicking the downloaded `.otf` or `.ttf` file. If your package manager offers a package for mononoki, that might be easier. For instance, Homebrew on macOS offers the `font-mononoki` package, and APT on Debian offers the `fonts-mononoki` package. To configure Emacs to use mononoki as its default font, add the following to the end of your Emacs configuration file:

```elisp
;; default to mononoki
(set-face-attribute 'default nil
                    :family "mononoki"
                    :height 120
                    :weight 'normal
                    :width  'normal)
```

#### Check if `agda-mode` was installed correctly

Open the first chapter of the book (`plfa/src/plfa/part1/Naturals.lagda.md`) in Emacs.  You can load and type-check the file by typing [`C-c C-l`][agda-readthedocs-emacs-notation].

#### Using `agda-mode` in Emacs

To load and type-check the file, use [`C-c C-l`][agda-readthedocs-emacs-notation].

Agda is edited interactively, using [“holes”][agda-readthedocs-holes], which are bits of the program that are not yet filled in. If you use a question mark as an expression, and load the buffer using `C-c C-l`, Agda replaces the question mark with a hole. There are several things you can to while the cursor is in a hole:

- `C-c C-c`: **c**ase split (asks for variable name)
- `C-c C-space`: fill in hole
- `C-c C-r`: **r**efine with constructor
- `C-c C-a`: **a**utomatically fill in hole
- `C-c C-,`: goal type and context
- `C-c C-.`: goal type, context, and inferred type

See [the emacs-mode docs][agda-readthedocs-emacs-mode] for more details.

If you want to see messages beside rather than below your Agda code, you can do the following:

- Open your Agda file, and load it using `C-c C-l`;
- type `C-x 1` to get only your Agda file showing;
- type `C-x 3` to split the window horizontally;
- move your cursor to the right-hand half of your frame;
- type `C-x b` and switch to the buffer called “Agda information”.

Now, error messages from Agda will appear next to your file, rather than squished beneath it.

#### Entering Unicode characters in Emacs with `agda-mode`

When you write Agda code, you will need to insert characters which are not found on standard keyboards. Emacs “agda-mode” makes it easier to do this by defining character translations: when you enter certain sequences of ordinary characters (the kind you find on any keyboard), Emacs will replace them in your Agda file with the corresponding special character.

For example, we can add a comment line to one of the `.agda` test files.
Let's say we want to add a comment line that reads:

```agda
{- I am excited to type ∀ and → and ≤ and ≡ !! -}
```

The first few characters are ordinary, so we would just type them as usual…

```agda
{- I am excited to type
```

But after that last space, we do not find ∀ on the keyboard. The code for this character is the four characters `\all`, so we type those four characters, and when we finish, Emacs will replace them with what we want…

```agda
{- I am excited to type ∀
```

We can continue with the codes for the other characters. Sometimes the characters will change as we type them, because a prefix of our character's code is the code of another character. This happens with the arrow, whose code is `\->`. After typing `\-` we see…

```agda
{- I am excited to type ∀ and -
```

…because the code `\-` corresponds to a hyphen of a certain width. When we add the `>`, the `-` becomes `→`! The code for `≤` is `\<=`, and the code for `≡` is `\==`.

```agda
{- I am excited to type ∀ and → and ≤ and ≡
```

Finally the last few characters are ordinary again…

```agda
{- I am excited to type ∀ and → and ≤ and ≡ !! -}
```

If you're having trouble typing the Unicode characters into Emacs, the end of each chapter should provide a list of the Unicode characters introduced in that chapter.

Emacs with `agda-mode` offers a number of useful commands, and two of them are especially useful when it comes to working with Unicode characters. For a full list of supported characters, use `agda-input-show-translations` with:

    M-x agda-input-show-translations

All the supported characters in `agda-mode` are shown.

If you want to know how you input a specific Unicode character in agda file, move the cursor onto the character and type the following command:

    M-x quail-show-key

You'll see the key sequence of the character in mini buffer.

### Spacemacs

[Spacemacs][spacemacs] is a “community-driven Emacs distribution” with native support for both Emacs and Vim editing styles. It comes with [integration for `agda-mode`][spacemacs-agda] out of the box. All that is required is that you enable the Agda layer in your `.spacemacs` file.

### Visual Studio Code

[Visual Studio Code][vscode] is a free source code editor developed by Microsoft. There is [a plugin for Agda support][vscode-agda] available on the Visual Studio Marketplace.

## Getting Started for Contributors

If you plan to build PLFA locally, please refer to [Contributing][plfa-contributing] for additional instructions.

<!-- Links -->

[plfa-badge-status-svg]: https://github.com/plfa/plfa.github.io/actions/workflows/ci.yml/badge.svg
[plfa-badge-status-url]: https://github.com/plfa/plfa.github.io/actions/workflows/ci.yml
[pre-commit-status-svg]: https://results.pre-commit.ci/badge/github/plfa/plfa.github.io/dev.svg
[pre-commit-status-url]: https://results.pre-commit.ci/latest/github/plfa/plfa.github.io/dev
[plfa-badge-version-svg]: https://img.shields.io/github/v/tag/plfa/plfa.github.io?label=release
[plfa-badge-version-url]: https://github.com/plfa/plfa.github.io/releases/latest
[agda-badge-version-svg]: https://img.shields.io/badge/agda-v2.6.3-blue.svg
[agda-badge-version-url]: https://github.com/agda/agda/releases/tag/v2.6.3.
[agda-stdlib-version-svg]: https://img.shields.io/badge/agda--stdlib-v1.7.2-blue.svg
[agda-stdlib-version-url]: https://github.com/agda/agda-stdlib/releases/tag/v1.7.2
[plfa]: https://plfa.inf.ed.ac.uk
[plfa-epub]: https://plfa.github.io/plfa.epub
[plfa-contributing]: https://plfa.github.io/Contributing/
[ghcup]: https://www.haskell.org/ghcup/
[git]: https://git-scm.com/downloads
[xcode]: https://developer.apple.com/xcode/
[agda-readthedocs-installation]: https://agda.readthedocs.io/en/v2.6.3/getting-started/installation.html
[agda-readthedocs-hello-world]: https://agda.readthedocs.io/en/v2.6.3/getting-started/hello-world.html
[agda-readthedocs-holes]: https://agda.readthedocs.io/en/v2.6.3/getting-started/a-taste-of-agda.html#preliminaries
[agda-readthedocs-emacs-mode]: https://agda.readthedocs.io/en/v2.6.3/tools/emacs-mode.html
[agda-readthedocs-emacs-notation]: https://agda.readthedocs.io/en/v2.6.3/tools/emacs-mode.html#notation-for-key-combinations
[agda-readthedocs-package-system]: https://agda.readthedocs.io/en/v2.6.3/tools/package-system.html#example-using-the-standard-library
[emacs]: https://www.gnu.org/software/emacs/download.html
[emacs-tour]: https://www.gnu.org/software/emacs/tour/
[emacs-home]: https://www.gnu.org/software/emacs/manual/html_node/efaq-w32/Location-of-init-file.html
[aquamacs]: https://aquamacs.org/
[spacemacs]: https://www.spacemacs.org/
[spacemacs-agda]: https://develop.spacemacs.org/layers/+lang/agda/README.html
[vscode]: https://code.visualstudio.com/
[vscode-agda]: https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode
[font-sourcecodepro]: https://github.com/adobe-fonts/source-code-pro
[font-dejavusansmono]: https://dejavu-fonts.github.io/
[font-freemono]: https://www.gnu.org/software/freefont/
[font-mononoki]: https://madmalik.github.io/mononoki/
[font-mononoki-debian]: https://packages.debian.org/sid/fonts/fonts-mononoki
