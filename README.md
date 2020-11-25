---
layout: page
title: Getting Started
permalink: /GettingStarted/
---

<!-- Status & Version Badges -->
[![Calendar Version][plfa-calver]][plfa-latest]
[![Build Status][plfa-status]][plfa-travis]
[![Agda][agda-version]][agda]
[![agda-stdlib][agda-stdlib-version]][agda-stdlib]


## Dependencies for users

You can read PLFA [online][plfa] without installing anything.
However, if you wish to interact with the code or complete the exercises, you need several things:

  - A specific version of [Agda][agda], which needs several other
    software systems
  - The [Agda standard library][agda-stdlib]
  - [PLFA][plfa-dev]

PLFA is tested against specific versions of Agda and the standard library, which are shown in the badges above. Agda and the standard library change rapidly, and these changes often break PLFA, so using older or newer versions usually causes problems.  If you are
using a Mac or linux repository system (like brew or Debian apt), then
the version of Agda which the repository holds may be out-of-date for
what PLFA expects.  Agda is under active development, so if
you install the development version of Agda from its GitHub
repository, you may find that the developers have introduced changes
which break the code here.  So it is important to have the specific
versions of Agda and its libraries shown above.

You will also need an editor for writing and changing Agda source
code.  Agda's best IDE is in Emacs, and we include steps below or
installing Emacs, familiarizing yourself with its basic editing
features, and with its Agda mode.

### Consider a virtual machine if you are running Windows

Agda seems to be tricky to install on Windows, and students often
report issues completing their installations.  If you are working on a
Windows computer, you should consider running a linux system via a
virtual machine within Windows, and install Agda there.  [Virtual
Box][virtualbox] is a fairly simple and open-source solution which
runs on both Windows and Macintosh hosts.

Note that on many computers, hardware virtualization is disabled by
default.  If this is the case on your computer, the virtual machine
will appear as just a blank black screen, and will not actually run.
To allow hardware virtualization, you must activate it from BIOS when
you first turn on your machine.  Check the documentation for your
particular computer model for instructions on accessing its BIOS.

### On Macs, install the [Xcode Developer Tools][applexcode]

Include at least the Developer Tools Essentials and UNIX Development
Support modules.

### Install the Haskell Tool Stack {#stack}

Agda is built against the [Haskell Tool Stack][haskell-stack], and
outputs code for the GHC compiler, so as a preliminary step you will
need to install these systems.

 1. **Install Stack.**

    - *On Unix systems (including linux and Macs)*.  Your repository
       probably offers Stack as a pre-packaged software, and this
       option is probably the easiest.  For example, on Debian the
       package is `haskell-stack`.  Alternatively, there are
       instructions for downloading and running a shell script on the
       [Stack site][haskell-stack].

      Once you have Stack installed, make sure you include its binary
      installation area in your `PATH` by including a line like
      ```bash
      export PATH=${HOME}/.local/bin:${PATH}
      ```
      in your `${HOME}/.bashrc` or `${HOME}/.profile` file.

    - *On Windows*.  There is a 64-bit Windows installer on the [Stack
       site][haskell-stack].

 2. **Update Stack.** Stack is able to update itself.  So after you
    install it, run the command
    ```bash
    stack upgrade
    ```

### Install GHC and Cabal {#cabal}

These systems are used for installing Agda, and for its runtme
environment.  

 - *With Unix repository systems*.  Again, your repository is
    probably the easiest option; an exact version for these more
    stable systems is less of an issue than with Agda itself.  On
    Debian, for example, the necessary packages are
    ```bash
    sudo apt-get install ghc cabal-install
    ```
    and packages `ghc-doc` and `haskell-mode` are also nice to
    have.

 - *On Windows*.  See the [Haskell Platform site][haskell-windows].

### Install Git {#git}

You will need Git to access the specific version of Agda we use.  If
you do not already have Git installed on your system, see the [git
downloads page][gitscm].

### Install the core Agda system {#core}

To install the specific version of Agda we need, we will first
download that version, and then ask Stack to install it for us.

 1. *Download Agda*.  If you have installed Git, you can fetch a copy
    of Agda with:
    ```bash
    git clone https://github.com/agda/agda.git
    cd agda
    git checkout v2.6.0.1
    ```

    The last step may give you notices about being in "'detached HEAD'
    state" --- it's fine.  The success message you hope to see is
    `Note: switching to 'v2.6.0.1'`.

    Alternatively, you can download a ZIP archive of that version from
    [the GitHub site][agda].

 2. *Base Agda installation.*  From the Agda source directory, run:

    ```bash
    stack install --stack-yaml stack-8.6.5.yaml
    ```

    **This step will take a while to complete.** Moreover, if your
    system is old or fragile, then your best results may come from
    exiting other programs and leaving it alone to complete.

    Be sure to watch the output of Stack for any further instructions
    it gives you.

 3. You may need to make sure that the new `agda` binary is in your
    executables path.  On most linux systems (and I assume Mac), Stack
    will add binaries to `~/.local/bin`, so you would add a line (or
    modify an existing line) like

        export PATH=~/.local/bin:$PATH

    For information about Stack and Windows executables, see [the
    Stack FAQ][stackAndWindows].
 
*Verify the base Agda system*.  After these three steps succeed, you
should be able to load Agda files which do not use any external
libraries:

 - Create a file `testdefs.agda` with these lines (keep the
   indentation of the second and third lines as shown):

       data Switch : Set where
         on : Switch
         off : Switch

       oneSwitchSettings : Switch
       oneSwitchSettings = on

 - From a command line, change to the same directory where your
   `testdefs.agda` file is located.  Then enter the command:

       agda -v 2 testdefs.agda

   You should see a short message like

       Loading  testdefs (/path/to/your/directory/testdefs.agdai).

   or

       Checking  testdefs (/path/to/your/directory/testdefs.agdai).

   but without any reported errors.
   
### Install the Agda standard libraries {#stdlib}

 1. *Download the standard libraries*.  This is similar to downloading
    Agda itself:
    
    ```bash
    git clone https://github.com/agda/agda-stdlib.git
    cd agda-stdlib
    git checkout v1.1
    ```

    Again, it is possible as an alternative to download a ZIP archive
    of that version from [the library GitHub site][agda-stdlib].

    Take note of where you have checked out this directory.  In what
    follows, if you were in the directory `/above/the/lib` when you
    ran Git, then we will refer to the directory
    `/above/the/lib/agda-stdlib` as `AGDA_STDLIB`.  You should see
    several subdirectories and files in that directory, such as
    `AGDA_STDLIB/standard-library.agda-lib` and
    `AGDA_STDLIB/src/Data/Nat.agda`.

 2. *Figure out where your user Agda configuration should be*.  In
    what follows, we will refer to this user Agda configuration as
    `AGDA_DIR`.

     - On linux and Macs, `AGDA_DIR` is `~/.agda`.

     - On Windows systems, `AGDA_DIR` _usually_ defaults to
       `C:\Users\USERNAME\AppData\Roaming\agda` or something similar,
       but on Windows it is generally best to explicitly create and
       directory, and set the `AGDA_DIR` environment variable to its
       path.

 3. Create the directory `AGDA_DIR` if it does not already exist.

 4. Create a plain-text file called `AGDA_DIR/libraries` containing
    the line

        AGDA_STDLIB/standard-library.agda-lib

    replacing `AGDA_STDLIB` with the name of the directory from Step 1
    of this section.

 5. Create a plain-text file called `AGDA_DIR/defaults` containing
    the line

        standard-library

More information about placing the standard libraries is available
from [the Library Management page][agda-docs-package-system] of the
Agda documentation.

*Verify the Agda standard libraries installation*.  After the above
steps succeed, you should be able to load Agda files which use
standard libraries:

 - Create a file `testnats.agda` with these lines (keep the
   indentation of the second and third lines as shown):

       open import Data.Nat
       x : ℕ
       x = 10

   Note that the ℕ is a Unicode character, not a plain capital N.  You
   should be able to just copy-and-paste it from this page into your
   file.

 - From a command line, change to the same directory where your
   `testnats.agda` file is located.  Then enter the command:

       agda -v 2 testnats.agda

   You should see several lines describing the external libraries
   which Agda loads on behalf of your file, such as:

       Loading  Agda.Builtin.Equality (/path/to/some/directory/Agda/Builtin/Equality.agdai).
          Loading  Level (/path/to/some/directory/Level.agdai).
         Loading  Data.Empty (/path/to/some/directory/Data/Empty.agdai).

And there is one other important thing to remember:

#### Leave the configuration directories which you made alone!

Do not put your other projects and exercises code there!  Keep them
separate, and put them in a different directory than what you use for
your classwork.  It is important not use these configuration
directories for other projects in a way that might make it easy for
you to tamper with the contents.

### Install PLFA {#plfa}

You can get the latest version of Programming Language Foundations in Agda from GitHub, either by cloning the repository, or by downloading [the zip archive][plfa-dev]:
```bash
git clone https://github.com/plfa/plfa.github.io
```

It is usually a good idea to also set up the PLFA sources as an Agda
library as well.  If you want to import PLFA modules into your Agda
files — which is necessary for loading later sections of PLFA — then
you _must_ set up the PLFA sources as an Agda library.  To do so,

 1. Add the full path of the `PLFA` directory to `~/.agda/libraries`
    on its own line.
        
 2. Add `plfa` (lower-case!) to `~/.agda/defaults`, again on a line of
    its own.

If you are using this book for a class, your instructor might add
exercises or explanations over the term.  So you should probably keep
*two* local versions:

 - One which you keep "clean" and updated from the repository without
   changes.  To receive updates on the clean copy from the repository,
   open a command-line shell in the clean copy's directory, and type

       git pull

   It is this clean copy which you should set as your Agda library as
   the steps above describe.

 - One which you use as a sandbox and for exercises, refreshing
   individual files from the clean copy as needed.

## Setting up and using Emacs

### Install Emacs, and familiarize yourself with it {#emacs}

Emacs is a text editor which serves as Agda's IDE.

To install Emacs:

 - *On linux systems*, the version of GNU Emacs in your repository is
    probably fine as long as it is fairly recent.  There are also
    links to the most recent release on the [GNU Emacs downloads
    page][gnuemacsDownload].

 - *On MacOS*, [Aquamacs][aquamacs] is the generally preferred version
    of Emacs; the Agda wiki notes that people have had success with
    agda-mode on Aquamacs.

 - *On Windows*.  See the [GNU Emacs downloads page][gnuemacsDownload]
    for instructions.

Make sure that you are able to open, edit, and save text files with
your installation.  The [tour of Emacs][emacstour] page on the GNU
Emacs site describes how to access the tutorial within your Emacs
installation.

### Install and configure agda-mode {#agdamode}

The recommended editor for Agda is Emacs with `agda-mode`. Agda ships
with `agda-mode`, so if you’ve installed Agda, all you have to do to
configure `agda-mode` is run:

```bash
agda-mode setup
agda-mode compile
```

If you are already an Emacs user and have customized your setup, you
may want to note the configuration which the `setup` appends to your
`.emacs` file, and integrate it with your own preferred setup.

*Verify agda-mode*.  Open the `testnats.agda` file which you set up
earlier.  Load and type-check the file by typing
[`C-c C-l`][agda-docs-emacs-notation].

*Auto-loading `agda-mode` in Emacs*.  Since version 2.6.0, Agda has
had support for literate editing with Markdown, using the `.lagda.md`
extension.  One issue is that Emacs will default to Markdown editing
mode for files with a `.md` suffix.  In order to have `agda-mode`
automatically loaded whenever you open a file ending with `.agda` or
`.lagda.md`, all the following line to your Emacs configuration file:

```elisp
(setq auto-mode-alist
   (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))
```

If you already have settings to `auto-mode-alist` in your
configuration, put these *after* the ones you already have (or combine
them, if you are comfortable with Emacs Lisp).  The configuration file
for Emacs is normally located in `~/.emacs` or `~/.emacs.d/init.el`,
but Aquamacs users might need to move their startup settings to the
`Preferences.el` file in `~/Library/Preferences/Aquamacs
Emacs/Preferences`.

### The mononoki font {#mononoki}

Agda uses Unicode characters for many key symbols, and it is important
that the font which you use to view and edit Agda programs shows these
symbols correctly.  So we recommend that you install the font
[mononoki][mononoki] and direct Emacs to use it.

 1. *Install mononoki*.  You can install directly from a download
    from [mononoki's GitHub][mononoki], but it may be easier if your
    system repository provided a pre-packaged version.

    For example, on Debian and Ubuntu `apt` there is [a package
    `fonts-mononoki`][debianMononoki].

 2. *Using mononoki from Emacs*.  Add the following to the end of your
    emacs configuration file `~/.emacs`:

    ``` elisp
    ;; default to mononoki
    (set-face-attribute 'default nil
    		        :family "mononoki"
    		        :height 120
    		        :weight 'normal
    		        :width  'normal)
    ```

### Entering Unicode characters in Emacs `agda-mode` {#unicode}

When you write Agda code, you will need to insert characters which are
not found on standard keyboards.  Emacs `agda-mode` makes it easier to
do this by defining character translations: when you enter certain
sequences of ordinary characters (the kind you find on any keyboard),
Emacs will replace them in your Agda file with the corresponding
special character.

For example, we can add a comment line to one of the `.agda` test
files.  Let's say we want to add a comment line that reads

```
{- I am excited to type ∀ and → and ≤ and ≡ !! -}
```

 - The first few characters are ordinary, so we would just type them as usual

   ```
   {- I am excited to type 
   ```

 - But after that last space, we do not find ∀ on the keyboard.  The
   code for this character is the four characters `\all` --- so we
   type those four characters, and when we finish, Emacs will replace
   them with what we want


   ```
   {- I am excited to type ∀
   ```

 - We can continue with the codes for the other characters.  Sometimes
   the characters will change as we type them, because a prefix of our
   character's code is the code of another character.  This happens
   with the arrow, whose code is `\->`.  After typing `\-` we see

   ```
   {- I am excited to type ∀ and ­
   ```

   because the code `\->` corresponds to a hyphen of a certain width.
   When we add the `>`, the `­` becomes `→`.

 - The code for `≤` is `\<=`, and the code for `≡` is `\==`.
 
   ```
   {- I am excited to type ∀ and → and ≤ and ≡
   ```

 - Finally the last few characters are ordinary again,
 
   ```
   {- I am excited to type ∀ and → and ≤ and ≡ !! -}
   ```

The end of each chapter of PLFA provides a list of the
Unicode characters introduced in that chapter.

Emacs and `agda-mode` have a number of commands which can help you
use Unicode characters when you solve exercises:

 - For a full list of supported characters, use
   `agda-input-show-translations` with:

      M-x agda-input-show-translations

   All the supported characters in `agda-mode` are shown.

 - If you want to know how you input a specific Unicode character in
   agda file, move the cursor onto the character and type the
   following command:

      M-x quail-show-key

   You'll see the key sequence of the character in minibuffer, usually
   at the bottom of your window.

### Whitespace sensitivity {#whitespace}

One important fact that you should know about Agda is that it is
*whitespace-sensitive*.  The presence or absence of indentation on a
line of code can impact the meaning of that line of code.  Python is
another example of a whitespace-sensitive language which you may have
seen.  Java, C and C++ are not whitespace-sensitive.  Pay attention to
the indentation that you see in sample code, and use those same
indentation patterns in the code that you write.

### Using Emacs as your Agda IDE

To load and type-check a file, use [`C-c C-l`][agda-docs-emacs-notation].

Agda is edited “interactively,” which means that one can type check code which is not yet complete: if a question mark (?) is used as a placeholder for an expression, and the buffer is then checked, Agda will replace the question mark with a “hole” which can be filled in later. One can also do various other things in the context of a hole: listing the context, inferring the type of an expression, and even evaluating an open term which mentions variables bound in the surrounding context.”

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


## Dependencies for developers

PLFA is available as both a website and an EPUB e-book, both of which can be built on Linux and macOS.
PLFA is written in literate Agda with [Kramdown Markdown][kramdown].


### Git hooks

The repository comes with several Git hooks:

 1. The [fix-whitespace][fix-whitespace] program is run to check for whitespace violations.

 2. The test suite is run to check if everything type checks.

You can install these Git hooks by calling `make init`.
You can install [fix-whitespace][fix-whitespace] by running:
```bash
git clone https://github.com/agda/fix-whitespace
cd fix-whitespace/
stack install --stack-yaml stack-8.8.3.yaml
```
If you want Stack to use your system installation of GHC, you can pass the `--system-ghc` flag and select the appropriate `stack-*.yaml` file, like when installing [Agda](#installing-agda-using-stack).


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
You can install the remainder of the dependencies—[Jekyll][ruby-jekyll], [html-proofer][ruby-html-proofer], *etc.*—by running:
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

The [EPUB version][epub] of the book is built using Pandoc.

Install a recent version of Pandoc, [available here][pandoc]. The easiest way to install Pandoc is using their official installer, which is much faster than compiling Pandoc from source with Haskell Stack.

Once you’ve installed Pandoc, you can build the EPUB by running:
```bash
make epub
```
The EPUB is written to `out/epub/plfa.epub`.


## Optional: Enable generating standalone binaries {#standalone}

This section is optional if all you want to do is debug and load the
exercises in this book and similar definitions, and evaluate
expressions using them.

Enter the following commands at the command line:

    ```bash
    cabal v2-repl --build-dep fail
    cabal v2-install --lib Agda ieee754 -v
    ```

**The second command will take a while to complete.** Moreover, if
your system is old or fragile, then your best results may come from
exiting other programs and leaving it alone to complete.

*Verifying standalone binary generation.* After these commands
succeed, you should be able to compile and run a Hello World program:

 - Create a new directory, and save the following lines as the file
   `hello-world.agda`:
   
   ```
   module hello-world where
   open import IO
   main = run (putStrLn "Hello, World!")
   ```

 - From that directory, run the command
 
   ```bash
   agda --compile hello-world.agda
   ```

   The first time you run this command, it will need to compile many
   library files.  Note also that it will generate a directory
   `MAlonzo`, which you can ignore.

 - You should then see an executable file `hello-world`, which you can
   run for a nice message.

*Verifying agda-mode for standalone binaries*.  Create a file
`hello-world.agda`,

```
module hello-world where

open import IO

main = run (putStrLn "Hello, World!")
```

 - To load and type-check the file, use
   [`C-c C-l`][agda-docs-emacs-notation].

 - To compile the file and generate the executable, use `C-c C-x C-c`.
   This will not actually run the executable file, but you can run it
   yourself from the command line.

### Appendix: note to system administrators installing on shared file systems {#sharedlib}

Some attention is required when installing Agda's libraries on a
shared file system.  The standard library as shipped contains `.agda`
files, and not the compiled `.agdai` images (which of course will
vary from system to system).  When an `.agdai` file does not exist for
a file from a library, Agda will attempt to compile that file _and
store the resulting `.agdai` file right alongside the `.agda` source_.
This tends to fail on shared file systems, because general accounts
will not (and should not) have write-access to shared files.

I believe that loading the two files below into Agda from an account
with privilege to write to the shared file area should create `.agdai`
files for all of the standard library.  Be sure to inspect the shared
files to make sure that both the `.agda` and `.agdai` files are
world-readable.  To load the files:

    agda -v 2 importall.agda
    agda -v 2 importall2.agda

 - File `importall.agda`

       module importall where
         open import Algebra
         open import Function
         open import IO
         open import Induction
         open import Level
         open import Record
         open import Reflection
         open import Size
         open import Strict
         open import Universe
         open import Algebra.FunctionProperties
         open import Algebra.Morphism
         open import Algebra.Structures
         open import Algebra.Construct.LiftedChoice
         open import Algebra.Construct.NaturalChoice.Max
         open import Algebra.Construct.NaturalChoice.Min
         open import Algebra.FunctionProperties.Consequences
         open import Algebra.FunctionProperties.Core
         open import Algebra.FunctionProperties.Consequences.Core
         open import Algebra.FunctionProperties.Consequences.Propositional
         open import Algebra.Operations.CommutativeMonoid
         open import Algebra.Operations.Semiring
         open import Algebra.Properties.AbelianGroup
         open import Algebra.Properties.BooleanAlgebra
         open import Algebra.Properties.CommutativeMonoid
         open import Algebra.Properties.DistributiveLattice
         open import Algebra.Properties.Group
         open import Algebra.Properties.Lattice
         open import Algebra.Properties.Ring
         open import Algebra.Properties.Semilattice
         open import Algebra.Properties.BooleanAlgebra.Expression
         open import Algebra.Solver.CommutativeMonoid
         open import Algebra.Solver.IdempotentCommutativeMonoid
         open import Algebra.Solver.Monoid
         open import Algebra.Solver.Ring
         open import Algebra.Solver.CommutativeMonoid.Example
         open import Algebra.Solver.IdempotentCommutativeMonoid.Example
         open import Algebra.Solver.Ring.AlmostCommutativeRing
         open import Algebra.Solver.Ring.Lemmas
         open import Algebra.Solver.Ring.NaturalCoefficients
         open import Algebra.Solver.Ring.Simple
         open import Algebra.Solver.Ring.NaturalCoefficients.Default
         open import Axiom.DoubleNegationElimination
         open import Axiom.ExcludedMiddle
         open import Axiom.UniquenessOfIdentityProofs
         open import Axiom.Extensionality.Heterogeneous
         open import Axiom.Extensionality.Propositional
         open import Axiom.UniquenessOfIdentityProofs.WithK
         open import Category.Applicative
         open import Category.Comonad
         open import Category.Functor
         open import Category.Monad
         open import Category.Applicative.Indexed
         open import Category.Applicative.Predicate
         open import Category.Functor.Predicate
         open import Category.Monad.Continuation
         open import Category.Monad.Indexed
         open import Category.Monad.Partiality
         open import Category.Monad.Predicate
         open import Category.Monad.Reader
         open import Category.Monad.State
         open import Category.Monad.Partiality.All
         open import Codata.Cofin
         open import Codata.Colist
         open import Codata.Conat
         open import Codata.Covec
         open import Codata.Cowriter
         open import Codata.Delay
         open import Codata.M
         open import Codata.Stream
         open import Codata.Thunk
         open import Codata.Cofin.Literals
         open import Codata.Colist.Bisimilarity
         open import Codata.Colist.Categorical
         open import Codata.Colist.Properties
         open import Codata.Conat.Bisimilarity
         open import Codata.Conat.Literals
         open import Codata.Conat.Properties
         open import Codata.Covec.Bisimilarity
         open import Codata.Covec.Categorical
         open import Codata.Covec.Properties
         open import Codata.Delay.Bisimilarity
         open import Codata.Delay.Categorical
         open import Codata.Delay.Properties
         open import Codata.M.Bisimilarity
         open import Codata.M.Properties
         open import Codata.Musical.Cofin
         open import Codata.Musical.Colist
         open import Codata.Musical.Conat
         open import Codata.Musical.Costring
         open import Codata.Musical.Covec
         open import Codata.Musical.M
         open import Codata.Musical.Notation
         open import Codata.Musical.Stream
         open import Codata.Musical.Colist.Infinite-merge
         open import Codata.Musical.M.Indexed
         open import Codata.Stream.Bisimilarity
         open import Codata.Stream.Categorical
         open import Codata.Stream.Properties
         open import Data.AVL
         open import Data.Bin
         open import Data.Bool
         open import Data.BoundedVec
         open import Data.Char
         open import Data.Container
         open import Data.DifferenceList
         open import Data.DifferenceNat
         open import Data.DifferenceVec
         open import Data.Digit
         open import Data.Empty
         open import Data.Fin
         open import Data.Float
         open import Data.Integer
         open import Data.List
         open import Data.Maybe
         open import Data.Nat
         open import Data.Plus
         open import Data.Product
         open import Data.Rational
         open import Data.Record
         open import Data.ReflexiveClosure
         open import Data.Sign
         open import Data.Star
         open import Data.String
         open import Data.Sum
         open import Data.Table
         open import Data.These
         open import Data.Trie
         open import Data.Unit
         open import Data.Universe
         open import Data.Vec
         open import Data.W
         open import Data.Word
         open import Data.AVL.Height
         open import Data.AVL.Indexed
         open import Data.AVL.IndexedMap
         open import Data.AVL.Key
         open import Data.AVL.NonEmpty
         open import Data.AVL.Sets
         open import Data.AVL.Indexed.WithK
         open import Data.AVL.NonEmpty.Propositional
         open import Data.Bin.Properties
         open import Data.Bool.Base
         open import Data.Bool.Properties
         open import Data.Bool.Show
         open import Data.Bool.Solver
         open import Data.BoundedVec.Inefficient
         open import Data.Char.Base
         open import Data.Char.Properties
         open import Data.Container.Any
         open import Data.Container.Combinator
         open import Data.Container.Core
         open import Data.Container.FreeMonad
         open import Data.Container.Indexed
         open import Data.Container.Membership
         open import Data.Container.Properties
         open import Data.Container.Related
         open import Data.Container.Combinator.Properties
         open import Data.Container.Indexed.Combinator
         open import Data.Container.Indexed.Core
         open import Data.Container.Indexed.FreeMonad
         open import Data.Container.Indexed.WithK
         open import Data.Container.Morphism.Properties
         open import Data.Container.Relation.Binary.Pointwise
         open import Data.Container.Relation.Binary.Equality.Setoid
         open import Data.Container.Relation.Binary.Pointwise.Properties
         open import Data.Container.Relation.Unary.All
         open import Data.Container.Relation.Unary.Any
         open import Data.Container.Relation.Unary.Any.Properties
         open import Data.Empty.Irrelevant
         open import Data.Fin.Base
         open import Data.Fin.Dec
         open import Data.Fin.Induction
         open import Data.Fin.Literals
         open import Data.Fin.Permutation
         open import Data.Fin.Properties
         open import Data.Fin.Subset
         open import Data.Fin.Substitution
         open import Data.Fin.Permutation.Components
         open import Data.Fin.Subset.Properties
         open import Data.Fin.Substitution.Example
         open import Data.Fin.Substitution.Lemmas
         open import Data.Fin.Substitution.List
         open import Data.Float.Unsafe
         open import Data.Graph.Acyclic
         open import Data.Integer.Base
         open import Data.Integer.Coprimality
         open import Data.Integer.DivMod
         open import Data.Integer.Divisibility
         open import Data.Integer.Literals
         open import Data.Integer.Properties
         open import Data.Integer.Solver
         open import Data.Integer.Divisibility.Signed
         open import Data.List.All
         open import Data.List.Any
         open import Data.List.Base
         open import Data.List.Categorical
         open import Data.List.Countdown
         open import Data.List.Extrema
         open import Data.List.Literals
         open import Data.List.NonEmpty
         open import Data.List.Properties
         open import Data.List.Reverse
         open import Data.List.Solver
         open import Data.List.Zipper
         open import Data.List.All.Properties
         open import Data.List.Any.Properties
         open import Data.List.Extrema.Core
         open import Data.List.Extrema.Nat
         open import Data.List.Membership.DecPropositional
         open import Data.List.Membership.DecSetoid
         open import Data.List.Membership.Propositional
         open import Data.List.Membership.Setoid
         open import Data.List.Membership.Propositional.Properties
         open import Data.List.Membership.Propositional.Properties.Core
         open import Data.List.Membership.Propositional.Properties.WithK
         open import Data.List.Membership.Setoid.Properties
         open import Data.List.NonEmpty.Categorical
         open import Data.List.NonEmpty.Properties
         open import Data.List.Relation.BagAndSetEquality
         open import Data.List.Relation.Pointwise
         open import Data.List.Relation.Binary.BagAndSetEquality
         open import Data.List.Relation.Binary.Pointwise
         open import Data.List.Relation.Binary.Disjoint.Propositional
         open import Data.List.Relation.Binary.Disjoint.Setoid
         open import Data.List.Relation.Binary.Disjoint.Setoid.Properties
         open import Data.List.Relation.Binary.Equality.DecPropositional
         open import Data.List.Relation.Binary.Equality.DecSetoid
         open import Data.List.Relation.Binary.Equality.Propositional
         open import Data.List.Relation.Binary.Equality.Setoid
         open import Data.List.Relation.Binary.Lex.Core
         open import Data.List.Relation.Binary.Lex.NonStrict
         open import Data.List.Relation.Binary.Lex.Strict
         open import Data.List.Relation.Binary.Permutation.Homogeneous
         open import Data.List.Relation.Binary.Permutation.Inductive
         open import Data.List.Relation.Binary.Permutation.Propositional
         open import Data.List.Relation.Binary.Permutation.Setoid
         open import Data.List.Relation.Binary.Permutation.Inductive.Properties
         open import Data.List.Relation.Binary.Permutation.Propositional.Properties
         open import Data.List.Relation.Binary.Permutation.Setoid.Properties
         open import Data.List.Relation.Binary.Prefix.Heterogeneous
         open import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties
         open import Data.List.Relation.Binary.Sublist.DecPropositional
         open import Data.List.Relation.Binary.Sublist.DecSetoid
         open import Data.List.Relation.Binary.Sublist.Heterogeneous
         open import Data.List.Relation.Binary.Sublist.Propositional
         open import Data.List.Relation.Binary.Sublist.Setoid
         open import Data.List.Relation.Binary.Sublist.DecPropositional.Solver
         open import Data.List.Relation.Binary.Sublist.DecSetoid.Solver
         open import Data.List.Relation.Binary.Sublist.Heterogeneous.Core
         open import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
         open import Data.List.Relation.Binary.Sublist.Heterogeneous.Solver
         open import Data.List.Relation.Binary.Sublist.Propositional.Properties
         open import Data.List.Relation.Binary.Sublist.Setoid.Properties
         open import Data.List.Relation.Binary.Subset.Propositional
         open import Data.List.Relation.Binary.Subset.Setoid
         open import Data.List.Relation.Binary.Subset.Propositional.Properties
         open import Data.List.Relation.Binary.Subset.Setoid.Properties
         open import Data.List.Relation.Binary.Suffix.Heterogeneous
         open import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties
         open import Data.List.Relation.Equality.DecPropositional
         open import Data.List.Relation.Equality.DecSetoid
         open import Data.List.Relation.Equality.Propositional
         open import Data.List.Relation.Equality.Setoid
         open import Data.List.Relation.Lex.Core
         open import Data.List.Relation.Lex.NonStrict
         open import Data.List.Relation.Lex.Strict
         open import Data.List.Relation.Permutation.Inductive
         open import Data.List.Relation.Permutation.Inductive.Properties
         open import Data.List.Relation.Sublist.Propositional
         open import Data.List.Relation.Sublist.Propositional.Properties
         open import Data.List.Relation.Subset.Propositional
         open import Data.List.Relation.Subset.Setoid
         open import Data.List.Relation.Subset.Propositional.Properties
         open import Data.List.Relation.Subset.Setoid.Properties
         open import Data.List.Relation.Ternary.Interleaving
         open import Data.List.Relation.Ternary.Interleaving.Properties
         open import Data.List.Relation.Ternary.Interleaving.Propositional
         open import Data.List.Relation.Ternary.Interleaving.Setoid
         open import Data.List.Relation.Ternary.Interleaving.Propositional.Properties
         open import Data.List.Relation.Ternary.Interleaving.Setoid.Properties
         open import Data.List.Relation.Unary.All
         open import Data.List.Relation.Unary.AllPairs
         open import Data.List.Relation.Unary.Any
         open import Data.List.Relation.Unary.First
         open import Data.List.Relation.Unary.All.Properties
         open import Data.List.Relation.Unary.AllPairs.Core
         open import Data.List.Relation.Unary.AllPairs.Properties
         open import Data.List.Relation.Unary.Any.Properties
         open import Data.List.Relation.Unary.First.Properties
         open import Data.List.Relation.Unary.Unique.Propositional
         open import Data.List.Relation.Unary.Unique.Setoid
         open import Data.List.Relation.Unary.Unique.Propositional.Properties
         open import Data.List.Relation.Unary.Unique.Setoid.Properties
         open import Data.List.Zipper.Properties
         open import Data.Maybe.Base
         open import Data.Maybe.Categorical
         open import Data.Maybe.Properties
         open import Data.Maybe.Relation.Binary.Pointwise
         open import Data.Maybe.Relation.Unary.All
         open import Data.Maybe.Relation.Unary.Any
         open import Data.Maybe.Relation.Unary.All.Properties
         open import Data.Nat.Base
         open import Data.Nat.Coprimality
         open import Data.Nat.DivMod
         open import Data.Nat.Divisibility
         open import Data.Nat.GCD
         open import Data.Nat.GeneralisedArithmetic
         open import Data.Nat.Induction
         open import Data.Nat.InfinitelyOften
         open import Data.Nat.LCM
         open import Data.Nat.Literals
         open import Data.Nat.Primality
         open import Data.Nat.Properties
         open import Data.Nat.Show
         open import Data.Nat.Solver
         open import Data.Nat.WithK
         open import Data.Nat.DivMod.Core
         open import Data.Nat.DivMod.WithK
         open import Data.Nat.Divisibility.Core
         open import Data.Nat.GCD.Lemmas
         open import Data.Product.N-ary
         open import Data.Product.Properties
         open import Data.Product.Categorical.Examples
         open import Data.Product.Categorical.Left
         open import Data.Product.Categorical.Right
         open import Data.Product.Categorical.Left.Base
         open import Data.Product.Categorical.Right.Base
         open import Data.Product.Function.Dependent.Propositional
         open import Data.Product.Function.Dependent.Setoid
         open import Data.Product.Function.Dependent.Propositional.WithK
         open import Data.Product.Function.Dependent.Setoid.WithK
         open import Data.Product.Function.NonDependent.Propositional
         open import Data.Product.Function.NonDependent.Setoid
         open import Data.Product.N-ary.Categorical
         open import Data.Product.N-ary.Properties
         open import Data.Product.Nary.NonDependent
         open import Data.Product.Properties.WithK
         open import Data.Product.Relation.Binary.Lex.NonStrict
         open import Data.Product.Relation.Binary.Lex.Strict
         open import Data.Product.Relation.Binary.Pointwise.Dependent
         open import Data.Product.Relation.Binary.Pointwise.NonDependent
         open import Data.Product.Relation.Binary.Pointwise.Dependent.WithK
         open import Data.Product.Relation.Lex.NonStrict
         open import Data.Product.Relation.Lex.Strict
         open import Data.Product.Relation.Pointwise.Dependent
         open import Data.Product.Relation.Pointwise.NonDependent
         open import Data.Rational.Base
         open import Data.Rational.Literals
         open import Data.Rational.Properties
         open import Data.Sign.Base
         open import Data.Sign.Properties
         open import Data.Star.BoundedVec
         open import Data.Star.Decoration
         open import Data.Star.Environment
         open import Data.Star.Fin
         open import Data.Star.List
         open import Data.Star.Nat
         open import Data.Star.Pointer
         open import Data.Star.Properties
         open import Data.Star.Vec
         open import Data.String.Base
         open import Data.String.Literals
         open import Data.String.Properties
         open import Data.String.Unsafe
         open import Data.Sum.Base
         open import Data.Sum.Properties
         open import Data.Sum.Categorical.Examples
         open import Data.Sum.Categorical.Left
         open import Data.Sum.Categorical.Right
         open import Data.Sum.Function.Propositional
         open import Data.Sum.Function.Setoid
         open import Data.Sum.Relation.LeftOrder
         open import Data.Sum.Relation.Pointwise
         open import Data.Sum.Relation.Binary.LeftOrder
         open import Data.Sum.Relation.Binary.Pointwise
         open import Data.Table.Base
         open import Data.Table.Properties
         open import Data.Table.Relation.Equality
         open import Data.Table.Relation.Binary.Equality
         open import Data.These.Base
         open import Data.These.Properties
         open import Data.These.Categorical.Left
         open import Data.These.Categorical.Right
         open import Data.These.Categorical.Left.Base
         open import Data.These.Categorical.Right.Base
         open import Data.Trie.NonEmpty
         open import Data.Unit.Base
         open import Data.Unit.NonEta
         open import Data.Unit.Properties
         open import Data.Universe.Indexed
         open import Data.Vec.All
         open import Data.Vec.Any
         open import Data.Vec.Base
         open import Data.Vec.Bounded
         open import Data.Vec.Categorical
         open import Data.Vec.N-ary
         open import Data.Vec.Properties
         open import Data.Vec.Recursive
         open import Data.Vec.All.Properties
         open import Data.Vec.Bounded.Base
         open import Data.Vec.Membership.DecPropositional
         open import Data.Vec.Membership.DecSetoid
         open import Data.Vec.Membership.Propositional
         open import Data.Vec.Membership.Setoid
         open import Data.Vec.Membership.Propositional.Properties
         open import Data.Vec.Properties.WithK
         open import Data.Vec.Recursive.Categorical
         open import Data.Vec.Recursive.Properties
         open import Data.Vec.Relation.Binary.Equality.DecPropositional
         open import Data.Vec.Relation.Binary.Equality.DecSetoid
         open import Data.Vec.Relation.Binary.Equality.Propositional
         open import Data.Vec.Relation.Binary.Equality.Setoid
         open import Data.Vec.Relation.Binary.Equality.Propositional.WithK
         open import Data.Vec.Relation.Binary.Pointwise.Extensional
         open import Data.Vec.Relation.Binary.Pointwise.Inductive
         open import Data.Vec.Relation.Equality.DecPropositional
         open import Data.Vec.Relation.Equality.DecSetoid
         open import Data.Vec.Relation.Equality.Propositional
         open import Data.Vec.Relation.Equality.Setoid
         open import Data.Vec.Relation.Pointwise.Extensional
         open import Data.Vec.Relation.Pointwise.Inductive
         open import Data.Vec.Relation.Unary.All
         open import Data.Vec.Relation.Unary.Any
         open import Data.Vec.Relation.Unary.All.Properties
         open import Data.Vec.Relation.Unary.Any.Properties
         open import Data.W.Indexed
         open import Data.W.WithK
         open import Data.Word.Unsafe
         open import Debug.Trace
         open import Foreign.Haskell
         open import Function.Bijection
         open import Function.Equality
         open import Function.Equivalence
         open import Function.HalfAdjointEquivalence
         open import Function.Injection
         open import Function.Inverse
         open import Function.LeftInverse
         open import Function.Reasoning
         open import Function.Related
         open import Function.Surjection
         open import Function.Endomorphism.Propositional
         open import Function.Endomorphism.Setoid
         open import Function.Identity.Categorical
         open import Function.Nary.NonDependent
         open import Function.Nary.NonDependent.Base
         open import Function.Related.TypeIsomorphisms
         open import Function.Related.TypeIsomorphisms.Solver
         open import IO.Primitive
         open import Induction.Lexicographic
         open import Induction.Nat
         open import Induction.WellFounded
         open import Level.Literals
         open import Relation.Binary
         open import Relation.Nary
         open import Relation.Nullary
         open import Relation.Unary
         open import Relation.Binary.Consequences
         open import Relation.Binary.Core
         open import Relation.Binary.EqReasoning
         open import Relation.Binary.EquivalenceClosure
         open import Relation.Binary.HeterogeneousEquality
         open import Relation.Binary.Lattice
         open import Relation.Binary.OrderMorphism
         open import Relation.Binary.PartialOrderReasoning
         open import Relation.Binary.PreorderReasoning
         open import Relation.Binary.PropositionalEquality
         open import Relation.Binary.Reflection
         open import Relation.Binary.Rewriting
         open import Relation.Binary.SetoidReasoning
         open import Relation.Binary.StrictPartialOrderReasoning
         open import Relation.Binary.SymmetricClosure
         open import Relation.Binary.Construct.Always
         open import Relation.Binary.Construct.Constant
         open import Relation.Binary.Construct.Converse
         open import Relation.Binary.Construct.Flip
         open import Relation.Binary.Construct.FromPred
         open import Relation.Binary.Construct.FromRel
         open import Relation.Binary.Construct.Intersection
         open import Relation.Binary.Construct.Never
         open import Relation.Binary.Construct.NonStrictToStrict
         open import Relation.Binary.Construct.On
         open import Relation.Binary.Construct.StrictToNonStrict
         open import Relation.Binary.Construct.Union
         open import Relation.Binary.Construct.Add.Extrema.Equality
         open import Relation.Binary.Construct.Add.Extrema.NonStrict
         open import Relation.Binary.Construct.Add.Extrema.Strict
         open import Relation.Binary.Construct.Add.Infimum.Equality
         open import Relation.Binary.Construct.Add.Infimum.NonStrict
         open import Relation.Binary.Construct.Add.Infimum.Strict
         open import Relation.Binary.Construct.Add.Point.Equality
         open import Relation.Binary.Construct.Add.Supremum.Equality
         open import Relation.Binary.Construct.Add.Supremum.NonStrict
         open import Relation.Binary.Construct.Add.Supremum.Strict
         open import Relation.Binary.Construct.Closure.Equivalence
         open import Relation.Binary.Construct.Closure.Reflexive
         open import Relation.Binary.Construct.Closure.ReflexiveTransitive
         open import Relation.Binary.Construct.Closure.Symmetric
         open import Relation.Binary.Construct.Closure.Transitive
         open import Relation.Binary.Construct.Closure.Equivalence.Properties
         open import Relation.Binary.Construct.Closure.Reflexive.Properties
         open import Relation.Binary.Construct.Closure.Reflexive.Properties.WithK
         open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
         open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties.WithK
         open import Relation.Binary.Construct.Closure.Transitive.WithK
         open import Relation.Binary.Construct.NaturalOrder.Left
         open import Relation.Binary.Construct.NaturalOrder.Right
         open import Relation.Binary.HeterogeneousEquality.Core
         open import Relation.Binary.HeterogeneousEquality.Quotients
         open import Relation.Binary.HeterogeneousEquality.Quotients.Examples
         open import Relation.Binary.Indexed.Heterogeneous
         open import Relation.Binary.Indexed.Homogeneous
         open import Relation.Binary.Indexed.Heterogeneous.Core
         open import Relation.Binary.Indexed.Heterogeneous.Construct.At
         open import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
         open import Relation.Binary.Indexed.Homogeneous.Core
         open import Relation.Binary.Properties.BoundedJoinSemilattice
         open import Relation.Binary.Properties.BoundedLattice
         open import Relation.Binary.Properties.BoundedMeetSemilattice
         open import Relation.Binary.Properties.DecTotalOrder
         open import Relation.Binary.Properties.DistributiveLattice
         open import Relation.Binary.Properties.HeytingAlgebra
         open import Relation.Binary.Properties.JoinSemilattice
         open import Relation.Binary.Properties.Lattice
         open import Relation.Binary.Properties.MeetSemilattice
         open import Relation.Binary.Properties.Poset
         open import Relation.Binary.Properties.Preorder
         open import Relation.Binary.Properties.StrictPartialOrder
         open import Relation.Binary.Properties.StrictTotalOrder
         open import Relation.Binary.Properties.TotalOrder
         open import Relation.Binary.PropositionalEquality.Core
         open import Relation.Binary.PropositionalEquality.TrustMe
         open import Relation.Binary.PropositionalEquality.WithK
         open import Relation.Binary.Reasoning.MultiSetoid
         open import Relation.Binary.Reasoning.PartialOrder
         open import Relation.Binary.Reasoning.Preorder
         open import Relation.Binary.Reasoning.Setoid
         open import Relation.Binary.Reasoning.StrictPartialOrder
         open import Relation.Binary.Reasoning.Base.Double
         open import Relation.Binary.Reasoning.Base.Single
         open import Relation.Binary.Reasoning.Base.Triple
         open import Relation.Nullary.Decidable
         open import Relation.Nullary.Implication
         open import Relation.Nullary.Negation
         open import Relation.Nullary.Product
         open import Relation.Nullary.Sum
         open import Relation.Nullary.Universe
         open import Relation.Nullary.Construct.Add.Extrema
         open import Relation.Nullary.Construct.Add.Infimum
         open import Relation.Nullary.Construct.Add.Point
         open import Relation.Nullary.Construct.Add.Supremum
         open import Relation.Nullary.Decidable.Core
         open import Relation.Unary.Consequences
         open import Relation.Unary.Indexed
         open import Relation.Unary.PredicateTransformer
         open import Relation.Unary.Properties
         open import Relation.Unary.Closure.Base
         open import Relation.Unary.Closure.Preorder
         open import Relation.Unary.Closure.StrictPartialOrder
         open import Text.Format
         open import Text.Printf
  
 - File `importall2.agda`

       module importall2 where
         open import Data.AVL.Value
         open import Data.Container.Morphism
         open import Foreign.Haskell.Maybe
         open import Foreign.Haskell.Pair


<!-- Links -->

[epub]: https://plfa.github.io/out/epub/plfa.epub
[plfa]: http://plfa.inf.ed.ac.uk
[plfa-dev]: https://github.com/plfa/plfa.github.io/archive/dev.zip
[plfa-status]: https://travis-ci.org/plfa/plfa.github.io.svg?branch=dev
[plfa-travis]: https://travis-ci.org/plfa/plfa.github.io
[plfa-calver]: https://img.shields.io/badge/calver-20.07-22bfda
[plfa-latest]: https://github.com/plfa/plfa.github.io/releases/latest
[plfa-master]: https://github.com/plfa/plfa.github.io/archive/master.zip

[agda]: https://github.com/agda/agda/releases/tag/v2.6.1
[agda-version]: https://img.shields.io/badge/agda-v2.6.1-blue.svg
[agda-docs-emacs-mode]: https://agda.readthedocs.io/en/v2.6.1/tools/emacs-mode.html
[agda-docs-emacs-notation]: https://agda.readthedocs.io/en/v2.6.1/tools/emacs-mode.html#notation-for-key-combinations
[agda-docs-package-system]: https://agda.readthedocs.io/en/v2.6.1/tools/package-system.html#example-using-the-standard-library

[agda-stdlib-version]: https://img.shields.io/badge/agda--stdlib-v1.3-blue.svg
[agda-stdlib]: https://github.com/agda/agda-stdlib/releases/tag/v1.3

[haskell-stack]:  https://docs.haskellstack.org/en/stable/README/
[haskell-ghc]: https://www.haskell.org/ghc/
[haskell-windows]: https://www.haskell.org/platform/windows.html

[fix-whitespace]: https://github.com/agda/fix-whitespace

[gnuemacsDownload]: https://www.gnu.org/software/emacs/download.html
[mononoki]: https://madmalik.github.io/mononoki/
[debianMononoki]: https://packages.debian.org/sid/fonts/fonts-mononoki
[virtualbox]: https://www.virtualbox.org/
[applexcode]: https://developer.apple.com/xcode/
[gitscm]: https://git-scm.com/downloads
[stackAndWindows]: https://docs.haskellstack.org/en/v1.0.2/faq/#how-to-get-a-working-executable-on-windows
[aquamacs]: http://aquamacs.org/
[emacstour]: https://www.gnu.org/software/emacs/tour/

[ruby]: https://www.ruby-lang.org/en/documentation/installation/
[ruby-bundler]: https://bundler.io/#getting-started
[ruby-jekyll]: https://jekyllrb.com/
[ruby-html-proofer]: https://github.com/gjtorikian/html-proofer

[kramdown]: https://kramdown.gettalong.org/syntax.html
[pandoc]: https://pandoc.org/installing.html
[epubcheck]: https://github.com/w3c/epubcheck
