# Roadmap

Here’s what still needs to happen in order to use Hakyll for PLFA builds.
We can release after the first milestone.
The goals in the second milestone are optional, but nice.


## Milestone 1

- render prev, next, and source links
  + requires populating the context with a link to the source file
  + prev and next are set in the metadata
  + see: https://github.com/plfa/plfa.github.io/blob/dev/_includes/next.html

- fix links to plfa:
  + should construct a regular expression which matches all PLFA modules,
    by assuming that PLFA is in the `src` folder
  + see https://github.com/wenkokke/agda2html/blob/master/src/Lib.hs#L213-L230

- fix Makefile to reuse html-proofer
  + that still leaves us with a Ruby dependency
  + only for testing

- migrate EPUB generation over to site.hs


## Milestone 2

- automatically generate Unicode sections
  + use a context field similar to the teaser context
  + create a template for book chapters which uses said field
  + use book chapter template for .lagda.md files

- automatically generate Statistics chapter
  + see https://github.com/plfa/plfa.github.io/blob/41939ad0312b6012ac76f056c6da1f9ff590c040/hs/agda-count.hs

- …
