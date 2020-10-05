# Roadmap

Here’s what still needs to happen in order to use Hakyll for PLFA builds.
We can release after the first milestone.
The goals in the second milestone are optional, but nice.


## Milestone 1

- migrate EPUB generation over to site.hs


## Milestone 2

- automatically generate Unicode sections
  + use a context field similar to the teaser context
  + create a template for book chapters which uses said field
  + use book chapter template for .lagda.md files

- automatically generate Statistics chapter
  + see https://github.com/plfa/plfa.github.io/blob/41939ad0312b6012ac76f056c6da1f9ff590c040/hs/agda-count.hs

- …
