---
title: "Building with Hakyll"
---

We’re pleased to announce that as of today, PLFA builds entirely using Haskell!
We’ve migrated our build system from a bundle of Makefiles, shell scripts, and Jekyll, over to [Hakyll][hakyll], a static site building written in Haskell.
All you need to do to build and serve PLFA locally is:
```bash
git clone --recurse-submodules https://github.com/plfa/plfa.github.io PLFA
cd PLFA/
stack build && stack exec site watch
```
That will pull in all the dependencies: Agda, the standard library, Hakyll, Pandoc, *etc.*

There’s been lots of changes to the organisation of PLFA as a consequence, but the most important change, if you’re using PLFA as a student, is that we now include the correct version of the Agda standard library as a Git submodule. The [“Getting Started”](/GettingStarted/#install-plfa-and-the-agda-standard-library) page can help you set it up correctly!

If you’re a contributor to PLFA, there are some further changes that will affect you!

<!--more-->

- The main build file is [“hs/Main.hs”][plfa-main].
- PLFA is written using Pandoc Markdown:
  + For links, write `/DeBruijn/` instead of `{{ site.baseurl }}/DeBruijn/`.
  + For explicit header anchors, write `{name=my-anchor}` instead of `{#my-anchor}`.
- Many of the files involved in rendering the website were moved:
  + The index page was moved to [“src/plfa/index.md”][plfa-index].<br />
    The sections on the index pages are generated from [“src/plfa/toc.metadata”][plfa-toc].
  + The HTML templates were moved to the [“templates/”][plfa-templates] directory.
  + The static files were moved to the [“public/”][plfa-public] directory.
  + The pages were moved to the [“src/pages/”][plfa-pages] directory.<br />
    Pages that are a part of the book, as part of the front matter and back matter, e.g., [Preface](/Preface/), were moved to [“src/plfa/frontmatter/”][plfa-frontmatter] and [“src/plfa/backmatter/”][plfa-backmatter], respectively.
  + We’ve moved to the latest version of the [Minima][jekyll-minima] theme, adapted for use with Hakyll, which is now explicitly stored in the repository.
- The historical versions which were built using Jekyll—19.08 and 20.07—are stored in the [“versions/”][plfa-versions] directory. For future versions, we plan to pull these in for publication.
- Support for Travis CI was dropped. We’ve been having trouble building and caching Agda on Travis for a while now, so until Agda starts publishing pre-built binaries, we’re moving away from Travis. In the meantime, we will publish PLFA directly to the [“web”][plfa-web] branch.
- The [acknowledgements](/Acknowledgements/) are built from the [contributors][plfa-contributors] directory. We regularly update these files using the GitHub API, using [“hs/UpdateContributors.hs”][plfa-update-contributors], but if your contribution wasn’t via a GitHub commit or it doesn’t show up for some reason, you can add yourself here!


[hakyll]: https://jaspervdj.be/hakyll/
[pandoc-markdown]: https://pandoc.org/MANUAL.html#pandocs-markdown
[plfa-index]: https://github.com/plfa/plfa.github.io/tree/dev/src/plfa/index.md
[plfa-toc]: https://github.com/plfa/plfa.github.io/tree/dev/src/plfa/toc.metadata
[plfa-templates]: https://github.com/plfa/plfa.github.io/tree/dev/templates
[plfa-public]: https://github.com/plfa/plfa.github.io/tree/dev/public
[plfa-pages]: https://github.com/plfa/plfa.github.io/tree/dev/src/pages
[plfa-frontmatter]: https://github.com/plfa/plfa.github.io/tree/dev/src/plfa/frontmatter
[plfa-backmatter]: https://github.com/plfa/plfa.github.io/tree/dev/src/plfa/backmatter
[plfa-versions]: https://github.com/plfa/plfa.github.io/tree/dev/versions
[plfa-web]: https://github.com/plfa/plfa.github.io/tree/web/
[plfa-contributors]: https://github.com/plfa/plfa.github.io/tree/dev/contributors
[plfa-main]: https://github.com/plfa/plfa.github.io/blob/dev/hs/Main.hs
[plfa-update-contributors]: https://github.com/plfa/plfa.github.io/blob/dev/hs/UpdateContributors.hs
[jekyll-minima]: https://github.com/jekyll/minima
