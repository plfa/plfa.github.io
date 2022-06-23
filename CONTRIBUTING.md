---
title: "Contributing"
permalink: /Contributing/
---

## Getting Started for Contributors

If you plan to contribute to the book, and wish to build the book locally, you will need to install some additional dependencies:
Please start by following the instructions for readers in [Getting Started](/GettingStarted/#getting-started-for-readers).
This should leave you with a working installation of basic development tools, Haskell, Agda, the standard library, and PLFA.

### Building, Viewing, and Basic Testing

Building the book requires the latest version of [Node.js][nodejs], which is used at various stages to compile and test HTML, CSS, and JavaScript.

Once you have installed [Node.js][nodejs], you can build the book, and run basic tests, using the following commands:

```sh
make                    # Alias for "make build"
make build              # Builds PLFA
make clean              # Cleans out the build cache
make clobber            # Cleans out the build cache and clobbers the build
make serve              # Starts server and opens the book in a browser
make test               # Alias for "make test-html-validate"
make test-html-validate # Tests the generated HTML using HTML-validate
```

The continuous integration tests the generated output with two additional testing commands, each of which come with their own dependencies.

### Testing Links with HTMLProofer

To test whether or not any of the internal links in the book are broken, we use [HTMLProofer][htmlproofer].
This requires [a relatively recent Ruby version][ruby] (see the `.ruby-version` file for details) as well as [bundler][bundler].
We recommend installing Ruby via [rbenv][rbenv].

Once you have installed [Ruby][ruby] and [bundler][bundler], you can test for broken links using the following command:

```sh
make test-html-proofer  # Tests the generated HTML using HTMLProofer
```

You can optionally pass `EXTERNAL_LINKS=true` to test external links as well.

### Testing EPUB with EPUBCheck

To test whether or not there are any faults in the generated EPUB, we use [EPUBCheck][epubcheck].
This requires [EPUBCheck][epubcheck], and possibly [Java][java].
We recommend installing [EPUBCheck][epubcheck] via [the installation instructions given by W3C][epubcheck].

Once you have installed [EPUBCheck][epubcheck], you can test the generated EPUB using the following command:

```sh
make test-epubcheck     # Tests the generated EPUB using EPUBCheck
```

### Checking for whitespace violations using fix-whitespace

To keep the code clean of trailing whitespace and missing terminal newlines we use [fix-whitespace][fix-whitespace].

You can install [fix-whitespace][fix-whitespace] by running the following command:

```sh
cabal v2-install fix-whitespace
```

Once you have installed [fix-whitespace][fix-whitespace], you can set up a git hook which automatically checks the whitespace on commit (see `.githooks/pre-commit`) by running the following command:

```sh
git config core.hooksPath .githooks
```

## How to publish the current version of PLFA

Any changes to the development branch `dev` are automatically published to the live version of the book, provided that they pass certain tests. If you've made changes though the book, and they are not propagated to the live version, please check the build status on [GitHub Actions][github-actions].

The copy of PLFA hosted at <https://plfa.inf.ed.ac.uk> updates daily.

## How to publish an announcement

PLFA announcements are files with names of the form `YYYY-0M-0D-SLUG.md`, where `YYYY` is the long year, `0M` is the zero-padded month, `0D` is the zero-padded day, and `SLUG` is the URL slug for the post, usually an URL-safe version of the title.

There are several steps to writing an announcement for PLFA:

- Create a new file in `web/posts` with the name `YYYY-0M-0D-SLUG.md`.
- Add the metadata block, setting at least the `title` field.
- Write the announcement in the remainder of the file.

If the announcement is short, it will be displayed in full in on the announcements page. If the announcement is long, insert a `<!--more-->` tag after the first paragraph. Everything before this tag will be displayed on the announcements page, followed by a link to the full announcement.

## How to publish a new release

For a project such as PLFA, [Semantic Versioning][semver] doesn’t make a huge amount of sense. Instead, we’ve adopted [Calendar Versioning][calver], following, e.g., [Ubuntu][ubuntu]. PLFA versions are of the form `YY.0M`, where `YY` is the short year, and `0M` is the zero-padded month.

To create a new release for PLFA, follow these steps:

- Write [an announcement](#how-to-publish-an-announcement) for the release,
  which describes any major changes.
- Update the version in `plfa.cabal` to `YY.M`.
  Don't use zero padding for the month, as Cabal does not allow leading zeros.
- Run `make test` and handle any warnings or errors.
- Push your changes to the `dev` branch.
- Wait for your changes to be propagated to the live version.
- Create a new tag named `vYY.0M`.

Then, to make sure that the release is published to live versions of PLFA, update the `deploy` job in the GitHub workflow to download and include the web build for the new version.

## How to add a citation

You can cite works by writing `@` followed by a citation key, e.g., `@plfa20.07`. For instance, the first release of PLFA was by @plfa19.08. See the [Bibliography](#bibliography) section below for the bibliography. Citations and the bibliography are currently styled using Pandoc's default citation style. Other styles can easily be found using the [Zotero Style Repository][zotero] and added into the build file by setting the `citation-style` meta-variable. The citation keys are cross-referenced with `data/bibliography.bib`.

## The structure of the PLFA repository

```
plfa
├── book
│   ├── epub
│   └── pdf
├── courses
│   └── TSPL/2019
├── data
│   ├── authors
│   ├── contributors
│   ├── dotagda
│   └── bibliography.bib
│   └── metadata.yml
│   └── tableOfContents.yml
├── extra
├── papers
├── src
│   └── plfa
│       ├── backmatter
│       ├── frontmatter
│       ├── part1
│       ├── part2
│       └── part3
├── tools
│   └── Buildfile.hs
│   └── UpdateContributors.hs
└── web
    ├── assets
    ├── posts
    ├── sass
    └── templates
```

## References

[semver]: https://semver.org/
[calver]: https://calver.org
[ubuntu]: https://www.ubuntu.com
[zotero]: https://www.zotero.org/styles
[github-actions]: https://github.com/plfa/plfa.github.io/actions
[github-releases]: https://github.com/plfa/plfa.github.io/releases
[nodejs]: https://nodejs.dev/learn/how-to-install-nodejs
[htmlproofer]: https://github.com/gjtorikian/html-proofer
[ruby]: https://www.ruby-lang.org/en/downloads/
[bundler]: https://bundler.io/#getting-started
[rbenv]: https://github.com/rbenv/rbenv
[rvm]: http://rvm.io
[epubcheck]: https://www.w3.org/publishing/epubcheck/docs/installation/
[epubcheck-brew]: https://formulae.brew.sh/formula/epubcheck
[epubcheck-apt]: https://tracker.debian.org/pkg/epubcheck
[java]: https://www.java.com/en/download/
[fix-whitespace]: https://github.com/agda/fix-whitespace
