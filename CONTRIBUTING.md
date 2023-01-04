---
title: "Contributing"
permalink: /Contributing/
---

## Getting Started for Contributors

If you plan to contribute to the book, and wish to build the book locally, you will need to install some additional dependencies.
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
make test-htmlproofer  # Tests the generated HTML using HTMLProofer
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

## How to make changes to PLFA

The `dev` branch of the repository is write-protected, meaning that changes can only be made via pull requests, once all tests have passed. To make changes, create a new branch by running the following command from your local copy of the repository:

```sh
git checkout -b [new_branch_name] [old_branch_name]
```

We suggest basing your branches on `dev`, and naming branches after issues, e.g., `issue-650` or using a description of the new features they implement, e,g., `feature-subtyping`.

Publish the branch by running the following command from your local copy of the repository:

```sh
git push origin [new_branch_name]
```

Then open a pull request on GitHub, from the [Pull Requests][github-pulls] tab.

## How to publish the current version of PLFA

Any changes to the development branch `dev` are automatically published to the live version of the book, provided that they pass certain tests. If you've made changes though the book, and they are not propagated to the live version, please check the build status on [GitHub Actions][github-actions].

The copy of PLFA hosted at <https://plfa.inf.ed.ac.uk> updates daily.

## How to publish an announcement

PLFA announcements are files with names of the form `0Y0Y-0M-0D-SLUG.md`, where `0Y0Y` is the long year, `0M` is the zero-padded month, `0D` is the zero-padded day, and `SLUG` is the URL slug for the post, usually an URL-safe version of the title.

There are several steps to writing an announcement for PLFA:

- Create a new file in `web/posts` with the name `0Y0Y-0M-0D-SLUG.md`.
- Add the metadata block, setting at least the `title` field.
- Write the announcement in the remainder of the file.

If the announcement is short, it will be displayed in full in on the announcements page. If the announcement is long, insert a `<!--more-->` tag after the first paragraph. Everything before this tag will be displayed on the announcements page, followed by a link to the full announcement.

## How to publish a new release

For a project such as PLFA, [Semantic Versioning][semver] doesn’t make a huge amount of sense. Instead, we’ve adopted [Calendar Versioning][calver], following, e.g., [Ubuntu][ubuntu]. PLFA versions are of the form `0Y.0M`, where `0Y` is the short year, and `0M` is the zero-padded month.

To create a new release for PLFA, follow these steps:

- Write [an announcement](#how-to-publish-an-announcement) for the release, which describes any major changes. Use the previous release notes announcements as a template.
- Add an entry for the new version to [`Citing.md`][citing].
- Run `bumpver update`, or:
  + Update the version in `plfa.cabal` to `YY.MM`. Don't use zero padding, as Cabal does not allow leading zeros.
  + Update the version in the badge in the README file, which is in the footnotes as `[plfa-badge-version-svg]`.
  + Commit and push your changes.
  + Run `make test` and handle any warnings or errors.
  + Create a new tag named `v0Y.0M` and push it to GitHub.
- Wait for the CI to finish, and a new version to be published to [GitHub Releases][github-releases].
- Update `publish.yml` to download and publish the new version, by adding the following snippet:
  ```yaml
  - uses: ./.github/actions/download-release
    with:
      plfa-version: v0Y.0M
      path: site
  ```
- Commit and push your changes.
- Wait for the CI to finish, and for the website to be updated.
- Check if the new version is available at <https://plfa.github.io/0Y.0M/>.

## How to add a citation

You can cite works by writing `@` followed by a citation key, e.g., `@plfa20.07`. For instance, the first release of PLFA was by @plfa19.08. See the [Bibliography](#bibliography) section below for the bibliography. Citations and the bibliography are currently styled using Pandoc's default citation style. Other styles can easily be found using the [Zotero Style Repository][zotero] and added into the build file by setting the `citation-style` meta-variable. The citation keys are cross-referenced with `data/bibliography.bib`.

## The structure of the PLFA repository

```sh
plfa
│
├── src                        # Source files for PLFA chapters:
│   └── plfa                   #
│       ├── backmatter         # All files in these folders must be either
│       ├── frontmatter        # plain Markdown or well-typed literate Agda
│       ├── part1              # with Markdown, and must contain a YAML header
│       ├── part2              # defining at least a title and a permalink.
│       └── part3              #
│
├── tools                      # Tools used for building PLFA:
│   └── Buildfile.hs           #   - code for building PLFA.
│   └── UpdateContributors.hs  #   - code for updating data/contributors.
│
├── data                       # Data used when building PLFA:
│   ├── authors                #   - information about the authors
│   ├── contributors           #   - information about the contributors
│   └── bibliography.bib       #   - bibliographic information
│   └── metadata.yml           #   - web metadata, e.g., language & description
│   └── tableOfContents.yml    #   - table of contents
│
├── web                        # Files only used for website:
│   ├── assets                 #   - static assets
│   ├── posts                  #   - announcements
│   ├── sass                   #   - stylesheets
│   └── templates              #   - HTML templates
│
├── book
│   ├── epub                   # Files only used for EPUB version.
│   └── pdf                    # Files only used for PDF version.
│
├── courses                    # Pages for courses using PLFA by the authors:
│   └── TSPL/2019              #   - TSPL, University of Edinburgh, 2019
│
├── papers                     # Source files for papers written about PLFA.
│
└── extra                      # Incomplete, unincorporated formalisations.
```

## Bibliography

[semver]: https://semver.org/
[calver]: https://calver.org
[ubuntu]: https://www.ubuntu.com
[zotero]: https://www.zotero.org/styles
[github-actions]: https://github.com/plfa/plfa.github.io/actions
[github-releases]: https://github.com/plfa/plfa.github.io/releases
[nodejs]: https://nodejs.dev/en/
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
[github-branches]: https://github.com/plfa/plfa.github.io/branches
[github-pulls]: https://github.com/plfa/plfa.github.io/pulls
[citing]: https://github.com/plfa/plfa.github.io/blob/dev/web/Citing.md
