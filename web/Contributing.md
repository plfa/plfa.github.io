---
title     : "Instructions for various tasks"
permalink : /Contributing/
---


## How to publish the current version of PLFA

Any changes to the development branch `dev` are automatically published to the live version of the book, provided that they pass certain tests. If you've made changes though the book, and they are not propagated to the live version, please check the build status on (GitHub Actions)[GitHub-Actions].

The copy of PLFA hosted at <https://plfa.inf.ed.ac.uk> updates daily.


## How to publish an announcement

PLFA announcements are files with names of the form `YYYY-0M-0D-SLUG.md`, where `YYYY` is the long year, `0M` is the zero-padded month, `0D` is the zero-padded day, and `SLUG` is the URL slug for the post, usually an URL-safe version of the title.

There are several steps to writing an announcement for PLFA:

- [ ] Create a new file in `web/posts` with the name `YYYY-0M-0D-SLUG.md`.
- [ ] Add the metadata block, setting at least the `title` field.
- [ ] Write the announcement in the remainder of the file.

If the announcement is short, it will be displayed in full in on the announcements page. If the announcement is long, insert a `<!--more-->` tag after the first paragraph. Everything before this tag will be displayed on the announcements page, followed by a link to the full announcement.


## How to publish a new release

For a project such as PLFA, [Semantic Versioning][SemVer] doesn’t make a huge amount of sense. Instead, we’ve adopted [Calendar Versioning][CalVer], following, e.g., [Ubuntu][Ubuntu]. PLFA versions are of the form `YY.0M`, where `YY` is the short year, and `0M` is the zero-padded month. For each release, there are two tags in the repository:

- `dev-YY.0M`: a copy of the contents of the `dev` branch at the time of release; and
- `web-YY.0M`: a copy of the web version of PLFA only.

The former contains everything you’d need to work with that version of PLFA, whereas the latter consists only of the relevant files to deploy a web version of PLFA.

To create a new release for PLFA, follow these steps:

- [ ] Write [an announcement](#how-to-publish-an-announcement) for the release,
      which describes any major changes.
- [ ] Update the version in `plfa.cabal` to `YY.M`.
      Don't use zero padding for the month, as Cabal does not allow leading zeros.
- [ ] Run `make test` and handle any warnings or errors.
- [ ] Push your changes to the `dev` branch.
- [ ] Wait for your changes to be propagated to the live version.
- [ ] Draft [a new release]][GitHub-Releases] of the `dev` branch titled `dev-YY.0M`.
      Use a new tag with the same name.
- [ ] Draft [a new release]][GitHub-Releases] of the `web` branch titled `web-YY.0M`.
      Use a new tag with the same name.

Then, we need to make sure that the release is published to live versions of PLFA:

- [ ] Update the build task in the `Makefile` to download a copy of
      the web release you just created, and place it in `_site/YY.0M/`.
- [ ] Run `make test` and handle any warnings or errors.
- [ ] Push your changes to the `dev` branch.
- [ ] Wait for your changes to be propagated to the live version.

The first two releases, 19.08 and 20.07, are included in the `dev` branch of the repository under `data/legacy/`, because these versions do not use relative URLs, and as such cannot simply be moved into a subdirectory. Later releases should use relative URLs, and therefore can simply be downloaded from GitHub, and copied into their appropriate subdirectories.


## How to add a citation

You can cite works by writing `@` followed by a citation key, e.g., `@plfa20.07`. For instance, the first release of PLFA was by @plfa19.08. See the [Bibliography](#bibliography) section below for the bibliography. Citations and the bibliography are currently styled according to the ISO-690 standard. Other styles can easily be found using the [Zotero Style Repository][Zotero]. The citation keys are cross-referenced with the BibTeX file under `bib/plfa.bib`.


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

[SemVer]: https://semver.org/
[CalVer]: https://calver.org
[Ubuntu]: https://www.ubuntu.com
[Zotero]: https://www.zotero.org/styles
[GitHub-Actions]: https://github.com/plfa/plfa.github.io/actions
[GitHub-Releases]: https://github.com/plfa/plfa.github.io/releases
