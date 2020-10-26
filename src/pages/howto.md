---
title     : "Instructions for various tasks"
permalink : /HOWTO/
---

## Add a citation

You can cite works by writing `@` followed by a citation key, e.g., `@plfa20.07`. For instance, the first release of PLFA was by @plfa19.08. See the [Bibliography](#bibliography) section below for the bibliography. Citations and the bibliography are currently styled according to the ISO-690 standard. Other styles can easily be found using the [Zotero Style Repository][Zotero]. The citation keys are cross-referenced with the BibTeX file under `bib/plfa.bib`.


## Publish the current version of PLFA to the web

PLFA used to be published automatically from the `dev` branch by Travis CI. However, given recent trouble with Agda and Travis CS, we moved away from automatic updates.

There are several steps to publishing the current version of PLFA to the web:

- [ ] Check that your local copy of PLFA is up-to-date and on the `dev` branch by running `git status`.
- [ ] Run `make publish`.

The `publish` task builds the book, runs the tests, and then deploys it to GitHub. If any errors occur while running `make build` or `make test`, fix these errors. If an error occurs while switching to or operating on the `web` branch, switch back to the `dev` branch by running `git checkout dev` and delete your local copy of the `web` branch by running `git branch -D web`, then restart the process.


## Publish an announcement

PLFA announcements are files with names of the form `YYYY-0M-0D-SLUG.md`, where `YYYY` is the long year, `0M` is the zero-padded month, `0D` is the zero-padded day, and `SLUG` is the URL slug for the post, usually an URL-safe version of the title.

There are several steps to writing an announcement for PLFA:

- [ ] Create a new file in `posts` with the name `YYYY-0M-0D-SLUG.md`.
- [ ] Add the metadata block, setting at least the `title` field.
- [ ] Write the announcement in the remainder of the file.

If the announcement is short, it will be displayed inline in on the announcements page. If the announcement is long, insert a `<!--more-->` tag after the first paragraph. Everything before this tag will be displayed on the announcements page, as a “teaser” followed by a link to the full text.


## Publish a new release

For a project such as PLFA, [Semantic Versioning][SemVer] doesn’t make a huge amount of sense. Instead, we’ve adopted [Calendar Versioning][CalVer], following, e.g., [Ubuntu][Ubuntu]. PLFA versions are of the form `YY.0M`, where `YY` is the short year, and `0M` is the zero-padded month. For each release, there are two tags in the repository:

- `dev-YY.0M`: a copy of the contents of the `dev` branch at the time of release; and
- `web-YY.0M`: a copy of the web version of PLFA only.

The former contains everything you’d need to work with that version of PLFA, whereas the latter consists only of the relevant files to deploy a web version of PLFA.

There are several steps to creating a new release for PLFA:

- [ ] Update the version in `plfa.cabal` to `YY.M` (no zero padding).
- [ ] Commit your changes to the `dev` branch.
- [ ] [Publish the current version of PLFA](#publish-the-current-version-of-plfa-to-the-web).
- [ ] Create a new tag `dev-YY.0M` of the `dev` branch.
- [ ] Create a new tag `web-YY.0M` of the `web` branch.
- [ ] Push the new tags.
- [ ] Draft a new release [on GitHub][releases] linked to the `dev-YY.0M` tag.
- [ ] Add the release version `YY.0M` to the end of the `releaseVersions` variable in `hs/Main.hs`.[^nosupport]
- [ ] Write an announcement for the release in the `_posts` folder, describing any major changes.
- [ ] Commit your changes to the `dev` branch.
- [ ] [Publish the current version of PLFA](#publish-the-current-version-of-plfa-to-the-web) (again).

## Bibliography

[^nosupport]: At the time of writing, all prior releases have been demoted to legacy releases, and are included in the GitHub repository under the `versions/` folder. There is no support for importing future releases upon publication. Such support will be drafted on a by-need basis.

[releases]: https://github.com/plfa/plfa.github.io/releases

[SemVer]: https://semver.org/
[CalVer]: https://calver.org
[Ubuntu]: https://www.ubuntu.com
[Zotero]: https://www.zotero.org/styles
