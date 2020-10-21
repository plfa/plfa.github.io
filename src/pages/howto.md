---
title     : "Checklists for various tasks"
permalink : /HOWTO/
---

# Publishing an announcement

PLFA announcements are files with names of the form `YYYY-0M-0D-SLUG.md`, where `YYYY` is the long year, `0M` is the zero-padded month, `0D` is the zero-padded day, and `SLUG` is the URL slug for the post, usually an URL-safe version of the title.

There are several steps to writing an announcement for PLFA:

- [ ] Create a new file in `posts` with the name `YYYY-0M-0D-SLUG.md`.
- [ ] Add the metadata block, setting at least the `title` field.
- [ ] Write the announcement in the remainder of the file.

If the announcement is short, it will be displayed inline in on the announcements page. If the announcement is long, insert a `<!--more-->` tag after the first paragraph. Everything before this tag will be displayed on the announcements page, as a “teaser” followed by a link to the full text.


# Publishing a release

For a project such as PLFA, [Semantic Versioning][SemVer] doesn’t make a huge amount of sense. Instead, we’ve adopted [Calendar Versioning][CalVer], following, e.g., [Ubuntu][Ubuntu]. PLFA versions are of the form `YY.0M`, where `YY` is the short year, and `0M` is the zero-padded month. For each release, there are two tags in the repository:

- `dev-YY.0M`: a copy of the contents of the `dev` branch at the time of release; and
- `web-YY.0M`: a copy of the web version of PLFA only.

The former contains everything you’d need to work with that version of PLFA, whereas the latter consists only of the relevant files to deploy a web version of PLFA.

There are several steps to creating a new release for PLFA:

- [ ] Update the version in `plfa.cabal` to `YY.M` (no zero padding).
- [ ] Create a new tag `dev-YY.0M` of the `dev` branch.
- [ ] Create a new tag `web-YY.0M` of the `master` branch.
- [ ] Push the new tags.
- [ ] Draft a new release [on GitHub][releases] linked to the `dev-YY.0M` tag.
- [ ] Add the release version `YY.0M` to the end of the `RELEASE_VERSIONS` variable in the Makefile.
- [ ] Write an announcement for the release in the `_posts` folder, describing any major changes.
- [ ] Run `make build build-history test` and deal with any problems.
- [ ] Commit and push.

[releases]: https://github.com/plfa/plfa.github.io/releases
[SemVer]: https://semver.org/
[CalVer]: https://calver.org
[Ubuntu]: https://www.ubuntu.com
