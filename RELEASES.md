# How to create a new release

For a project such as PLFA, [Semantic Versioning][SemVer] doesn’t make a huge amount of sense. Instead, we’ve adopted [Calendar Versioning][CalVer], following, e.g., [Ubuntu][Ubuntu]. PLFA versions are of the form `YY.0M`, where `YY` is the short year, and `0M` is the zero-padded month. For each release, there are two tags in the repository:

- `dev-YY.0M`: a copy of the contents of the `dev` branch at the time of release; and
- `web-YY.0M`: a copy of the web version of PLFA only.

The former contains everything you’d need to work with that version of PLFA, whereas the latter consists only of the relevant files to deploy a web version of PLFA.

There are several steps to creating a new release for PLFA:

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
