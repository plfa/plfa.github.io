---
layout : post
title  : "Versions and Releases"
short  : false
---

We’re adding stable releases to PLFA, which you can find [on GitHub][releases]!

<!--more-->

For the past two years, we’ve tried to do major revisions of the book during winter break and early summer, to ensure that the text remains consistent throughout the teaching period… Inevitably, we fixed bugs, and make small changes here and there, perhaps resulting in a less-than-consistent experience.

Starting today, you can be sure that PLFA will remain consistent, since we’re adding stable releases! You can find the releases [on GitHub][releases], and as tags in the Git repository. The releases are numbered using [calendar versioning][CalVer] using the `YY.0M` format, e.g., `20.07` was released in July 2020. Each release will have two associated tags.

- [`dev-20.07`][dev-20.07] is a copy of the `dev` branch, and contains everything you need to work with PLFA;
- [`web-20.07`][web-20.07] is a copy of the web site *only*, and does not contain Agda sources.

The `web-YY.0M` releases are useful if you’d like to host a copy of PLFA, but you don’t have all the required dependencies installed. However, if you’d like to view a particular release only, we have you covered! If you’d like to browse PLFA version 20.07, just go to:

- <https://plfa.github.io/20.07/>

Currently, we have the [`20.07`][PLFA-20.07] release, made just before the recent changes, and the [`19.08`][PLFA-19.08] release, the stable release for the past academic year. We’re expecting to release `20.08` next month, to provide a stable release for the upcoming academic year, which will include support for the latest version of Agda.

[CalVer]: https://calver.org/
[releases]: https://github.com/plfa/plfa.github.io/releases
[dev-20.07]: https://github.com/plfa/plfa.github.io/releases/tag/dev-20.07
[web-20.07]: https://github.com/plfa/plfa.github.io/releases/tag/web-20.07
[PLFA-20.07]: https://plfa.github.io/20.07/
[PLFA-19.08]: https://plfa.github.io/19.08/
