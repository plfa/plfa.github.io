---
title     : "Acknowledgements"
layout    : page
prev      : /Untyped/
permalink : /Acknowledgements/
next      : /Fonts/
---

Thank you to:
  * The inventors of Agda, for a new playground.
  * The authors of Software Foundations, for inspiration.


A special thank you, for inventing ideas on which
this book is based, and for hand-holding:
  * Conor McBride
  * James McKinna
  * Ulf Norell
  * Andreas Abel


For a note showing how much more compact it is to avoid raw terms:
  * David Darais


<span class="force-end-of-list"></span>
{%- if site.contributors or site.extra_contributors -%}
For pull requests big and small, and for answering questions on the Agda mailing list:
<ul class="list-of-contributors">
{%- for contributor in site.contributors -%}
  <li><a href="https://github.com/{{ contributor.github_username }}">{{ contributor.name }}</a></li>
{%- endfor -%}
{%- for contributor in site.extra_contributors -%}
  {%- if contributor.name and contributor.github_username -%}
  <li><a href="https://github.com/{{ contributor.github_username }}">{{ contributor.name }}</a></li>
  {%- else -%}
  {%- if contributor.name -%}
  <li>{{ contributor.name }}</li>
  {%- endif -%}
  {%- if contributor.github_username -%}
  <li><a href="https://github.com/{{ contributor.github_username }}">{{ contributor.github_username }}</a></li>
  {%- endif -%}
  {%- endif -%}
{%- endfor -%}
<li>[Your name goes here]</li>
</ul>
{%- else -%}
{%- endif -%}


For support:
  * EPSRC Programme Grant EP/K034413/1
  * NSF Grant No. 1814460 
  * Foundation Sciences Mathematiques de Paris (FSMP)
    Distinguised Professor Fellowship
