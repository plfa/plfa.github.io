---
comment: This template is used to restore the standard PLFA metadata to Markdown files. It is used in raw writers.
---

---
title       : $title$
$if(authors)$
author      :
$for(authors)$
  - $name$
$endfor$
$endif$
description : $description$
rights      : $rights$
language    : $language$
layout      : $layout$
prev        : $prev$
permalink   : $permalink$
next        : $next$
---

$body$
