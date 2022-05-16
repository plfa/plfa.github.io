---
title     : "Announcements"
permalink : /Announcements/
---

:::::: {.post-list}
$for(post)$
## $post.title$
[$post.date$]{.post-meta}
$if(post.teaser)$
$post.teaser$
[(more)]($post.url$)
$else$
$post.body$
$endif$
$endfor$
::::::
