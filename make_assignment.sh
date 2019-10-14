#!/bin/bash

# This script can be used to automatically generate assignment files from PLFA source files.
# It takes a course abbreviation, e.g. TSPL, a year, and the number of the assignment.
# At the moment, it outputs the University of Edinburgh guidelines for good scholarly practice,
# making it somewhat specific to courses run there, but the header should be easy to edit.
#
# Usage:
#
#   ./make_assignment.sh [COURSE_NAME] [COURSE_YEAR] [ASSIGNMENT_NUMBER] [PLFA_SOURCE_FILE...]

COURSE="$1"
shift

YEAR="$1"
shift

NUM="$1"
shift

## Make assignment header

cat <<-EOF
---
title     : "Assignment$NUM: $COURSE Assignment $NUM"
layout    : page
permalink : /$COURSE/$YEAR/Assignment$NUM/
---

\`\`\`
module Assignment$NUM where
\`\`\`

## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using the "submit" command.
Please ensure your files execute correctly under Agda!


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

Furthermore, you are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself, or your group in the case of group practicals).

EOF

## Make import statements

cat <<-EOF

## Imports

\`\`\`
EOF
for SRC in "$@"; do
    AGDA_MODULE=$(eval "echo \"$SRC\" | sed -e \"s|src/||g; s|\\\.lagda\\\.md||g; s|/|\\\.|g;\"")
    echo "open import $AGDA_MODULE"
done
cat <<-EOF
\`\`\`

EOF

## Extract exercises

for SRC in "$@"; do
    NAME=$(basename "${SRC%.lagda.md}")
    cat <<-EOF

## $NAME

EOF
    awk '/^#/{flag=0} /^#### Exercise/{flag=1} flag' "$SRC"
done
