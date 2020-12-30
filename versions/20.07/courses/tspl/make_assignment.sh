#!/usr/bin/env bash

# TODO:
#   - put the exercises from each chapter in their own module
#   - replicate the imports from that module
#   - import that module hiding anything defined in an exercise section

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

## Awk Scripts

AWK_GET_IMPORTS='
    /^#/ {
        import=0
    }
    /^## Imports/ {
        import=1
    }
    /^```/ {
        code=!code;
        {
            if (import)
                print $0
        };
        next
    }
    {
        if (import) {
            if (code)
                print "  "$0
            else
                print $0
        }
    }
'

AWK_GET_DEFNS='
    /^#/ {
        exercise=0
    }
    /^#### Exercise/ {
        exercise=1
    }
    /^```/ {
        code=!code;
        next
    }
    !/^  / {
        postulate=0
    }
    /^postulate/ {
        postulate=1
    }
    /^  [^ :(){}]+ +:/ {
        if (exercise && code && postulate)
            print $0
    }
    /^[^ :(){}]+ +:/ {
        if (exercise && code)
            print $0
    }
'

AWK_GET_EXERCISES='
    /^#/ {
        exercise=0
    }
    /^#### Exercise/ {
        exercise=1
    }
    /^```/ {
        code=!code;
        {
            if (exercise)
                print $0
        };
        next
    }
    {
        if (exercise) {
            if (code)
                print "  "$0
            else
                print $0
        }
    }
'

## Exercises

for SRC in "$@"; do

    # Generate Section & Module Header
    NAME=$(basename "${SRC%.lagda.md}")
    echo
    echo "## $NAME"
    echo
    echo '```'
    echo "module $NAME where"
    echo '```'
    echo

    # Extract Imports
    awk "$AWK_GET_IMPORTS" "$SRC"

    # Generate Import and Hiding List
    echo '```'
    AGDA_MODULE=$(eval "echo \"$SRC\" | sed -e \"s|src/||g; s|\\\.lagda\\\.md||g; s|/|\\\.|g;\"")
    echo "  open import $AGDA_MODULE"
    HIDING_LIST=""
    OLDIFS=$IFS
    IFS=$(echo -en "\n\b")
    for defn in `awk "$AWK_GET_DEFNS" "$SRC"`;
    do
        NEW=$(eval "echo \"$defn\" | cut -d: -f1 | xargs")
        if [ -z "$HIDING_LIST" ]; then
            HIDING_LIST="$NEW"
        else
            HIDING_LIST="$HIDING_LIST; $NEW"
        fi
    done
    IFS=$OLDIFS
    echo "    hiding ($HIDING_LIST)"
    echo '```'
    echo

    # Extract Exercises
    awk "$AWK_GET_EXERCISES" "$SRC"
done
