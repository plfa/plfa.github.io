#!/bin/bash

# Script to extract exercises from PLFA chapters, e.g., `src/plfa/part1/Naturals.lagda.md`.
# Usage:
#
#   ./exercise.sh [SOURCE] [TARGET]

SRC="$1"
shift

DST="$1"
shift

awk '/^#/{flag=0} /^#### Exercise/{flag=1} flag' "$SRC" > "$DST"