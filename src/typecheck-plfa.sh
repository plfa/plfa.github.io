#!/bin/sh

# Script to build the PFLA sources with agda.
# Andreas Abel, 2022-05-30

# Run this script from the project root.
# It expects the name of the agda binary as first argument (defaults to agda-2.6.1.3).
AGDA_BIN=${1:-agda-2.6.1.3}

# Generate libraries file
echo "standard-library/standard-library.agda-lib" > libraries

AGDA="${AGDA_BIN} --library-file=libraries"

# Check all files that define BUILTINs
for f in $(grep -r --include=\*.lagda.md -e BUILTIN -l src); do
  echo ${AGDA} $f;
  ${AGDA} $f;
done

# Collect all files that do not define BUILTINs
EVERYTHING=src/Everything.agda
cat > ${EVERYTHING} <<EOF
-- List of all agda files that do not define a BUILTIN.
-- Automatically generated, DO NOT EDIT!

module Everything where

EOF
grep -r --include=\*.lagda.md -e BUILTIN -L src | sed -e 's/src\//import /g' | sed -e 's/\.lagda\.md//g' | sed -e 's/\//\./g' >> ${EVERYTHING}

# Check those in one go
echo ${AGDA} ${EVERYTHING}
${AGDA} ${EVERYTHING}

# Done!
