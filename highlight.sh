#!/bin/bash

AGDA_STDLIB_SED=".agda-stdlib.sed"

SRC="$1"
shift

OUT="$1"
OUT_DIR="$(dirname $OUT)"
shift

# Create temporary directory and compute path to output of `agda --html`
# NOTE: this assumes $OUT is equivalent to out/ plus the module path
HTML_DIR="$(mktemp -d)"
HTML="${OUT#out/}"
HTML="/${HTML//\//.}"
HTML="$HTML_DIR/$HTML"

# Highlight Syntax using Agda
set -o pipefail \
   && agda --html --html-highlight=code --html-dir="$HTML_DIR" "$SRC" "$@" \
    | sed '/^Generating.*/d; /^Warning\: HTML.*/d; /^reached from the.*/d; /^\s*$/d'

# Add source file to the Jekyll metadata
sed -i "1 s|---|---\nsrc: $SRC|" "$HTML"

# Add raw tags around Agda code blocks
sed -i "s|<pre class=\"Agda\">|{% raw %}<pre class=\"Agda\">|" "$HTML"
sed -i "s|</pre>|</pre>{% endraw %}|" "$HTML"

# Fix links to the Agda standard library
STDLIB_AGDALIB=`grep -m 1 "standard-library" $HOME/.agda/libraries`
STDLIB_AGDALIB="$(eval "echo -e \"$STDLIB_AGDALIB\"")"

STDLIB_INCLUDE=`grep -m 1 "include:" "$STDLIB_AGDALIB"`
STDLIB_INCLUDE="${STDLIB_INCLUDE#include: }"

STDLIB_PATH="$(dirname $STDLIB_AGDALIB)"
STDLIB_PATH="$STDLIB_PATH/$STDLIB_INCLUDE"

if [ -z "$AGDA_STDLIB_VERSION" ]; then
    AGDA_STDLIB_URL="https://agda.github.io/agda-stdlib/"
else
    AGDA_STDLIB_URL="https://agda.github.io/agda-stdlib/v$AGDA_STDLIB_VERSION/"
fi

if [ ! -f "$AGDA_STDLIB_SED" ]; then
    find "$STDLIB_PATH" -name "*.agda" -print0 | while read -d $'\0' AGDA_MODULE_PATH; do
        AGDA_MODULE=$(eval "echo \"$AGDA_MODULE_PATH\" | sed -e \"s|$STDLIB_PATH/||g; s|/|\\\.|g; s|\.agda|\\\.html|g\"")
        echo "s|$AGDA_MODULE|$AGDA_STDLIB_URL$AGDA_MODULE|g;" >> "$AGDA_STDLIB_SED"
    done
fi

sed -i -f "$AGDA_STDLIB_SED" "$HTML"

# Copy over the temporary file to the output path
mkdir -p "$OUT_DIR"
cp "$HTML" "$OUT"
