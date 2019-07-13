#!/bin/bash

AGDA_STDLIB_SED=".agda-stdlib.sed"

SRC="$1"
shift

OUT="$1"
OUT_DIR="$(dirname $OUT)"
shift

# Extract the module name from the Agda file
# NOTE: this fails if there is more than a single space after 'module'
MOD_NAME=`grep -oP -m 1 "(?<=^module )(\\S+)(?=\\s+(\\S+\\s+)*where)" "$SRC"`

# Create temporary directory and compute path to output of `agda --html`
HTML_DIR="$(mktemp -d)"
SRC_EXT="$(basename $SRC)"
SRC_EXT="${SRC_EXT##*.}"
HTML="$HTML_DIR/$MOD_NAME.$SRC_EXT"

# Highlight Syntax using Agda
set -o pipefail \
   && agda --html --html-highlight=code --html-dir="$HTML_DIR" "$SRC" "$@" \
    | sed '/^Generating.*/d; /^Warning\: HTML.*/d; /^reached from the.*/d; /^\s*$/d'

# Check if the highlighted file was successfully generated
if [[ ! -f "$HTML" ]]; then
    echo "File not generated: $FILE"
    exit 1
fi

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

# Create a sed script which matches and replaces all Agda standard library links
if [ ! -f "$AGDA_STDLIB_SED" ]; then
    echo "s|\\(Agda\\.[A-Za-z\\.]*\\)|$AGDA_STDLIB_URL\\1|;" > "$AGDA_STDLIB_SED"
    find "$STDLIB_PATH" -name "*.agda" -print0 | while read -d $'\0' AGDA_MODULE_PATH; do
        AGDA_MODULE=$(eval "echo \"$AGDA_MODULE_PATH\" | sed -e \"s|$STDLIB_PATH/||g; s|/|\\\.|g; s|\.agda|\\\.html|g\"")
        echo "s|$AGDA_MODULE|$AGDA_STDLIB_URL$AGDA_MODULE|g;" >> "$AGDA_STDLIB_SED"
    done
fi

sed -i -f "$AGDA_STDLIB_SED" "$HTML"

# Fix links to local modules
# TODO:
#   1) gather source files from the dirname and --include-path arguments, e.g., src/ and courses/tspl/2018/
#   2) compute module filenames for these files and compute their HTML output names (as above)
#   3) compute output filenames for these files (requires output names to be computable)
#   4) create sed script which matches and replaces the HTML filenames with Jekyll links to the output filenames
#   5) run sed script

# Copy over the temporary file to the output path
mkdir -p "$OUT_DIR"
cp "$HTML" "$OUT"
