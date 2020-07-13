#!/bin/bash

AGDA_STDLIB_SED=".agda-stdlib.sed"

function sedi {
    sed --version >/dev/null 2>&1 && sed -i "$@" || sed -i "" "$@"
}

SRC="$1"
shift

function out_path {
    OUT="$1"
    OUT=`echo "$OUT" | sed -e "s|src/|out/|; s|courses/|out/|; s|\.lagda\.md|\.md|;"`
    echo "$OUT"
}

OUT="$(out_path $SRC)"
OUT_DIR="$(dirname $OUT)"

function html_path {
    SRC="$1"
    HTML_DIR="$2"

    # Extract the module name from the Agda file
    #
    # NOTE: This fails when there is no module statement,
    #       or when there is more than one space after 'module'.
    #
    MOD_NAME=`grep -o -m 1 "module\\s*\\(\\S\\S*\\)\\s.*where$" "$SRC" | cut -d ' ' -f 2`

    if [ -z "$MOD_NAME" ]
    then
        echo "Error: No module header detected in '$SRC'" 1>&2
        exit 1
    fi

    # Extract the extension from the Agda file
    SRC_EXT="$(basename $SRC)"
    SRC_EXT="${SRC_EXT##*.}"

    HTML="$HTML_DIR/$MOD_NAME.$SRC_EXT"
    echo "$HTML"
}

HTML_DIR="$(mktemp -d)"
HTML="$(html_path $SRC $HTML_DIR)"

# Highlight Syntax using Agda
set -o pipefail \
   && agda --html --html-highlight=code --html-dir="$HTML_DIR" "$SRC" "$@" \
    | sed '/^Generating.*/d; /^Warning\: HTML.*/d; /^reached from the.*/d; /^\s*$/d'

# Check if the highlighted file was successfully generated
if [[ ! -f "$HTML" ]]; then
    echo "Error: File not generated: '$FILE'" 1>&2
    exit 1
fi

# Add source file to the Jekyll metadata
#sedi "1 s|---|---\nsrc: $SRC|" "$HTML"
ed "$HTML" <<EOF >/dev/null 2>&1
2i
src       : "$SRC"
.
w
q
EOF

# Add raw tags around Agda code blocks
sedi "s|<pre class=\"Agda\">|{% raw %}<pre class=\"Agda\">|" "$HTML"
sedi "s|</pre>|</pre>{% endraw %}|" "$HTML"

# Fix links to the Agda standard library
STDLIB_AGDALIB=`grep -m 1 "standard-library" $HOME/.agda/libraries`
STDLIB_AGDALIB="${STDLIB_AGDALIB/#\~/$HOME}" # see https://stackoverflow.com/q/3963716/312692
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
    echo "s|\\(Agda\\.[A-Za-z\\.]+\\)|$AGDA_STDLIB_URL\\1|;" > "$AGDA_STDLIB_SED"
    find "$STDLIB_PATH" -name "*.agda" -print0 | while read -d $'\0' AGDA_MODULE_PATH; do
        AGDA_MODULE=$(eval "echo \"$AGDA_MODULE_PATH\" | sed -e \"s|$STDLIB_PATH/||g; s|/|\\\.|g; s|\.agda|\\\.html|g\"")
        echo "s|$AGDA_MODULE|$AGDA_STDLIB_URL$AGDA_MODULE|g;" >> "$AGDA_STDLIB_SED"
    done
fi

sedi -f "$AGDA_STDLIB_SED" "$HTML"

# Create a sed script which matches and repairs all local links
for INCLUDE_PATH in "$@"; do
    if [[ "$INCLUDE_PATH" = --include-path=* ]]; then
        INCLUDE_PATH="${INCLUDE_PATH:15}"
        INCLUDE_PATH="${INCLUDE_PATH%/}"
        LOCAL_LINKS_SED=`echo ".links-${INCLUDE_PATH}.sed" | sed -e "s|/|-|g;"`

        if [ ! -f "$LOCAL_LINKS_SED" ]; then
            find "$INCLUDE_PATH" -name "*.lagda.md" -print0 | while read -d $'\0' AGDA_MODULE_SRC; do
                AGDA_MODULE_OUT="$(out_path "$AGDA_MODULE_SRC")"
                AGDA_MODULE_HTML="$(basename "$(html_path "$AGDA_MODULE_SRC" "$HTML_DIR")" .md).html"
                echo "s|$AGDA_MODULE_HTML|{% endraw %}{{ site.baseurl }}{% link $AGDA_MODULE_OUT %}{% raw %}|g;" >> "$LOCAL_LINKS_SED"
            done
        fi

        sedi -f "$LOCAL_LINKS_SED" "$HTML"
    fi
done

# Copy over the temporary file to the output path
mkdir -p "$OUT_DIR"
cp "$HTML" "$OUT"
