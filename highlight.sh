#!/bin/bash

SRC="$1"
shift

OUT="$1"
OUT_DIR="$(dirname $OUT)"
shift

# NOTE: this assumes $OUT is equivalent to out/ plus the module path
HTML_DIR="$(mktemp -d)"
HTML="${OUT#out/}"
HTML="/${HTML//\//.}"
HTML="$HTML_DIR/$HTML"

set -o pipefail \
   && agda --html --html-highlight=code --html-dir="$HTML_DIR" "$SRC" "$@" \
    | sed '/^Generating.*/d; /^Warning\: HTML.*/d; /^reached from the.*/d; /^\s*$/d'

sed -i "1 s|---|---\nsrc       : $SRC |" "$HTML"
sed -i "s|<pre class=\"Agda\">|{% raw %}<pre class=\"Agda\">|" "$HTML"
sed -i "s|</pre>|</pre>{% endraw %}|" "$HTML"

mkdir -p "$OUT_DIR"
cp "$HTML" "$OUT"
