#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$SCRIPT_DIR"

latexmk -xelatex -halt-on-error -file-line-error -interaction=nonstopmode main.tex

if rg -ni \
  'undefined (reference|references|citation|citations)|citation .* undefined|reference .* undefined|LaTeX Error|Overfull \\hbox' \
  main.log main.blg main.fdb_latexmk 2>/dev/null; then
  printf 'FAIL: unresolved reference/citation, LaTeX error, or overfull box\n' >&2
  exit 1
fi

printf 'PASS: %s/main.pdf\n' "$SCRIPT_DIR"
