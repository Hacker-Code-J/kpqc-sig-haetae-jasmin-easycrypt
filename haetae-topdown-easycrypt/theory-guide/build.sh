#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

cd "$SCRIPT_DIR"
latexmk -xelatex -halt-on-error -interaction=nonstopmode main.tex

if rg -ni 'undefined (reference|references|citation|citations)|citation .* undefined|reference .* undefined|LaTeX Error' \
    main.log main.fls main.fdb_latexmk 2>/dev/null; then
  printf 'FAIL theory guide has an undefined reference/citation or LaTeX error\n'
  exit 1
fi

printf 'PASS theory guide build %s/main.pdf\n' "$SCRIPT_DIR"
