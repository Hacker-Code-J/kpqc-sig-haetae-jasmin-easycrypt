#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
LATEX_DIR="$PROJECT_DIR/latex"

mkdir -p "$PROJECT_DIR/logs"

cd "$LATEX_DIR"
latexmk -pdf -halt-on-error -interaction=nonstopmode main.tex

if rg -ni 'undefined (reference|references|citation|citations)|citation .* undefined|reference .* undefined|LaTeX Error' \
    main.log main.fls main.fdb_latexmk 2>/dev/null; then
  printf 'FAIL LaTeX undefined reference/citation or error\n'
  exit 1
fi

if rg -n 'Overfull \\[hv]box' main.log; then
  printf 'FAIL LaTeX overfull box\n'
  exit 1
fi

printf 'PASS notes build %s/main.pdf\n' "$LATEX_DIR"
