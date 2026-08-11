#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
MANIFEST="$PROJECT_DIR/manifests/proof-targets.txt"

failed=0
while IFS= read -r target || [ -n "$target" ]; do
  [ -n "$target" ] || continue
  if rg -ni '(^|[^[:alnum:]_])(admit|admitted|abort|sorry)([^[:alnum:]_]|$)' \
      "$PROJECT_DIR/$target"; then
    failed=1
  fi
done < "$MANIFEST"

if [ "$failed" -ne 0 ]; then
  printf 'FAIL proof-hole scan\n'
  exit 1
fi

printf 'PASS proof-hole scan\n'
