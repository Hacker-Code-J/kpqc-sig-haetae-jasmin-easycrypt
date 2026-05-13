#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../.." && pwd)
MANIFEST="$ROOT/provable-security/proof-files.txt"
ECDIR="$ROOT/provable-security/easycrypt"

if [ ! -f "$MANIFEST" ]; then
  echo "missing manifest: $MANIFEST" >&2
  exit 1
fi

printf '%s,%s,%s,%s,%s,%s,%s,%s\n' \
  file lines types ops modules lemmas axioms hoare_equiv

total_lines=0
total_types=0
total_ops=0
total_modules=0
total_lemmas=0
total_axioms=0
total_hoare=0

while IFS= read -r rel || [ -n "$rel" ]; do
  case "$rel" in
    ''|'#'*) continue ;;
  esac

  file="$ECDIR/$rel"
  if [ ! -f "$file" ]; then
    file="$ROOT/$rel"
  fi
  if [ ! -f "$file" ]; then
    echo "missing proof file listed in manifest: $rel" >&2
    exit 1
  fi

  lines=$(wc -l < "$file" | tr -d ' ')
  types=$(grep -Ec '^[[:space:]]*(type|abbrev[[:space:]]+type)[[:space:]]+' "$file" || true)
  ops=$(grep -Ec '^[[:space:]]*(op|pred)[[:space:]]+' "$file" || true)
  modules=$(grep -Ec '^[[:space:]]*module([[:space:]]+type)?[[:space:]]+' "$file" || true)
  lemmas=$(grep -Ec '^[[:space:]]*lemma[[:space:]]+' "$file" || true)
  axioms=$(grep -Ec '^[[:space:]]*axiom[[:space:]]+' "$file" || true)
  hoare=$(grep -Ec '^[[:space:]]*(hoare|phoare|equiv)\[' "$file" || true)

  printf '%s,%s,%s,%s,%s,%s,%s,%s\n' \
    "$rel" "$lines" "$types" "$ops" "$modules" "$lemmas" "$axioms" "$hoare"

  total_lines=$((total_lines + lines))
  total_types=$((total_types + types))
  total_ops=$((total_ops + ops))
  total_modules=$((total_modules + modules))
  total_lemmas=$((total_lemmas + lemmas))
  total_axioms=$((total_axioms + axioms))
  total_hoare=$((total_hoare + hoare))
done < "$MANIFEST"

printf '%s,%s,%s,%s,%s,%s,%s,%s\n' \
  TOTAL "$total_lines" "$total_types" "$total_ops" \
  "$total_modules" "$total_lemmas" "$total_axioms" "$total_hoare"
