#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)
GAP_SOURCE="$ROOT_DIR/haetae-security/PAPER_CORRESPONDENCE_GAPS.md"
INVENTORY=${PAPER_GAP_OWNER_INVENTORY:-"$PROJECT_DIR/manifests/paper-gap-owners.csv"}
ASSUMPTIONS="$PROJECT_DIR/manifests/assumptions.md"
PREMISES="$PROJECT_DIR/manifests/theorem-premises.csv"
TMP_DIR=$(mktemp -d)

cleanup() {
  rm -rf "$TMP_DIR"
}
trap cleanup EXIT HUP INT TERM

EXPECTED_HEADER='gap_id,source_area,source_line,risk,status,owner_file,owner_lemma,acceptance_criterion,linked_ids'
if [ "$(sed -n '1p' "$INVENTORY")" != "$EXPECTED_HEADER" ]; then
  printf 'paper-gap owner check: unexpected CSV header\n' >&2
  exit 1
fi

awk '
  function trim(value) {
    sub(/^[[:space:]]+/, "", value)
    sub(/[[:space:]]+$/, "", value)
    return value
  }
  /^\| Area \| Current EasyCrypt status \|/ {
    in_table = 1
    next
  }
  in_table && /^\| ---/ { next }
  in_table && /^\|/ {
    count = split($0, fields, "|")
    area = trim(fields[2])
    risk = trim(fields[5])
    sub(/:.*/, "", risk)
    print area "," NR "," risk
    next
  }
  in_table { exit }
' "$GAP_SOURCE" | LC_ALL=C sort > "$TMP_DIR/source-keys"

awk -F, '
  NR == 1 { next }
  NF != 9 {
    print "paper-gap owner check: row " NR " has " NF " fields; expected 9" > "/dev/stderr"
    bad = 1
    next
  }
  $1 !~ /^GAP-[A-Z0-9-]+$/ || $2 == "" || $3 !~ /^[0-9]+$/ ||
  ($4 != "High" && $4 != "Medium") || $5 != "OPEN" ||
  $6 == "" || $6 == "-" || $7 == "" || $7 == "-" ||
  $8 == "" || $9 == "" {
    print "paper-gap owner check: invalid required field at row " NR > "/dev/stderr"
    bad = 1
  }
  { print $2 "," $3 "," $4 }
  END { exit bad }
' "$INVENTORY" | LC_ALL=C sort > "$TMP_DIR/inventory-keys"

if [ "$(wc -l < "$TMP_DIR/source-keys" | tr -d ' ')" -ne 8 ]; then
  printf 'paper-gap owner check: source table no longer has 8 rows\n' >&2
  exit 1
fi

if ! diff -u "$TMP_DIR/source-keys" "$TMP_DIR/inventory-keys"; then
  printf 'paper-gap owner check: source rows and owner inventory diverge\n' >&2
  exit 1
fi

awk -F'|' '
  /^\|[[:space:]]*[A-Z][A-Z0-9-]*[[:space:]]*\|/ {
    id = $2
    gsub(/^[[:space:]]+|[[:space:]]+$/, "", id)
    print id
  }
' "$ASSUMPTIONS" | LC_ALL=C sort -u > "$TMP_DIR/registered-assumption-ids"

awk -F, 'NR > 1 {
  count = split($9, ids, ";")
  for (i = 1; i <= count; i++) print ids[i]
}' "$INVENTORY" | LC_ALL=C sort -u > "$TMP_DIR/linked-assumption-ids"

comm -23 "$TMP_DIR/linked-assumption-ids" "$TMP_DIR/registered-assumption-ids" \
  > "$TMP_DIR/unknown-assumption-ids"
if [ -s "$TMP_DIR/unknown-assumption-ids" ]; then
  printf 'paper-gap owner check: linked assumption IDs are not registered:\n' >&2
  sed 's/^/  /' "$TMP_DIR/unknown-assumption-ids" >&2
  exit 1
fi

awk -F, 'NR > 1 { print $1 }' "$INVENTORY" | LC_ALL=C sort \
  > "$TMP_DIR/owner-gap-ids"
if [ -n "$(uniq -d "$TMP_DIR/owner-gap-ids")" ]; then
  printf 'paper-gap owner check: duplicate gap IDs\n' >&2
  uniq -d "$TMP_DIR/owner-gap-ids" >&2
  exit 1
fi

awk -F, 'NR > 1 && $8 == "OPEN" {
  count = split($9, ids, ";")
  for (i = 1; i <= count; i++) if (ids[i] ~ /^GAP-/) print ids[i]
}' "$PREMISES" | LC_ALL=C sort -u > "$TMP_DIR/open-premise-gap-ids"

comm -23 "$TMP_DIR/open-premise-gap-ids" "$TMP_DIR/owner-gap-ids" \
  > "$TMP_DIR/unowned-premise-gap-ids"
if [ -s "$TMP_DIR/unowned-premise-gap-ids" ]; then
  printf 'paper-gap owner check: open premise gap IDs lack planned owners:\n' >&2
  sed 's/^/  /' "$TMP_DIR/unowned-premise-gap-ids" >&2
  exit 1
fi

printf 'paper-gap owner check: PASS (8/8 source gaps; all open premise gap IDs owned)\n'
