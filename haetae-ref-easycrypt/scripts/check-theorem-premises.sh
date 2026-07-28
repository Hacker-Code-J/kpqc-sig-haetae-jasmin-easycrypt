#!/bin/sh

set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../.." && pwd)
SOURCE=haetae-security/provable-security/easycrypt/HAETAE_Security.ec
CSV=haetae-ref-easycrypt/manifests/theorem-premises.csv
EXPECTED_HEADER='theorem,file,theorem_line,premise_ordinal,premise_line,premise_meaning,classification,current_status,linked_id,discharge_lemma,closure_criterion'

cd "$ROOT"

test -f "$SOURCE"
test -f "$CSV"

header=$(sed -n '1p' "$CSV")
if [ "$header" != "$EXPECTED_HEADER" ]; then
  echo "theorem-premise check: unexpected CSV header" >&2
  exit 1
fi

tmp_dir=$(mktemp -d)
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

# The current security file puts each explicit premise's final implication on
# a line ending in `=>`.  Capture a stable key rather than attempting to parse
# the complete EasyCrypt grammar.
awk '
  /^lemma euf_cma_security[^[:space:]]*/ {
    theorem = $2
    theorem_line = NR
    ordinal = 0
    premise_line = 0
    in_statement = 1
    next
  }
  in_statement && /^proof[.]/ {
    in_statement = 0
    premise_line = 0
    next
  }
  in_statement {
    if ($0 ~ /^[[:space:]]*$/ ||
        $0 ~ /^[[:space:]]*&m[[:space:]]*:/) {
      next
    }
    if (premise_line == 0) {
      premise_line = NR
    }
    if ($0 ~ /=>[[:space:]]*$/) {
      ordinal++
      print theorem "," theorem_line "," ordinal "," premise_line
      premise_line = 0
    }
  }
' "$SOURCE" > "$tmp_dir/source-keys-unsorted"
LC_ALL=C sort "$tmp_dir/source-keys-unsorted" > "$tmp_dir/source-keys"

awk -F, -v source="$SOURCE" '
  BEGIN {
    allowed_id["CRYPTO-MLWE"] = 1
    allowed_id["CRYPTO-MSIS"] = 1
    allowed_id["MODEL-ROM"] = 1
    allowed_id["GAP-CHALLENGE"] = 1
    allowed_id["GAP-FORKING"] = 1
    allowed_id["GAP-MSIS"] = 1
    allowed_id["GAP-REJECTION"] = 1
    allowed_id["GAP-ROM-DOMAINS"] = 1
    allowed_id["GAP-SIGNING"] = 1
    allowed_id["GAP-TOP-LEVEL"] = 1
  }
  NR == 1 { next }
  NF != 11 {
    print "theorem-premise check: row " NR " has " NF " fields; expected 11" > "/dev/stderr"
    bad = 1
    next
  }
  $2 != source {
    print "theorem-premise check: row " NR " has unexpected source path: " $2 > "/dev/stderr"
    bad = 1
  }
  $6 == "" || $9 == "" || $10 == "" || $11 == "" {
    print "theorem-premise check: row " NR " has an empty required audit field" > "/dev/stderr"
    bad = 1
  }
  $7 != "retained hardness/ROM" &&
  $7 != "checked derived premise" &&
  $7 != "structural correspondence obligation" &&
  $7 != "implementation refinement obligation" {
    print "theorem-premise check: row " NR " has unknown classification: " $7 > "/dev/stderr"
    bad = 1
  }
  $8 != "RETAINED" && $8 != "CHECKED_STRUCTURAL" &&
  $8 != "CHECKED_COARSE" && $8 != "OPEN" {
    print "theorem-premise check: row " NR " has unknown status: " $8 > "/dev/stderr"
    bad = 1
  }
  $7 == "retained hardness/ROM" && $8 != "RETAINED" {
    print "theorem-premise check: row " NR " has inconsistent retained status" > "/dev/stderr"
    bad = 1
  }
  $7 == "checked derived premise" &&
  $8 != "CHECKED_STRUCTURAL" && $8 != "CHECKED_COARSE" {
    print "theorem-premise check: row " NR " has inconsistent checked status" > "/dev/stderr"
    bad = 1
  }
  $7 == "structural correspondence obligation" && $8 != "OPEN" {
    print "theorem-premise check: row " NR " has inconsistent structural status" > "/dev/stderr"
    bad = 1
  }
  {
    id_count = split($9, ids, ";")
    for (id_index = 1; id_index <= id_count; id_index++) {
      if (!(ids[id_index] in allowed_id)) {
        print "theorem-premise check: row " NR " has unknown linked ID: " ids[id_index] > "/dev/stderr"
        bad = 1
      }
    }
  }
  { print $1 "," $3 "," $4 "," $5 }
  END { exit bad }
' "$CSV" > "$tmp_dir/csv-keys-unsorted"
LC_ALL=C sort "$tmp_dir/csv-keys-unsorted" > "$tmp_dir/csv-keys"

if [ -s "$tmp_dir/csv-keys" ] &&
   [ -n "$(uniq -d "$tmp_dir/csv-keys")" ]; then
  echo "theorem-premise check: duplicate theorem/premise keys" >&2
  uniq -d "$tmp_dir/csv-keys" >&2
  exit 1
fi

source_count=$(wc -l < "$tmp_dir/source-keys" | tr -d ' ')
csv_count=$(wc -l < "$tmp_dir/csv-keys" | tr -d ' ')
theorem_count=$(cut -d, -f1 "$tmp_dir/source-keys" | uniq | wc -l | tr -d ' ')

if [ "$source_count" -ne 104 ] || [ "$theorem_count" -ne 25 ]; then
  echo "theorem-premise check: parser baseline changed: $theorem_count theorems / $source_count premises" >&2
  echo "Review the source formatting and this bounded parser before updating the audit." >&2
  exit 1
fi

if ! diff -u "$tmp_dir/source-keys" "$tmp_dir/csv-keys"; then
  echo "theorem-premise check: CSV keys do not exactly cover source premises" >&2
  exit 1
fi

echo "theorem-premise check: PASS ($theorem_count theorems; $csv_count premises)"
