#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
project_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
repo_root=$(CDPATH= cd -- "$project_dir/.." && pwd)
proof_dir="$repo_root/haetae-security/provable-security/easycrypt"
proof_manifest="$repo_root/haetae-security/provable-security/proof-files.txt"
inventory=${SECURITY_DECLARATIONS_INVENTORY:-"$project_dir/manifests/security-declarations.csv"}
assumption_register="$project_dir/manifests/assumptions.md"

# This is deliberately a bounded declaration scanner rather than an EasyCrypt
# parser.  It recognizes the formatting used by the managed proof corpus:
# top-level `type`, `op`, `module type`, and `declare module` declarations start
# in column one; type/op statements end with a period on their final line; and
# definitions contain `=`.  It does not strip comments, expand clones/includes,
# or infer that a fully defined operator is semantically a proof-boundary
# stand-in.  If the corpus adopts alternate formatting, attributes other than
# the current op attributes, or declaration-generating syntax, update this
# scanner together with the inventory.  The separate theorem-premise and gap
# audits remain responsible for semantic placeholders with ordinary definitions.

if [ ! -f "$proof_manifest" ]; then
  printf 'FAIL: proof manifest not found: %s\n' "$proof_manifest" >&2
  exit 1
fi

if [ ! -f "$inventory" ]; then
  printf 'FAIL: declaration inventory not found: %s\n' "$inventory" >&2
  exit 1
fi

tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/haetae-security-declarations.XXXXXX")
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

discovered="$tmp_dir/discovered.csv"
covered="$tmp_dir/covered.csv"
missing="$tmp_dir/missing.csv"
extra="$tmp_dir/extra.csv"
duplicate="$tmp_dir/duplicate.csv"
registered_ids="$tmp_dir/registered-ids.txt"
linked_ids="$tmp_dir/linked-ids.txt"
unknown_ids="$tmp_dir/unknown-ids.txt"
: > "$discovered"

while IFS= read -r file || [ -n "$file" ]; do
  case "$file" in
    ''|'#'*) continue ;;
  esac

  source_file="$proof_dir/$file"
  if [ ! -f "$source_file" ]; then
    printf 'FAIL: managed proof file not found: %s\n' "$source_file" >&2
    exit 1
  fi

  awk -v file="$file" '
    function emit(kind, symbol, line) {
      print file "," line "," kind "," symbol
    }

    function finish_statement() {
      if (statement !~ /=/) {
        emit(statement_kind, statement_symbol, statement_line)
      }
      statement_kind = ""
      statement_symbol = ""
      statement = ""
    }

    statement_kind != "" {
      statement = statement " " $0
      if ($0 ~ /\.[[:space:]]*$/) {
        finish_statement()
      }
      next
    }

    /^type[[:space:]]+[A-Za-z_][A-Za-z0-9_]*/ {
      symbol = $0
      sub(/^type[[:space:]]+/, "", symbol)
      sub(/[^A-Za-z0-9_].*$/, "", symbol)
      statement_kind = "abstract_type"
      statement_symbol = symbol
      statement_line = NR
      statement = $0
      if ($0 ~ /\.[[:space:]]*$/) {
        finish_statement()
      }
      next
    }

    /^op[[:space:]]+/ {
      symbol = $0
      sub(/^op[[:space:]]+/, "", symbol)
      sub(/^\[[^]]*\][[:space:]]*/, "", symbol)
      sub(/[^A-Za-z0-9_].*$/, "", symbol)
      statement_kind = "bodyless_op"
      statement_symbol = symbol
      statement_line = NR
      statement = $0
      if ($0 ~ /\.[[:space:]]*$/) {
        finish_statement()
      }
      next
    }

    /^module type[[:space:]]+/ {
      symbol = $0
      sub(/^module type[[:space:]]+/, "", symbol)
      sub(/[^A-Za-z0-9_].*$/, "", symbol)
      emit("module_type", symbol, NR)
      next
    }

    /^declare module[[:space:]]+/ {
      symbol = $0
      sub(/^declare module[[:space:]]+/, "", symbol)
      sub(/[[:space:]]*<:.*/, "", symbol)
      emit("declared_module", symbol, NR)
      next
    }

    END {
      if (statement_kind != "") {
        print "unterminated declaration at " file ":" statement_line > "/dev/stderr"
        exit 2
      }
    }
  ' "$source_file" >> "$discovered"
done < "$proof_manifest"

expected_header='file,line,kind,symbol,classification,status,linked_id,closure_criterion'
actual_header=$(sed -n '1p' "$inventory")
if [ "$actual_header" != "$expected_header" ]; then
  printf 'FAIL: unexpected CSV header\nexpected: %s\nactual:   %s\n' \
    "$expected_header" "$actual_header" >&2
  exit 1
fi

if ! awk -F, '
  NR == 1 { next }
  NF != 8 {
    printf "invalid field count at inventory line %d: expected 8; got %d\n", NR, NF > "/dev/stderr"
    bad = 1
    next
  }
  $1 == "" || $2 !~ /^[0-9]+$/ || $3 == "" || $4 == "" ||
  $5 == "" || $6 == "" || $7 == "" || $8 == "" {
    printf "blank or invalid required field at inventory line %d\n", NR > "/dev/stderr"
    bad = 1
  }
  $3 != "abstract_type" && $3 != "bodyless_op" &&
  $3 != "module_type" && $3 != "declared_module" {
    printf "unknown declaration kind at inventory line %d: %s\n", NR, $3 > "/dev/stderr"
    bad = 1
  }
  $5 != "retained cryptographic assumption" &&
  $5 != "idealized model interface" &&
  $5 != "implementation correspondence obligation" &&
  $5 != "structural placeholder to remove" &&
  $5 != "trusted library interface" {
    printf "unknown classification at inventory line %d: %s\n", NR, $5 > "/dev/stderr"
    bad = 1
  }
  $6 != "RETAINED" && $6 != "TO_PROVE" && $6 != "TO_VALIDATE" {
    printf "unknown status at inventory line %d: %s\n", NR, $6 > "/dev/stderr"
    bad = 1
  }
  { print $1 "," $2 "," $3 "," $4 }
  END { exit bad }
' "$inventory" > "$covered"; then
  printf 'FAIL: malformed declaration inventory\n' >&2
  exit 1
fi

if [ ! -f "$assumption_register" ]; then
  printf 'FAIL: assumption register not found: %s\n' "$assumption_register" >&2
  exit 1
fi

awk -F'|' '
  /^\|[[:space:]]*[A-Z][A-Z0-9-]*[[:space:]]*\|/ {
    id = $2
    gsub(/^[[:space:]]+|[[:space:]]+$/, "", id)
    print id
  }
' "$assumption_register" | LC_ALL=C sort -u > "$registered_ids"
awk -F, 'NR > 1 { print $7 }' "$inventory" | LC_ALL=C sort -u > "$linked_ids"
comm -23 "$linked_ids" "$registered_ids" > "$unknown_ids"
if [ -s "$unknown_ids" ]; then
  printf 'FAIL: linked IDs absent from the assumption register:\n' >&2
  sed 's/^/  /' "$unknown_ids" >&2
  exit 1
fi

LC_ALL=C sort "$discovered" -o "$discovered"
LC_ALL=C sort "$covered" -o "$covered"
uniq -d "$covered" > "$duplicate"
comm -23 "$discovered" "$covered" > "$missing"
comm -13 "$discovered" "$covered" > "$extra"

if [ -s "$duplicate" ] || [ -s "$missing" ] || [ -s "$extra" ]; then
  if [ -s "$duplicate" ]; then
    printf 'FAIL: duplicate inventory keys:\n' >&2
    sed 's/^/  /' "$duplicate" >&2
  fi
  if [ -s "$missing" ]; then
    printf 'FAIL: discovered declarations missing from inventory:\n' >&2
    sed 's/^/  /' "$missing" >&2
  fi
  if [ -s "$extra" ]; then
    printf 'FAIL: inventory rows not found by scanner:\n' >&2
    sed 's/^/  /' "$extra" >&2
  fi
  exit 1
fi

managed_count=$(sed -e '/^[[:space:]]*#/d' -e '/^[[:space:]]*$/d' \
  "$proof_manifest" | wc -l | tr -d ' ')
declaration_count=$(wc -l < "$discovered" | tr -d ' ')

printf 'PASS: %s declarations covered across %s managed EasyCrypt files\n' \
  "$declaration_count" "$managed_count"
for kind in abstract_type bodyless_op module_type declared_module; do
  count=$(awk -F, -v kind="$kind" '$3 == kind { count++ } END { print count + 0 }' \
    "$discovered")
  printf '  %s: %s\n' "$kind" "$count"
done
