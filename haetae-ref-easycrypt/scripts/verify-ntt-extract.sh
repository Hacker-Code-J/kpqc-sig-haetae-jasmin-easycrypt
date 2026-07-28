#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
EXTRACT_DIR="$PROJECT_DIR/easycrypt/extract/ntt"
FILE_MANIFEST="$PROJECT_DIR/manifests/ntt-extract-files.txt"
LOG_DIR="$PROJECT_DIR/logs/ntt-extract"
SUMMARY="$PROJECT_DIR/logs/ntt-extract-summary.txt"
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}

mkdir -p "$LOG_DIR"

{
  printf 'HAETAE target NTT extraction verification\n'
  printf 'Date (UTC): %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf 'Source: ../haetae-ref-jasmin/jasmin/hpoly.jazz\n'
  printf 'Functions: poly_ntt_jazz poly_invntt_jazz\n'
  printf 'Extraction model: barray\n'
  printf 'Toolchain: manifests/toolchain.md\n\n'
} > "$SUMMARY"

"$SCRIPT_DIR/check-ntt-extract-drift.sh" | tee -a "$SUMMARY"

passed=0
total=0
while IFS= read -r file || [ -n "$file" ]; do
  total=$((total + 1))
  log="$LOG_DIR/${file%.ec}.log"
  if "$EASYCRYPT_BIN" compile -no-eco "$EXTRACT_DIR/$file" \
      -I "$EXTRACT_DIR" < /dev/null > "$log" 2>&1; then
    passed=$((passed + 1))
    printf 'PASS compile %s\n' "$file" | tee -a "$SUMMARY"
  else
    status=$?
    printf 'FAIL compile %s exit=%s log=%s\n' "$file" "$status" "$log" \
      | tee -a "$SUMMARY"
    tail -n 80 "$log"
    exit "$status"
  fi
done < "$FILE_MANIFEST"

sha256sum "$EXTRACT_DIR/HpolyTarget.ec" >> "$SUMMARY"
printf 'RESULT: PASS compiled=%s total=%s mode=-no-eco\n' "$passed" "$total" \
  | tee -a "$SUMMARY"
