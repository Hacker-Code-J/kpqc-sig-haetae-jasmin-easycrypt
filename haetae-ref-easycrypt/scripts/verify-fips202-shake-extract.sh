#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)
SOURCE="$ROOT_DIR/haetae-ref-jasmin/jasmin/fips202.jazz"
DEPENDENCY="$ROOT_DIR/haetae-ref-jasmin/jasmin/keccak.jinc"
EXTRACT_DIR="$PROJECT_DIR/easycrypt/extract/fips202"
FILE_MANIFEST="$PROJECT_DIR/manifests/fips202-shake-extract-files.txt"
LOG_DIR="$PROJECT_DIR/logs/fips202-shake-extract"
SUMMARY="$PROJECT_DIR/logs/fips202-shake-extract-summary.txt"
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}

mkdir -p "$LOG_DIR"

{
  printf 'HAETAE target FIPS202/SHAKE extraction verification\n'
  printf 'Date (UTC): %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf 'Source: ../haetae-ref-jasmin/jasmin/fips202.jazz\n'
  printf 'Dependency: ../haetae-ref-jasmin/jasmin/keccak.jinc\n'
  printf 'Functions: fips202_shake128_jazz fips202_shake256_jazz\n'
  printf 'Extraction model: barray\n'
  printf 'FIPS202 source SHA-256: %s\n' "$(sha256sum "$SOURCE" | awk '{print $1}')"
  printf 'Keccak dependency SHA-256: %s\n' "$(sha256sum "$DEPENDENCY" | awk '{print $1}')"
  printf 'Toolchain: manifests/toolchain.md\n\n'
} > "$SUMMARY"

"$SCRIPT_DIR/check-fips202-shake-extract-drift.sh" | tee -a "$SUMMARY"

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

PROOF_BOUNDARY_LOG="$LOG_DIR/proof-boundary-scan.log"
scan_status=0
rg -n '(^|[^[:alnum:]_])(admit|abort)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' \
  "$EXTRACT_DIR" --glob '*.ec' > "$PROOF_BOUNDARY_LOG" || scan_status=$?
case "$scan_status" in
  0)
    printf 'FAIL proof-boundary scan log=%s\n' "$PROOF_BOUNDARY_LOG" \
      | tee -a "$SUMMARY"
    cat "$PROOF_BOUNDARY_LOG"
    exit 1
    ;;
  1)
    printf 'PASS proof-boundary scan\n' | tee -a "$SUMMARY"
    ;;
  *)
    printf 'FAIL proof-boundary scan exit=%s log=%s\n' \
      "$scan_status" "$PROOF_BOUNDARY_LOG" | tee -a "$SUMMARY"
    exit "$scan_status"
    ;;
esac

sha256sum "$EXTRACT_DIR/Fips202ShakeTarget.ec" >> "$SUMMARY"
printf 'RESULT: PASS compiled=%s total=%s mode=-no-eco\n' "$passed" "$total" \
  | tee -a "$SUMMARY"
