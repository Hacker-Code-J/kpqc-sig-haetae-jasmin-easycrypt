#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)
SECURITY_DIR="$ROOT_DIR/haetae-security"
PROOF_DIR="$SECURITY_DIR/provable-security/easycrypt"
MANIFEST="$SECURITY_DIR/provable-security/proof-files.txt"
LOG_DIR="$PROJECT_DIR/logs/security-fresh"
SUMMARY="$PROJECT_DIR/logs/security-fresh-summary.txt"
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}
PER_FILE_TIMEOUT=${EC_TIMEOUT:-900}

mkdir -p "$LOG_DIR"

{
  printf 'HAETAE security proof fresh-compilation summary\n'
  printf 'Date (UTC): %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf 'Command: easycrypt compile -no-eco <target> -I <proof-dir> -I <kyber-security>\n'
  printf 'Proof manifest: %s\n' "$MANIFEST"
  printf 'Source manifest: %s\n' "$PROJECT_DIR/manifests/sources.sha256"
  printf 'Toolchain record: %s\n\n' "$PROJECT_DIR/manifests/toolchain.md"
} > "$SUMMARY"

passed=0
total=0

while IFS= read -r file || [ -n "$file" ]; do
  case "$file" in
    ''|\#*) continue ;;
  esac

  total=$((total + 1))
  log="$LOG_DIR/${file%.ec}.log"
  printf '[%s] ' "$file"

  if timeout "$PER_FILE_TIMEOUT" "$EASYCRYPT_BIN" compile -no-eco \
      "$PROOF_DIR/$file" -max-provers "${EC_MAX_PROVERS:-1}" \
      -I "$PROOF_DIR" -I "$SECURITY_DIR/kyber-security" \
      > "$log" 2>&1; then
    passed=$((passed + 1))
    printf 'PASS\n'
    printf 'PASS %s\n' "$file" >> "$SUMMARY"
  else
    status=$?
    printf 'FAIL (exit %s)\n' "$status"
    printf 'FAIL %s exit=%s log=%s\n' "$file" "$status" "$log" >> "$SUMMARY"
    tail -n 80 "$log"
    printf 'RESULT: FAIL passed=%s total=%s\n' "$passed" "$total" >> "$SUMMARY"
    exit "$status"
  fi
done < "$MANIFEST"

HOLE_LOG="$LOG_DIR/proof-hole-scan.log"
if grep -En '^[[:space:]]*(admit|abort)([.;[:space:]]|$)' \
    "$PROOF_DIR"/*.ec > "$HOLE_LOG" 2>&1; then
  printf 'FAIL proof-hole scan log=%s\n' "$HOLE_LOG" | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS proof-hole scan (no admit/abort proof commands)\n' >> "$SUMMARY"

AXIOM_LOG="$LOG_DIR/axiom-declaration-scan.log"
if grep -En '^[[:space:]]*axiom[[:space:]]' \
    "$PROOF_DIR"/*.ec > "$AXIOM_LOG" 2>&1; then
  printf 'FAIL unexpected axiom declaration log=%s\n' "$AXIOM_LOG" \
    | tee -a "$SUMMARY"
  exit 1
fi
printf 'PASS axiom declaration scan (none found)\n' >> "$SUMMARY"

"$SCRIPT_DIR/check-security-declarations.sh" >> "$SUMMARY"
"$SCRIPT_DIR/check-theorem-premises.sh" >> "$SUMMARY"
"$SCRIPT_DIR/check-paper-gap-owners.sh" >> "$SUMMARY"

printf 'RESULT: PASS passed=%s total=%s mode=-no-eco\n' "$passed" "$total" \
  | tee -a "$SUMMARY"
