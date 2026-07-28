#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
EASYCRYPT_DIR="$PROJECT_DIR/easycrypt"
PARENT_EXTRACT_DIR="$EASYCRYPT_DIR/extract/keygen-mode2-parent"
CALLER_EXTRACT_DIR="$EASYCRYPT_DIR/extract/keygen-sampler-callers"
NTT_EXTRACT_DIR="$EASYCRYPT_DIR/extract/ntt"
SPEC_DIR="$EASYCRYPT_DIR/spec"
REFINEMENT_DIR="$EASYCRYPT_DIR/refinement"
LOCAL_SUPPORT_DIR="$EASYCRYPT_DIR/support"
SECURITY_DIR="$PROJECT_DIR/../haetae-security/provable-security/easycrypt"
NTT_SUPPORT_DIR=${NTT_SUPPORT_DIR:-"$PROJECT_DIR/../haetae-ntt-verify/easycrypt-ct"}
NTT_SUPPORT_HASHES="$PROJECT_DIR/manifests/ntt-proof-support.sha256"
FILE_MANIFEST="$PROJECT_DIR/manifests/keygen-m23-matrix-proof-files.txt"
LOG_DIR="$PROJECT_DIR/logs/keygen-m23-matrix-proof"
SUMMARY="$PROJECT_DIR/logs/keygen-m23-matrix-proof-summary.txt"
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}
WHY3_BIN=${WHY3:-why3}
WHY3SERVER_BIN=${WHY3SERVER:-"$($WHY3_BIN --print-libdir)/why3server"}
MAX_PROVERS=${EC_MAX_PROVERS:-1}
EASYCRYPT_BIN_PATH=$(command -v "$EASYCRYPT_BIN")
WHY3_VERSION=$("$WHY3_BIN" --version | head -n 1)

mkdir -p "$LOG_DIR"

SERVER_DIR=
SERVER_SOCKET=${WHY3_SERVER_SOCKET:-}
SERVER_LOG="$LOG_DIR/why3server.log"
SERVER_PID=

cleanup() {
  if [ -n "$SERVER_PID" ]; then
    kill "$SERVER_PID" 2>/dev/null || true
    wait "$SERVER_PID" 2>/dev/null || true
  fi
  if [ -n "$SERVER_DIR" ]; then
    rm -rf "$SERVER_DIR"
  fi
}
trap cleanup EXIT HUP INT TERM

if [ -z "$SERVER_SOCKET" ]; then
  if [ ! -x "$WHY3SERVER_BIN" ]; then
    printf 'FAIL missing Why3 server executable: %s\n' "$WHY3SERVER_BIN"
    exit 2
  fi
  SERVER_DIR=$(mktemp -d)
  SERVER_SOCKET="$SERVER_DIR/why3server.socket"
  "$WHY3SERVER_BIN" --socket "$SERVER_SOCKET" -j "$MAX_PROVERS" \
    > "$SERVER_LOG" 2>&1 &
  SERVER_PID=$!
  server_wait=0
  while [ ! -S "$SERVER_SOCKET" ] && [ "$server_wait" -lt 50 ]; do
    sleep 0.1
    server_wait=$((server_wait + 1))
  done
  if [ ! -S "$SERVER_SOCKET" ]; then
    printf 'FAIL Why3 server startup log=%s\n' "$SERVER_LOG"
    tail -n 80 "$SERVER_LOG"
    exit 1
  fi
elif [ ! -S "$SERVER_SOCKET" ]; then
  printf 'FAIL supplied Why3 server socket is unavailable: %s\n' \
    "$SERVER_SOCKET"
  exit 2
fi

if [ -z "$SERVER_DIR" ]; then
  SERVER_DIR=$(mktemp -d)
fi

SOURCE_LOG="$LOG_DIR/source-hash-check.log"
"$SCRIPT_DIR/check-sources.sh" > "$SOURCE_LOG" 2>&1

DRIFT_LOG="$LOG_DIR/parent-extraction-drift.log"
"$SCRIPT_DIR/check-keygen-mode2-parent-extract-drift.sh" \
  > "$DRIFT_LOG" 2>&1

CALLER_DRIFT_LOG="$LOG_DIR/caller-extraction-drift.log"
"$SCRIPT_DIR/check-keygen-sampler-callers-extract-drift.sh" \
  > "$CALLER_DRIFT_LOG" 2>&1

NTT_DRIFT_LOG="$LOG_DIR/ntt-extraction-drift.log"
"$SCRIPT_DIR/check-ntt-extract-drift.sh" \
  > "$NTT_DRIFT_LOG" 2>&1

SUPPORT_LOG="$LOG_DIR/ntt-support-hash-check.log"
(cd "$PROJECT_DIR" && sha256sum -c "$NTT_SUPPORT_HASHES") \
  > "$SUPPORT_LOG" 2>&1

AUTHORED_FILES="$SERVER_DIR/authored-files.txt"
sed "s#^#$EASYCRYPT_DIR/#" "$FILE_MANIFEST" > "$AUTHORED_FILES"

{
  printf 'HAETAE mode-2 key-generation matrix, finalization, and singular-word proof verification\n'
  printf 'Date (UTC): %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf 'Command: ./scripts/verify-keygen-m23-matrix-proof.sh\n'
  printf 'Toolchain: easycrypt=%s; %s; max-provers=%s\n' \
    "$EASYCRYPT_BIN_PATH" "$WHY3_VERSION" "$MAX_PROVERS"
  printf 'Actual target: easycrypt/extract/keygen-mode2-parent/KeygenMode2ParentTarget.ec\n'
  printf 'Proof manifest: manifests/keygen-m23-matrix-proof-files.txt\n'
  printf 'Project NTT loop support: easycrypt/support/RefJasminNTTLoop.ec\n'
  printf 'Imported NTT dependency directory: %s\n\n' "$NTT_SUPPORT_DIR"
  printf 'PASS canonical source hash check\n'
  cat "$DRIFT_LOG"
  cat "$CALLER_DRIFT_LOG"
  cat "$NTT_DRIFT_LOG"
  printf 'PASS NTT support hash check (%s files)\n' \
    "$(wc -l < "$NTT_SUPPORT_HASHES" | tr -d ' ')"
} > "$SUMMARY"

passed=0
total=0
while IFS= read -r file || [ -n "$file" ]; do
  total=$((total + 1))
  name=$(basename "$file" .ec)
  log="$LOG_DIR/$name.log"
  if "$EASYCRYPT_BIN" compile -no-eco "$EASYCRYPT_DIR/$file" \
      -server "$SERVER_SOCKET" -max-provers "$MAX_PROVERS" \
      -I "$PARENT_EXTRACT_DIR" -I "$CALLER_EXTRACT_DIR" \
      -I "$NTT_EXTRACT_DIR" -I "$SPEC_DIR" -I "$REFINEMENT_DIR" \
      -I "$SECURITY_DIR" -I "$NTT_SUPPORT_DIR" -I "$LOCAL_SUPPORT_DIR" \
      < /dev/null > "$log" 2>&1; then
    passed=$((passed + 1))
    printf 'PASS compile %s\n' "$file" | tee -a "$SUMMARY"
  else
    status=$?
    printf 'FAIL compile %s exit=%s log=%s\n' \
      "$file" "$status" "$log" | tee -a "$SUMMARY"
    tail -n 80 "$log"
    exit "$status"
  fi
done < "$FILE_MANIFEST"

HOLE_LOG="$LOG_DIR/proof-hole-scan.log"
if xargs rg -n '(^|[^[:alnum:]_])(admit|abort)([^[:alnum:]_]|$)' \
    < "$AUTHORED_FILES" > "$HOLE_LOG"; then
  printf 'FAIL proof-hole scan log=%s\n' "$HOLE_LOG" | tee -a "$SUMMARY"
  cat "$HOLE_LOG"
  exit 1
fi
printf 'PASS proof-hole scan (no admit/abort proof commands)\n' \
  | tee -a "$SUMMARY"

AXIOM_LOG="$LOG_DIR/axiom-declaration-scan.log"
if xargs rg -n '^[[:space:]]*axiom[[:space:]]' \
    < "$AUTHORED_FILES" > "$AXIOM_LOG"; then
  printf 'FAIL authored axiom declaration scan log=%s\n' "$AXIOM_LOG" \
    | tee -a "$SUMMARY"
  cat "$AXIOM_LOG"
  exit 1
fi
printf 'PASS authored axiom declaration scan (no declarations)\n' \
  | tee -a "$SUMMARY"

DEBUG_LOG="$LOG_DIR/debug-command-scan.log"
if xargs rg -n '^[[:space:]]*print[[:space:]]+(goal|all)([^[:alnum:]_]|$)' \
    < "$AUTHORED_FILES" > "$DEBUG_LOG"; then
  printf 'FAIL leftover debug command scan log=%s\n' "$DEBUG_LOG" \
    | tee -a "$SUMMARY"
  cat "$DEBUG_LOG"
  exit 1
fi
printf 'PASS debug command scan (no print goal/all commands)\n' \
  | tee -a "$SUMMARY"

printf 'RESULT: PASS compiled=%s total=%s mode=-no-eco\n' "$passed" "$total" \
  | tee -a "$SUMMARY"
printf 'Exit status: 0\n' | tee -a "$SUMMARY"
