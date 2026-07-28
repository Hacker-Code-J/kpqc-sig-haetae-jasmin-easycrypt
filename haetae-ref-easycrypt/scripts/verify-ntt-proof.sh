#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
EASYCRYPT_DIR="$PROJECT_DIR/easycrypt"
EXTRACT_DIR="$EASYCRYPT_DIR/extract/ntt"
REFINEMENT_DIR="$EASYCRYPT_DIR/refinement"
LOCAL_SUPPORT_DIR="$EASYCRYPT_DIR/support"
OLD_PROOF_DIR=${NTT_SUPPORT_DIR:-"$PROJECT_DIR/../haetae-ntt-verify/easycrypt-ct"}
LOOP_SUPPORT="$LOCAL_SUPPORT_DIR/RefJasminNTTLoop.ec"
PROOF_MANIFEST="$PROJECT_DIR/manifests/ntt-proof-files.txt"
SHARED_MANIFEST="$PROJECT_DIR/manifests/ntt-proof-shared-theories.txt"
SUPPORT_HASHES="$PROJECT_DIR/manifests/ntt-proof-support.sha256"
LOG_DIR="$PROJECT_DIR/logs/ntt-proof"
SUMMARY="$PROJECT_DIR/logs/ntt-proof-summary.txt"
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}
MAX_EASYCRYPT_ATTEMPTS=${MAX_EASYCRYPT_ATTEMPTS:-6}
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

if [ ! -x "$WHY3SERVER_BIN" ]; then
  printf 'FAIL missing Why3 server executable: %s\n' "$WHY3SERVER_BIN"
  exit 2
fi

if [ -z "$SERVER_SOCKET" ]; then
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

SOURCE_LOG="$LOG_DIR/source-hash-check.log"
"$SCRIPT_DIR/check-sources.sh" > "$SOURCE_LOG" 2>&1

DRIFT_LOG="$LOG_DIR/extraction-drift.log"
"$SCRIPT_DIR/check-ntt-extract-drift.sh" > "$DRIFT_LOG" 2>&1

SUPPORT_LOG="$LOG_DIR/support-hash-check.log"
(cd "$PROJECT_DIR" && sha256sum -c "$SUPPORT_HASHES") \
  > "$SUPPORT_LOG" 2>&1

SHARED_LOG="$LOG_DIR/shared-theory-identity.log"
: > "$SHARED_LOG"
shared_count=0
while IFS= read -r file || [ -n "$file" ]; do
  if diff -u "$OLD_PROOF_DIR/$file" "$EXTRACT_DIR/$file" \
      >> "$SHARED_LOG"; then
    shared_count=$((shared_count + 1))
  else
    printf 'FAIL shared generated theory differs: %s\n' "$file"
    cat "$SHARED_LOG"
    exit 1
  fi
done < "$SHARED_MANIFEST"

{
  printf 'HAETAE target NTT mathematical refinement verification\n'
  printf 'Date (UTC): %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf 'Command: ./scripts/verify-ntt-proof.sh\n'
  printf 'Toolchain: easycrypt=%s; %s; max-provers=%s\n' \
    "$EASYCRYPT_BIN_PATH" "$WHY3_VERSION" "$MAX_PROVERS"
  printf 'Actual target: easycrypt/extract/ntt/HpolyTarget.ec\n'
  printf 'Authored refinement: easycrypt/refinement/TargetNTTRefinement.ec\n'
  printf 'Project NTT loop support: easycrypt/support/RefJasminNTTLoop.ec\n'
  printf 'Imported NTT dependency directory: %s\n\n' "$OLD_PROOF_DIR"
  printf 'PASS canonical source hash check\n'
  cat "$DRIFT_LOG"
  printf 'PASS imported proof support hash check (%s files)\n' \
    "$(wc -l < "$SUPPORT_HASHES" | tr -d ' ')"
  printf 'PASS byte-identical generated representations (%s files)\n' \
    "$shared_count"
} > "$SUMMARY"

passed=0
total=0
while IFS= read -r file || [ -n "$file" ]; do
  total=$((total + 1))
  name=$(basename "$file" .ec)
  log="$LOG_DIR/$name.log"
  attempt=0
  while :; do
    attempt=$((attempt + 1))
    if "$EASYCRYPT_BIN" compile -no-eco "$EASYCRYPT_DIR/$file" \
        -I "$EXTRACT_DIR" -I "$REFINEMENT_DIR" \
        -I "$OLD_PROOF_DIR" -I "$LOCAL_SUPPORT_DIR" \
        -server "$SERVER_SOCKET" -max-provers "$MAX_PROVERS" \
        < /dev/null > "$log" 2>&1; then
      passed=$((passed + 1))
      printf 'PASS compile %s attempts=%s\n' "$file" "$attempt" \
        | tee -a "$SUMMARY"
      break
    else
      status=$?
    fi
    if [ "$attempt" -lt "$MAX_EASYCRYPT_ATTEMPTS" ] &&
        rg -q 'cannot start & connect to why3server' "$log"; then
      continue
    fi
    printf 'FAIL compile %s exit=%s log=%s\n' \
      "$file" "$status" "$log" | tee -a "$SUMMARY"
    tail -n 80 "$log"
    exit "$status"
  done
done < "$PROOF_MANIFEST"

HOLE_LOG="$LOG_DIR/proof-hole-scan.log"
if rg -n '(^|[^[:alnum:]_])(admit|abort)([^[:alnum:]_]|$)' \
    "$REFINEMENT_DIR/TargetNTTRefinement.ec" \
    "$LOOP_SUPPORT" > "$HOLE_LOG"; then
  printf 'FAIL proof-hole scan log=%s\n' "$HOLE_LOG" | tee -a "$SUMMARY"
  cat "$HOLE_LOG"
  exit 1
fi
printf 'PASS proof-hole scan (no admit/abort proof commands)\n' \
  | tee -a "$SUMMARY"

AXIOM_LOG="$LOG_DIR/axiom-declaration-scan.log"
if rg -n '^[[:space:]]*axiom[[:space:]]' \
    "$REFINEMENT_DIR/TargetNTTRefinement.ec" \
    "$LOOP_SUPPORT" > "$AXIOM_LOG"; then
  printf 'FAIL authored axiom declaration scan log=%s\n' "$AXIOM_LOG" \
    | tee -a "$SUMMARY"
  cat "$AXIOM_LOG"
  exit 1
fi
printf 'PASS authored axiom declaration scan (no declarations)\n' \
  | tee -a "$SUMMARY"

printf 'RESULT: PASS compiled=%s total=%s mode=-no-eco\n' "$passed" "$total" \
  | tee -a "$SUMMARY"
printf 'Exit status: 0\n' | tee -a "$SUMMARY"
