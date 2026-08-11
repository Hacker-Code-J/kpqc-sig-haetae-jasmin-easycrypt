#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}
WHY3_BIN=${WHY3:-why3}
WHY3SERVER_BIN=${WHY3SERVER:-"$($WHY3_BIN --print-libdir)/why3server"}
LOG_DIR="$PROJECT_DIR/logs/baselines"

mkdir -p "$LOG_DIR"
WORK_DIR=$(mktemp -d)
SERVER_SOCKET="$WORK_DIR/why3server.socket"
SERVER_PID=
cleanup() {
  if [ -n "$SERVER_PID" ]; then
    kill "$SERVER_PID" 2>/dev/null || true
    wait "$SERVER_PID" 2>/dev/null || true
  fi
  rm -rf "$WORK_DIR"
}
trap cleanup EXIT HUP INT TERM

"$WHY3SERVER_BIN" --socket "$SERVER_SOCKET" -j 1 \
  > "$LOG_DIR/why3server.log" 2>&1 &
SERVER_PID=$!
server_wait=0
while [ ! -S "$SERVER_SOCKET" ] && [ "$server_wait" -lt 50 ]; do
  sleep 0.1
  server_wait=$((server_wait + 1))
done
[ -S "$SERVER_SOCKET" ] || exit 1

SUMMARY="$LOG_DIR/summary.txt"
: > "$SUMMARY"
"$SCRIPT_DIR/check-source-drift.sh" > "$LOG_DIR/source-before.log" 2>&1

SECURITY_DIR="$ROOT_DIR/haetae-security/provable-security/easycrypt"
SECURITY_MANIFEST="$ROOT_DIR/haetae-security/provable-security/proof-files.txt"
security_count=0
while IFS= read -r file || [ -n "$file" ]; do
  case "$file" in
    ''|\#*) continue ;;
  esac
  name=$(basename "$file" .ec)
  "$EASYCRYPT_BIN" compile -script -no-eco "$SECURITY_DIR/$file" \
    -I "$SECURITY_DIR" -I "$ROOT_DIR/haetae-security/kyber-security" \
    -server "$SERVER_SOCKET" -max-provers 1 < /dev/null \
    > "$LOG_DIR/security-$name.log" 2>&1
  security_count=$((security_count + 1))
done < "$SECURITY_MANIFEST"
printf 'PASS security fresh targets=%s\n' "$security_count" \
  | tee -a "$SUMMARY"

REF="$ROOT_DIR/haetae-ref-easycrypt/easycrypt"
"$EASYCRYPT_BIN" compile -script -no-eco \
  "$REF/refinement/TargetNTTRefinement.ec" \
  -I "$REF/extract/ntt" -I "$REF/refinement" \
  -I "$ROOT_DIR/haetae-ntt-verify/easycrypt-ct" -I "$REF/support" \
  -server "$SERVER_SOCKET" -max-provers 1 < /dev/null \
  > "$LOG_DIR/ntt-target.log" 2>&1
printf 'PASS NTT target refinement\n' | tee -a "$SUMMARY"

"$EASYCRYPT_BIN" compile -script -no-eco \
  "$REF/extract/fips202/Fips202ShakeTarget.ec" \
  -I "$REF/extract/fips202" \
  -server "$SERVER_SOCKET" -max-provers 1 < /dev/null \
  > "$LOG_DIR/fips202-extraction.log" 2>&1
printf 'PASS FIPS202 generated extraction target\n' | tee -a "$SUMMARY"

"$EASYCRYPT_BIN" compile -script -no-eco \
  "$REF/refinement/TargetKeygenMode2ParentComposition.ec" \
  -I "$REF/extract/keygen-mode2-parent" \
  -I "$REF/extract/keygen-sampler-callers" \
  -I "$REF/spec" -I "$REF/refinement" -I "$SECURITY_DIR" \
  -server "$SERVER_SOCKET" -max-provers 1 < /dev/null \
  > "$LOG_DIR/keygen-mode2-parent.log" 2>&1
printf 'PASS KeyGen mode-2 parent composition\n' | tee -a "$SUMMARY"

"$EASYCRYPT_BIN" compile -script -no-eco \
  "$REF/refinement/TargetKeygenM23FullFirstAttempt.ec" \
  -I "$REF/extract/keygen-mode2-parent" \
  -I "$REF/extract/keygen-sampler-callers" -I "$REF/extract/ntt" \
  -I "$REF/spec" -I "$REF/refinement" -I "$REF/support" \
  -I "$SECURITY_DIR" -I "$ROOT_DIR/haetae-ntt-verify/easycrypt-ct" \
  -server "$SERVER_SOCKET" -max-provers 1 < /dev/null \
  > "$LOG_DIR/keygen-m23-first-attempt.log" 2>&1
printf 'PASS KeyGen M23 first-attempt head\n' | tee -a "$SUMMARY"

"$SCRIPT_DIR/check-source-drift.sh" > "$LOG_DIR/source-after.log" 2>&1
printf 'RESULT PASS selected-baselines=20 read-only=true\n' | tee -a "$SUMMARY"
