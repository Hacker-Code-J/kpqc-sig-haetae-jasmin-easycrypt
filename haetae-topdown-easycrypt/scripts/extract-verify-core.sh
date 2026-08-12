#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)
JASMIN2EC_BIN=${JASMIN2EC:-jasmin2ec}
EASYCRYPT_BIN=${EASYCRYPT:-easycrypt}
SERVER_SOCKET=${WHY3_SERVER_SOCKET:-}

cleanup_output=0
if [ -n "${TOPDOWN_EXTRACT_DIR:-}" ]; then
  OUTPUT_DIR=$TOPDOWN_EXTRACT_DIR
  mkdir -p "$OUTPUT_DIR"
else
  OUTPUT_DIR=$(mktemp -d)
  cleanup_output=1
fi

cleanup() {
  if [ "$cleanup_output" -eq 1 ]; then
    rm -rf "$OUTPUT_DIR"
  fi
}
trap cleanup EXIT HUP INT TERM

TARGET_DIR="$OUTPUT_DIR/verify-core"
TARGET="$TARGET_DIR/VerifyCoreTarget.ec"
mkdir -p "$TARGET_DIR"

# Focus only the five actual mode-2 verify-core helpers. jasmin2ec pulls their
# transitive closure but excludes parser, codec, public API, and top-level
# verify wrappers.
"$JASMIN2EC_BIN" --array-model=barray \
  --output-array="$TARGET_DIR" \
  -o "$TARGET" \
  -f _verify_prepare_z1_wprime \
  -f _verify_matrix_crt \
  -f _sign_verify_recover_w_z2 \
  -f _sign_verify_norm_reject \
  -f _sign_verify_tail_m23 \
  "$ROOT_DIR/haetae-ref-jasmin/jasmin/verify.jazz"

if [ -n "$SERVER_SOCKET" ]; then
  "$EASYCRYPT_BIN" compile -script -no-eco "$TARGET" \
    -I "$TARGET_DIR" -server "$SERVER_SOCKET" -max-provers 1 \
    < /dev/null
else
  "$EASYCRYPT_BIN" compile -script -no-eco "$TARGET" \
    -I "$TARGET_DIR" < /dev/null
fi

printf 'PASS focused Verify core extraction target=%s\n' "$TARGET"
