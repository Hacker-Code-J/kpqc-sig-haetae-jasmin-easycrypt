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

TARGET_DIR="$OUTPUT_DIR/verify-unpack-v3"
TARGET="$TARGET_DIR/VerifyUnpackMode2Target.ec"
mkdir -p "$TARGET_DIR"

# Keep this post-freeze extraction separate from the frozen five-helper Verify
# core.  The root is the exact helper called by verify.jazz; jasmin2ec includes
# only its reachable decoding, seed-expansion, arithmetic, and NTT closure.
"$JASMIN2EC_BIN" --array-model=barray \
  --output-array="$TARGET_DIR" \
  -o "$TARGET" \
  -f _unpack_vk_m23_full \
  "$ROOT_DIR/haetae-ref-jasmin/jasmin/verify.jazz"

if [ -n "$SERVER_SOCKET" ]; then
  "$EASYCRYPT_BIN" compile -script -no-eco "$TARGET" \
    -I "$TARGET_DIR" -server "$SERVER_SOCKET" -max-provers 1 \
    < /dev/null
else
  "$EASYCRYPT_BIN" compile -script -no-eco "$TARGET" \
    -I "$TARGET_DIR" < /dev/null
fi

printf 'PASS focused Verify V-3 unpack extraction target=%s\n' "$TARGET"
