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

PACK_DIR="$OUTPUT_DIR/packers"
mkdir -p "$PACK_DIR"

"$JASMIN2EC_BIN" --array-model=barray \
  --output-array="$PACK_DIR" \
  -o "$PACK_DIR/FocusedPackersTarget.ec" \
  -f _pack_vk_m23 \
  -f _pack_sk_m23 \
  "$ROOT_DIR/haetae-ref-jasmin/jasmin/keypair.jazz"

if [ -n "$SERVER_SOCKET" ]; then
  "$EASYCRYPT_BIN" compile -script -no-eco \
    "$PACK_DIR/FocusedPackersTarget.ec" -I "$PACK_DIR" \
    -server "$SERVER_SOCKET" -max-provers 1 < /dev/null
else
  "$EASYCRYPT_BIN" compile -script -no-eco \
    "$PACK_DIR/FocusedPackersTarget.ec" -I "$PACK_DIR" < /dev/null
fi

printf 'PASS focused packer extraction target=%s\n' \
  "$PACK_DIR/FocusedPackersTarget.ec"
