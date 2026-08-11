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

PACK_DIR="$OUTPUT_DIR/pack"
UNPACK_DIR="$OUTPUT_DIR/unpack"
mkdir -p "$PACK_DIR" "$UNPACK_DIR"

"$JASMIN2EC_BIN" --array-model=barray \
  --output-array="$PACK_DIR" \
  -o "$PACK_DIR/SignaturePackMode2Target.ec" \
  -f pack_sig_mode2_full_jazz \
  "$ROOT_DIR/haetae-ref-jasmin/jasmin/signature_pack.jazz"

"$JASMIN2EC_BIN" --array-model=barray \
  --output-array="$UNPACK_DIR" \
  -o "$UNPACK_DIR/SignatureUnpackMode2Target.ec" \
  -f unpack_sig_mode2_full_jazz \
  "$ROOT_DIR/haetae-ref-jasmin/jasmin/signature_unpack.jazz"

compile_target() {
  target=$1
  include_dir=$2
  if [ -n "$SERVER_SOCKET" ]; then
    "$EASYCRYPT_BIN" compile -script -no-eco "$target" \
      -I "$include_dir" -server "$SERVER_SOCKET" -max-provers 1 \
      < /dev/null
  else
    "$EASYCRYPT_BIN" compile -script -no-eco "$target" \
      -I "$include_dir" < /dev/null
  fi
}

compile_target "$PACK_DIR/SignaturePackMode2Target.ec" "$PACK_DIR"
compile_target "$UNPACK_DIR/SignatureUnpackMode2Target.ec" "$UNPACK_DIR"

printf 'PASS focused signature codec extraction pack=%s unpack=%s\n' \
  "$PACK_DIR/SignaturePackMode2Target.ec" \
  "$UNPACK_DIR/SignatureUnpackMode2Target.ec"
