#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)
SOURCE="$ROOT_DIR/haetae-ref-jasmin/jasmin/keypair.jazz"
OUT_DIR="$PROJECT_DIR/easycrypt/extract/keygen-uniform-xof"
FILE_MANIFEST="$PROJECT_DIR/manifests/keygen-uniform-xof-extract-files.txt"
PROCEDURE_MANIFEST="$PROJECT_DIR/manifests/keygen-uniform-xof-procedures.txt"
TMP_DIR=$(mktemp -d)

cleanup() {
  rm -rf "$TMP_DIR"
}
trap cleanup EXIT HUP INT TERM

"$SCRIPT_DIR/check-sources.sh" >/dev/null

jasmin2ec --array-model=barray \
  --output-array="$TMP_DIR" \
  -o "$TMP_DIR/KeygenUniformXofTarget.ec" \
  -f _kp_poly_uniform_at_seedbuf_8192 \
  -f _kp_poly_uniform_at_seedbuf_2048 \
  "$SOURCE"

find "$TMP_DIR" -maxdepth 1 -type f -name '*.ec' -exec basename {} \; \
  | LC_ALL=C sort > "$TMP_DIR/generated-files.txt"
diff -u "$FILE_MANIFEST" "$TMP_DIR/generated-files.txt"

sed -n 's/^[[:space:]]*proc \([^ (]*\).*/\1/p' \
  "$TMP_DIR/KeygenUniformXofTarget.ec" > "$TMP_DIR/generated-procedures.txt"
diff -u "$PROCEDURE_MANIFEST" "$TMP_DIR/generated-procedures.txt"

mkdir -p "$OUT_DIR"
while IFS= read -r file || [ -n "$file" ]; do
  cp "$TMP_DIR/$file" "$OUT_DIR/$file"
done < "$FILE_MANIFEST"

printf 'Regenerated %s from %s\n' \
  "$OUT_DIR/KeygenUniformXofTarget.ec" "$SOURCE"
