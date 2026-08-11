#!/usr/bin/env sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
ROOT_DIR=$(CDPATH= cd -- "$PROJECT_DIR/.." && pwd)
HASHES="$PROJECT_DIR/manifests/sources.sha256"

(cd "$ROOT_DIR" && sha256sum -c "$HASHES")

if ! git -C "$ROOT_DIR" diff --quiet -- \
    haetae-ref-jasmin haetae-ref-easycrypt haetae-ntt-verify \
    haetae-security easycrypt; then
  printf 'FAIL tracked read-only source has a working-tree diff\n'
  git -C "$ROOT_DIR" diff --stat -- \
    haetae-ref-jasmin haetae-ref-easycrypt haetae-ntt-verify \
    haetae-security easycrypt
  exit 1
fi

printf 'PASS source hashes and tracked read-only roots\n'
