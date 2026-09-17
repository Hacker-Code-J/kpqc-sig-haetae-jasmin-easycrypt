#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$repo_root"

echo "Checking the pinned HAETAE-1.2.0 distribution..."
sha256sum --check --status docs/UPSTREAM-SHA256SUMS
echo "PASS: supplied distribution matches docs/UPSTREAM-SHA256SUMS"

# This distribution contains only the reference implementation.
exec bash HAETAE-1.2.0/kat.sh check ref
