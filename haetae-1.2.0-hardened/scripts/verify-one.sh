#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
baseline_dir="$project_dir/../haetae-1.2.0-easycrypt"
cd -- "$project_dir"
[[ $# -ge 1 ]] || { echo "Usage: $0 TARGET.ec [EASYCRYPT_OPTIONS...]" >&2; exit 2; }
source_path=$1
shift
source_dir="$(cd -- "$(dirname -- "$source_path")" && pwd)"
source_basename="$(basename -- "$source_path")"
server_args=()
if [[ -n "${WHY3_SERVER_SOCKET:-}" ]]; then
  [[ -S "$WHY3_SERVER_SOCKET" ]] || { echo "Missing Why3 socket: $WHY3_SERVER_SOCKET" >&2; exit 2; }
  server_args=(-server "$WHY3_SERVER_SOCKET")
fi
verify_temp_dir="$(mktemp -d "${TMPDIR:-/tmp}/haetae120-hardened-eof.XXXXXXXX")"
trap 'rm -rf -- "$verify_temp_dir"' EXIT
cp -- "$source_path" "$verify_temp_dir/$source_basename"
cat >> "$verify_temp_dir/$source_basename" <<'EOF'

lemma __haetae120_hardened_eof_complete : true.
proof. trivial. qed.
EOF
"${EASYCRYPT:-easycrypt}" compile -no-eco -pragmas Proofs:check \
  -timeout "${EC_TIMEOUT:-10}" -max-provers "${EC_MAX_PROVERS:-1}" \
  "${server_args[@]}" -I "$source_dir" \
  -I easycrypt/generated -I easycrypt/theories -I easycrypt/proofs \
  -I "$baseline_dir/generated/sampler" -I "$baseline_dir/generated/ntt" \
  -I "$baseline_dir/generated/api" -I "$baseline_dir/theories" \
  -I "$baseline_dir/theories/ntt" -I "$baseline_dir/proofs" \
  "$verify_temp_dir/$source_basename" "$@"
