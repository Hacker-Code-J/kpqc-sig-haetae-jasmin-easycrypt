#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
proof_dir="$script_dir/easycrypt"
manifest="$script_dir/proof-files.txt"
log_dir="$script_dir/logs"
summary="$log_dir/last-run-summary.txt"

easycrypt_bin=${EASYCRYPT:-easycrypt}
per_file_timeout=${EC_TIMEOUT:-900}
max_attempts=${EC_ATTEMPTS:-4}

mkdir -p "$log_dir"
: > "$summary"

printf 'HAETAE provable-security EasyCrypt verification\n' | tee -a "$summary"
printf 'Root: %s\n' "$root_dir" | tee -a "$summary"
printf 'Proof dir: %s\n' "$proof_dir" | tee -a "$summary"
printf 'Manifest: %s\n' "$manifest" | tee -a "$summary"
printf 'Per-file timeout: %ss\n' "$per_file_timeout" | tee -a "$summary"
printf 'Attempts per file: %s\n\n' "$max_attempts" | tee -a "$summary"

rc_all=0

while IFS= read -r file || [ -n "$file" ]; do
  case "$file" in
    ''|\#*) continue ;;
  esac

  src="$proof_dir/$file"
  log="$log_dir/${file%.ec}.log"
  printf '=== %s ===\n' "$file" | tee -a "$summary"

  if [ ! -f "$src" ]; then
    printf 'FAIL %s: file not found in %s\n' "$file" "$proof_dir" | tee -a "$summary"
    rc_all=1
    break
  fi

  attempt=1
  file_rc=1
  while [ "$attempt" -le "$max_attempts" ]; do
    attempt_log="$log.attempt-$attempt"
    if timeout "$per_file_timeout" "$easycrypt_bin" compile "$src" -max-provers "${EC_MAX_PROVERS:-1}" -I "$proof_dir" -I "$root_dir/kyber-security" > "$attempt_log" 2>&1; then
      cp "$attempt_log" "$log"
      printf 'PASS %s attempt=%s\n' "$file" "$attempt" | tee -a "$summary"
      file_rc=0
      break
    else
      file_rc=$?
      cp "$attempt_log" "$log"
      if [ "$attempt" -lt "$max_attempts" ]; then
        printf 'RETRY %s attempt=%s exit=%s\n' "$file" "$attempt" "$file_rc" | tee -a "$summary"
        sleep 5
      fi
    fi
    attempt=$((attempt + 1))
  done

  if [ "$file_rc" -ne 0 ]; then
    printf 'FAIL %s exit=%s\n' "$file" "$file_rc" | tee -a "$summary"
    printf 'Log: %s\n' "$log" | tee -a "$summary"
    tail -n 120 "$log" | tee -a "$summary"
    rc_all=$file_rc
    break
  fi
done < "$manifest"

if [ "$rc_all" -eq 0 ]; then
  printf '\nRESULT: PASS\n' | tee -a "$summary"
else
  printf '\nRESULT: FAIL\n' | tee -a "$summary"
fi

exit "$rc_all"
