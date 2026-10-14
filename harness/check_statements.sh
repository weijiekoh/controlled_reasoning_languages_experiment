#!/usr/bin/env bash
# Compile each statement file (proof = sorry) in lean_env. Print OK/FAIL per file.
# Usage: check_statements.sh <out.tsv> <file>...
set -u
out=$1; shift
env_dir="$(cd "$(dirname "$0")/.." && pwd)/lean_env"
check() {
  f=$1
  log=$(cd "$env_dir" && timeout 600 lake env lean "$f" 2>&1)
  if echo "$log" | grep -q 'error'; then
    printf '%s\tFAIL\t%s\n' "$(basename "$f" .lean)" "$(echo "$log" | grep -m1 error | tr '\t' ' ' | cut -c1-200)"
  else
    printf '%s\tOK\t\n' "$(basename "$f" .lean)"
  fi
}
export -f check
export env_dir
printf '%s\n' "$@" | xargs -P 16 -I{} bash -c 'check "$@"' _ {} > "$out"
