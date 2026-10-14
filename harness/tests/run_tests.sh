#!/usr/bin/env bash
# Run every adversarial case through verify.py and print a PASS/FAIL table.
# Exit nonzero on any mismatch. Cases: "<target> <submission> <expected stage>".
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
VERIFY="$ROOT/harness/verify.py"
T_AIME="$ROOT/data/miniF2F-lean4/MiniF2F/Test/aime_1983_p2.lean"
T_PUTNAM="$ROOT/data/putnam_subst/putnam_1999_a1.lean"
T_COMBI="$ROOT/data/combi/combi_imo_2010_p5.lean"
OUT="$ROOT/runs/test_results"
mkdir -p "$OUT"

CASES=(
  "$T_AIME good.lean ok"
  "$T_AIME sorry.lean compile"
  "$T_AIME axiom.lean safeverify"
  "$T_AIME weaker.lean safeverify"
  "$T_AIME native.lean safeverify"
  "$T_AIME eval.lean source"
  "$T_PUTNAM putnam_good.lean ok"
  "$T_PUTNAM putnam_cheat.lean safeverify"
  "$T_PUTNAM putnam_nosol.lean safeverify"
  "$T_PUTNAM putnam_exact.lean ok"
  "$T_PUTNAM putnam_native.lean safeverify"
  # Hygienic universe-param names embed the module name; SafeVerify must compare modulo them.
  "$T_COMBI combi_good.lean ok"
  # Same proof, constructor OP.op24 renamed: inductive check must still reject.
  "$T_COMBI combi_ctor_renamed.lean safeverify"
)

# Compile each target once (sequentially) so parallel runs do not race on the cache.
for t in "$T_AIME" "$T_PUTNAM" "$T_COMBI"; do
  python3 -I -c "import sys; sys.path.insert(0, '$ROOT/harness'); import verify, pathlib; verify.target_olean(pathlib.Path('$t'))" || exit 2
done

pids=()
for c in "${CASES[@]}"; do
  set -- $c
  sub="$2"
  ( python3 -I "$VERIFY" "$1" "$ROOT/harness/tests/$sub" > "$OUT/${sub%.lean}.json" 2>&1 ) &
  pids+=($!)
done
wait

fail=0
printf '%-22s %-11s %-11s %s\n' SUBMISSION EXPECTED GOT RESULT
for c in "${CASES[@]}"; do
  set -- $c
  sub="$2"; exp="$3"
  got=$(python3 -I -c "import json,sys; print(json.load(open(sys.argv[1]))['stage'])" "$OUT/${sub%.lean}.json" 2>/dev/null || echo "error")
  if [ "$got" = "$exp" ]; then res=PASS; else res=FAIL; fail=1; fi
  printf '%-22s %-11s %-11s %s\n' "$sub" "$exp" "$got" "$res"
done
exit $fail
