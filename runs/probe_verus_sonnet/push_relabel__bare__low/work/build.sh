#!/bin/bash
cd /work
awk '
/\/\/ <helpers>/ {print; while((getline l < "helpers.txt")>0) print l; while((getline l < "helpers_exec.txt")>0) print l; skip=1; next}
/\/\/ <\/helpers>/ {skip=0}
/\/\/ <proofs>/ {print; while((getline l < "proofs.txt")>0) print l; skip=1; next}
/\/\/ <\/proofs>/ {skip=0}
/\/\/ <code>/ {print; while((getline l < "code.txt")>0) print l; skip=1; next}
/\/\/ <\/code>/ {skip=0}
!skip {print}
' orig.rs > push_relabel.rs
verus push_relabel.rs "$@" 2>&1 | grep -v "^warning" | grep -B2 -A14 -E "^error|verification results" | head -${LINES_MAX:-80}
