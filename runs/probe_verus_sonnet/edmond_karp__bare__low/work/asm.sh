#!/bin/bash
cd /work
awk '
/\/\/ <helpers>/ {print; while((getline l < "helpers.rs")>0) print l; skip=1; next}
/\/\/ <proofs>/ {print; while((getline l < "proofs.rs")>0) print l; skip=1; next}
/\/\/ <code>/ {print; while((getline l < "code.rs")>0) print l; skip=1; next}
/\/\/ <\/(helpers|proofs|code)>/ {skip=0}
!skip {print}
' template.rs > edmond_karp.rs
