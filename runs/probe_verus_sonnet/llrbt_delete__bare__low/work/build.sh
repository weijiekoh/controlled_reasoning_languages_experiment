#!/bin/bash
cd /work
awk '
function cat(f,  l){ while((getline l < f)>0) print l; close(f) }
/\/\/ <helpers>/ {print; cat("helpers.txt"); skip=1; next}
/\/\/ <proofs>/ {print; cat("proofs.txt"); skip=1; next}
/\/\/ <code>/ {print; cat("code.txt"); skip=1; next}
/\/\/ <\/(helpers|proofs|code)>/ {skip=0}
!skip {print}
' orig.rs > llrbt_delete.rs
